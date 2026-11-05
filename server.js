#!/usr/bin/env node
/*
 * Kart Racer 3D – LAN server
 * ---------------------------------------------------------------
 *   node server.js            (default port 8080)
 *   node server.js 3000       (custom port)
 *   PORT=3000 node server.js
 *
 * - Serves kart_racer.html to every device on your network
 * - Relays the game's lobby / room / presence messages over WebSocket
 * - No npm packages needed (Node 16+)
 */
'use strict';
const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const os = require('os');

const PORT = +process.env.PORT || +process.argv[2] || 8080;
const GAME = path.join(__dirname, 'kart_racer.html');
const VENDOR = path.join(__dirname, 'vendor');
const THREE_FILE = path.join(VENDOR, 'three.min.js');
const THREE_URL = 'https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js';

const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const MAX_MSG = 64 * 1024;      // max size of one client message
const GRACE_MS = 6000;          // keep a dropped player's slot this long so they can reconnect
const BAD_KEYS = new Set(['__proto__', 'constructor', 'prototype']);

/* ------------------------------------------------------------------ */
/*  HTTP: serve the game (and a locally cached three.js for offline)   */
/* ------------------------------------------------------------------ */
function sendFile(res, file, type, cache) {
  fs.readFile(file, (err, buf) => {
    if (err) { res.writeHead(404, { 'content-type': 'text/plain' }); return res.end('Not found'); }
    res.writeHead(200, { 'content-type': type, 'cache-control': cache, 'content-length': buf.length });
    res.end(buf);
  });
}

const server = http.createServer((req, res) => {
  const url = req.url.split('?')[0];
  if (url === '/' || url === '/kart_racer.html' || url === '/index.html')
    return sendFile(res, GAME, 'text/html; charset=utf-8', 'no-cache');
  if (url === '/vendor/three.min.js')
    return sendFile(res, THREE_FILE, 'application/javascript; charset=utf-8', 'public, max-age=86400');
  if (url === '/healthz') { res.writeHead(200, { 'content-type': 'text/plain' }); return res.end('ok'); }
  res.writeHead(404, { 'content-type': 'text/plain' });
  res.end('Not found');
});

/* ------------------------------------------------------------------ */
/*  Minimal RFC 6455 WebSocket implementation                          */
/* ------------------------------------------------------------------ */
function frame(op, payload) {
  const len = payload.length;
  let head;
  if (len < 126) head = Buffer.from([0x80 | op, len]);
  else if (len < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(len, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeBigUInt64BE(BigInt(len), 2); }
  return Buffer.concat([head, payload]);
}

function makeParser(onText, onClose, onPing, onPong) {
  let buf = Buffer.alloc(0), parts = [], partOp = 0, partLen = 0;
  return chunk => {
    buf = buf.length ? Buffer.concat([buf, chunk]) : chunk;
    for (;;) {
      if (buf.length < 2) return;
      const b0 = buf[0], b1 = buf[1];
      const fin = (b0 & 0x80) !== 0, op = b0 & 0x0f, masked = (b1 & 0x80) !== 0;
      let len = b1 & 0x7f, off = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) {
        if (buf.length < 10) return;
        const big = buf.readBigUInt64BE(2);
        if (big > BigInt(MAX_MSG)) throw new Error('frame too large');
        len = Number(big); off = 10;
      }
      if (len > MAX_MSG) throw new Error('frame too large');
      if (!masked) throw new Error('unmasked client frame');
      const total = off + 4 + len;
      if (buf.length < total) return;
      const mask = buf.subarray(off, off + 4), src = buf.subarray(off + 4, total);
      const payload = Buffer.allocUnsafe(len);
      for (let i = 0; i < len; i++) payload[i] = src[i] ^ mask[i & 3];
      buf = buf.subarray(total);

      if (op === 8) { onClose(); return; }
      if (op === 9) { onPing(payload); continue; }
      if (op === 10) { onPong(); continue; }
      if (op === 0 || op === 1 || op === 2) {
        if (op !== 0) { parts = []; partOp = op; partLen = 0; }
        parts.push(payload); partLen += len;
        if (partLen > MAX_MSG) throw new Error('message too large');
        if (fin) {
          const full = parts.length === 1 ? parts[0] : Buffer.concat(parts);
          parts = [];
          if (partOp === 1) onText(full.toString('utf8'));
        }
      }
    }
  };
}

/* ------------------------------------------------------------------ */
/*  Rooms + presence                                                   */
/*    rooms:   name -> Map(clientId -> presence object)                */
/*    clients: clientId -> { id, sock, rooms:Set, alive, grace }       */
/* ------------------------------------------------------------------ */
const clients = new Map();
const rooms = new Map();

const live = c => c && c.sock && !c.sock.destroyed;
const send = (c, obj) => { if (live(c)) c.sock.write(frame(1, Buffer.from(JSON.stringify(obj)))); };

function bcast(room, exceptId, obj) {
  const mem = rooms.get(room);
  if (!mem) return;
  const f = frame(1, Buffer.from(JSON.stringify(obj)));
  for (const id of mem.keys()) {
    if (id === exceptId) continue;
    const c = clients.get(id);
    // skip clients that can't keep up – presence is a stream, they catch up on the next update
    if (live(c) && c.sock.writableLength < 512 * 1024) c.sock.write(f);
  }
}

function merge(target, patch) {
  for (const k of Object.keys(patch)) {
    if (BAD_KEYS.has(k)) continue;
    if (patch[k] === null) delete target[k]; else target[k] = patch[k];
  }
}

function joinRoom(c, m) {
  const name = String(m.r || '');
  if (!name || name.length > 64) { send(c, { t: 'err', q: m.q, msg: 'bad room name' }); return; }
  let mem = rooms.get(name);
  if (!mem) { mem = new Map(); rooms.set(name, mem); }
  const isNew = !mem.has(c.id);
  if (isNew) mem.set(c.id, {});
  c.rooms.add(name);
  send(c, { t: 'snap', r: name, q: m.q, peers: [...mem].map(([id, presence]) => ({ peer: id, presence })) });
  if (isNew) bcast(name, c.id, { t: 'pres', r: name, p: c.id, d: {} });
}

function leaveRoom(c, name) {
  const mem = rooms.get(name);
  if (!mem || !mem.has(c.id)) return;
  mem.delete(c.id);
  c.rooms.delete(name);
  if (!mem.size) rooms.delete(name);
  else bcast(name, c.id, { t: 'left', r: name, p: c.id });
}

function drop(c) {
  clearTimeout(c.grace);
  for (const r of [...c.rooms]) leaveRoom(c, r);
  if (clients.get(c.id) === c) clients.delete(c.id);
}

function handle(c, text) {
  let m;
  try { m = JSON.parse(text); } catch (e) { return; }
  if (!m || typeof m !== 'object') return;
  switch (m.t) {
    case 'ping':                       // clock sync: client uses this to align Date.now() with the server
      send(c, { t: 'pong', c: m.c, s: Date.now() });
      break;
    case 'join':
      joinRoom(c, m);
      break;
    case 'leave':
      leaveRoom(c, String(m.r));
      break;
    case 'pres': {
      const r = String(m.r), mem = rooms.get(r);
      if (!mem || !mem.has(c.id) || !m.d || typeof m.d !== 'object' || Array.isArray(m.d)) return;
      if (m.full) { const fresh = {}; merge(fresh, m.d); mem.set(c.id, fresh); }
      else merge(mem.get(c.id), m.d);
      bcast(r, c.id, { t: 'pres', r, p: c.id, d: m.d, full: m.full ? 1 : 0 });
      break;
    }
  }
}

function attach(sock, id) {
  let c = clients.get(id);
  if (c) {                                   // reconnect (or takeover of a half-dead socket)
    clearTimeout(c.grace);
    if (c.sock && c.sock !== sock) c.sock.destroy();
  } else {
    c = { id, sock: null, rooms: new Set(), alive: true, grace: null };
    clients.set(id, c);
  }
  c.sock = sock; c.alive = true;
  let graceful = false;

  const feed = makeParser(
    text => handle(c, text),
    () => { graceful = true; try { sock.write(frame(8, Buffer.alloc(0))); } catch (e) {} sock.end(); },
    payload => { if (live(c)) sock.write(frame(10, payload)); },
    () => {}
  );
  sock.on('data', d => { c.alive = true; try { feed(d); } catch (e) { sock.destroy(); } });
  sock.on('error', () => {});
  sock.on('end', () => sock.end());          // http sockets are half-open by default: finish the close so 'close' fires
  sock.on('close', () => {
    if (c.sock !== sock) return;             // replaced by a newer connection
    c.sock = null;
    if (graceful) drop(c);                   // tab closed / left on purpose
    else c.grace = setTimeout(() => drop(c), GRACE_MS);   // network hiccup: allow reconnect
  });
}

server.on('upgrade', (req, sock) => {
  const u = new URL(req.url, 'http://localhost');
  const key = req.headers['sec-websocket-key'];
  if (u.pathname !== '/ws' || !key || String(req.headers.upgrade).toLowerCase() !== 'websocket') { sock.destroy(); return; }
  const id = (u.searchParams.get('id') || '').replace(/[^0-9a-z]/gi, '').slice(0, 24) || crypto.randomBytes(8).toString('hex');
  const accept = crypto.createHash('sha1').update(key + WS_GUID).digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  sock.setNoDelay(true);                     // low latency: don't batch small packets
  sock.setKeepAlive(true, 15000);
  attach(sock, id);
});

// Heartbeat: drop connections that stopped answering
setInterval(() => {
  for (const c of clients.values()) {
    if (!c.sock) continue;
    if (!c.alive) { c.sock.destroy(); continue; }
    c.alive = false;
    try { c.sock.write(frame(9, Buffer.alloc(0))); } catch (e) {}
  }
}, 10000);

/* ------------------------------------------------------------------ */
/*  Startup                                                            */
/* ------------------------------------------------------------------ */
// Cache three.js locally once, so the game also runs on a LAN without internet.
function ensureThree() {
  return new Promise(resolve => {
    try { if (fs.statSync(THREE_FILE).size > 100000) return resolve(true); } catch (e) {}
    console.log('Downloading three.js once so the game works without internet …');
    const req = https.get(THREE_URL, { timeout: 8000 }, r => {
      if (r.statusCode !== 200) { r.resume(); return resolve(false); }
      const chunks = [];
      r.on('data', d => chunks.push(d));
      r.on('end', () => {
        const b = Buffer.concat(chunks);
        if (b.length < 100000) return resolve(false);
        try { fs.mkdirSync(VENDOR, { recursive: true }); fs.writeFileSync(THREE_FILE, b); resolve(true); }
        catch (e) { resolve(false); }
      });
    });
    req.on('timeout', () => req.destroy());
    req.on('error', () => resolve(false));
  });
}

function lanAddresses() {
  const out = [];
  for (const [name, list] of Object.entries(os.networkInterfaces()))
    for (const i of list || [])
      if ((i.family === 'IPv4' || i.family === 4) && !i.internal) out.push({ name, address: i.address });
  const priv = a => /^(192\.168\.|10\.|172\.(1[6-9]|2\d|3[01])\.)/.test(a);
  return out.sort((a, b) => priv(b.address) - priv(a.address));
}

if (!fs.existsSync(GAME)) {
  console.error('kart_racer.html not found next to server.js (' + GAME + ')');
  process.exit(1);
}

server.on('error', e => {
  if (e.code === 'EADDRINUSE') console.error('Port ' + PORT + ' is already in use. Try: node server.js ' + (PORT + 1));
  else console.error(e);
  process.exit(1);
});

ensureThree().then(ok => {
  server.listen(PORT, '0.0.0.0', () => {
    console.log('\n  Kart Racer 3D – LAN server running\n');
    console.log('  On this device:   http://localhost:' + PORT);
    const addrs = lanAddresses();
    if (addrs.length) {
      console.log('  Other devices on the same Wi-Fi / LAN open:');
      for (const a of addrs) console.log('    http://' + a.address + ':' + PORT + '    (' + a.name + ')');
    } else {
      console.log('  No network interface found – connect to Wi-Fi / LAN first.');
    }
    if (!ok) console.log('\n  Note: could not cache three.js (no internet). Clients need internet access for it, or put three.min.js (r128) into ./vendor/');
    console.log('\n  If others cannot connect: allow "node" through your firewall for private networks.');
    console.log('  Press Ctrl+C to stop.\n');
  });
});
