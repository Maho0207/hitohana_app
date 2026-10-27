/* 一花交通 バス案内 — app.js
 * 一般向け: 停留所時刻表 / 便の停車停留所 / 乗換案内 / 走行位置（遅延シミュレーション）/ 車番表示
 * 事業者向け: 車両 / 乗務員（担当車）/ 運用表 / 臨時便 / 設定
 */
'use strict';

/* ================= utilities ================= */
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
const esc = (v) => String(v ?? '').replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const pad2 = (n) => String(n).padStart(2, '0');
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const CFG = Object.assign({ companyName: '一花交通', adminPasswordHash: '', storagePrefix: 'ichika.' }, window.APP_CONFIG || {});

function fmt(min) {
  if (min == null || !isFinite(min)) return '—';
  const m = Math.floor(min + 1e-6);
  return `${Math.floor(m / 60) % 24}:${pad2(((m % 60) + 60) % 60)}`;
}
function parseHM(s) {
  const m = /^(\d{1,2}):(\d{2})$/.exec(String(s).trim());
  return m ? +m[1] * 60 + +m[2] : null;
}
function hmInput(min) { const m = Math.floor(min) % 1440; return `${pad2(Math.floor(m / 60))}:${pad2(m % 60)}`; }
function dateStr(d) { return `${d.getFullYear()}-${pad2(d.getMonth() + 1)}-${pad2(d.getDate())}`; }
function addDays(ds, n) { const [y, m, d] = ds.split('-').map(Number); return dateStr(new Date(y, m - 1, d + n)); }
function dayIndex(ds) { const [y, m, d] = ds.split('-').map(Number); return Math.floor(Date.UTC(y, m - 1, d) / 864e5); }
function dateJa(ds) {
  const [y, m, d] = ds.split('-').map(Number);
  const w = '日月火水木金土'[new Date(y, m - 1, d).getDay()];
  return `${m}月${d}日(${w})`;
}
function ageOn(birth, ds) {
  const [by, bm, bd] = birth.split('-').map(Number);
  const [y, m, d] = ds.split('-').map(Number);
  return y - by - (m < bm || (m === bm && d < bd) ? 1 : 0);
}
function hashStr(s) { let h = 2166136261; for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); } return h >>> 0; }
function rngFrom(seed) {
  let a = seed >>> 0;
  return function () { a |= 0; a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}
function uid(p) { return p + Date.now().toString(36) + Math.random().toString(36).slice(2, 6); }
function sha256(str) {
  const rr = (v, a) => (v >>> a) | (v << (32 - a));
  const H = [], K = []; let c = 0;
  for (let cand = 2; c < 64; cand++) {
    let p = true; for (let i = 2; i * i <= cand; i++) if (cand % i === 0) { p = false; break; }
    if (p) { if (c < 8) H[c] = (Math.pow(cand, 1 / 2) * 4294967296) | 0; K[c] = (Math.pow(cand, 1 / 3) * 4294967296) | 0; c++; }
  }
  const bytes = new TextEncoder().encode(str), l = bytes.length;
  const buf = new Uint8Array(((l + 9 + 63) >> 6) << 6); buf.set(bytes); buf[l] = 0x80;
  const dv = new DataView(buf.buffer); dv.setUint32(buf.length - 4, (l * 8) >>> 0); dv.setUint32(buf.length - 8, Math.floor(l / 536870912));
  let h = H.slice();
  for (let i = 0; i < buf.length; i += 64) {
    const w = new Array(64);
    for (let j = 0; j < 16; j++) w[j] = dv.getUint32(i + j * 4);
    for (let j = 16; j < 64; j++) {
      const s0 = rr(w[j - 15], 7) ^ rr(w[j - 15], 18) ^ (w[j - 15] >>> 3);
      const s1 = rr(w[j - 2], 17) ^ rr(w[j - 2], 19) ^ (w[j - 2] >>> 10);
      w[j] = (w[j - 16] + s0 + w[j - 7] + s1) | 0;
    }
    let [a, b, cc, d, e, f, g, hh] = h;
    for (let j = 0; j < 64; j++) {
      const t1 = (hh + (rr(e, 6) ^ rr(e, 11) ^ rr(e, 25)) + ((e & f) ^ (~e & g)) + K[j] + w[j]) | 0;
      const t2 = ((rr(a, 2) ^ rr(a, 13) ^ rr(a, 22)) + ((a & b) ^ (a & cc) ^ (b & cc))) | 0;
      hh = g; g = f; f = e; e = (d + t1) | 0; d = cc; cc = b; b = a; a = (t1 + t2) | 0;
    }
    h = [a, b, cc, d, e, f, g, hh].map((v, k) => (v + h[k]) | 0);
  }
  return h.map((v) => (v >>> 0).toString(16).padStart(8, '0')).join('');
}
const pwHash = (pw) => sha256('ichika-bus:' + pw);

const LS = {
  get(k, d) { try { const v = localStorage.getItem(CFG.storagePrefix + k); return v == null ? d : JSON.parse(v); } catch { return d; } },
  set(k, v) { try { localStorage.setItem(CFG.storagePrefix + k, JSON.stringify(v)); return true; } catch { toast('ブラウザに保存できませんでした（容量不足の可能性があります）'); return false; } },
  del(k) { try { localStorage.removeItem(CFG.storagePrefix + k); } catch { /* noop */ } },
};
let toastTimer;
function toast(msg) {
  let el = $('.toast'); if (!el) { el = document.createElement('div'); el.className = 'toast'; el.setAttribute('role', 'status'); document.body.append(el); }
  el.textContent = msg; el.hidden = false; clearTimeout(toastTimer); toastTimer = setTimeout(() => { el.hidden = true; }, 2600);
}

/* ================= guide data & indexes ================= */
const G = {};
function buildIndex(D) {
  G.D = D;
  G.stop = Object.fromEntries(D.stops.map((s) => [s.id, s]));
  G.route = Object.fromEntries(D.routes.map((r) => [r.id, r]));
  G.sys = {};
  G.fare = Object.fromEntries((D.fares?.routes || []).map((f) => [f.routeId + '|' + f.lineId, f]));
  G.depots = (D.operations?.depots || []).length ? D.operations.depots : [{ id: 'dep0', name: '本社営業所', stopId: D.stops[0]?.id, routes: D.routes.map((r) => r.id) }];
  G.stopSys = {};
  for (const s of D.systems) {
    const route = G.route[s.routeId];
    const line = route?.lines.find((l) => l.id === s.lineId) || route?.lines[0];
    const ls = line ? (s.direction === 'up' ? line.stops.slice().reverse() : line.stops) : [];
    let p = 0; const map = [];
    for (const st of s.stops) {
      let k = p; while (k < ls.length && ls[k] !== st.stopId) k++;
      if (k < ls.length) { map.push(s.direction === 'up' ? ls.length - 1 - k : k); p = k + 1; } else map.push(null);
    }
    const sys = { ...s, route, color: route?.color || '#0B5D4B', lineMap: map, fareTable: G.fare[s.routeId + '|' + s.lineId] || null, n: s.stops.length };
    sys.circular = s.origin === s.destination;
    G.sys[s.id] = sys;
    s.stops.forEach((st, i) => { if (i < s.stops.length - 1) (G.stopSys[st.stopId] ||= []).push({ sys, idx: i }); });
  }
  const useDay = D.trips.some((t) => t.day === 'wd') ? 'wd' : (D.trips[0]?.day || 'wd');
  G.baseTrips = D.trips.filter((t) => t.day === useDay && G.sys[t.systemId]).map((t) => normTrip({ id: t.id, sys: G.sys[t.systemId], times: t.times, temp: false }));
  G.stopsActive = D.stops.filter((s) => G.stopSys[s.id]);
  G.rank = Object.fromEntries(D.stops.map((s) => [s.id, (s.routes || []).length]));
  G.bounds = (() => {
    const xs = D.stops.map((s) => s.x), ys = D.stops.map((s) => s.y);
    return { x0: Math.min(...xs), x1: Math.max(...xs), y0: Math.min(...ys), y1: Math.max(...ys) };
  })();
}
function normTrip(t) {
  let s = 0, e = t.times.length - 1;
  while (s < e && !t.times[s]) s++;
  while (e > s && !t.times[e]) e--;
  t.s = s; t.e = e; t.dep = t.times[s][1]; t.end = t.times[e][0];
  return t;
}
const stopName = (id) => G.stop[id]?.name || '（不明）';
function sysLabel(sys) {
  if (sys.circular) return sys.via ? `${sys.via}（循環）` : '循環';
  return `${stopName(sys.destination)}行`;
}
function tripDestName(trip) {
  if (trip.e === trip.sys.n - 1) return sysLabel(trip.sys);
  return `${stopName(trip.sys.stops[trip.e].stopId)}行`;
}
function routeBadge(sys) { return `<span class="badge" style="background:${esc(sys.color)}">${esc(sys.no)}</span>`; }

/* fares */
function fareBetween(sys, i, j) {
  const ft = sys.fareTable; if (!ft) return null;
  const a = sys.lineMap[i], b = sys.lineMap[j]; if (a == null || b == null) return null;
  const v = ft.adult?.[a]?.[b]; return v == null ? null : v;
}
const childFare = (a) => a == null ? null : Math.ceil(a / 2 / 10) * 10;
const yen = (v) => v == null ? '—' : `${v.toLocaleString('ja-JP')}円`;

/* ================= app state (company side) ================= */
const DEFAULT_SETTINGS = {
  bands: [
    { name: '早朝', from: 0, to: 420, p: 1.0, max: 1 },
    { name: '朝ラッシュ', from: 420, to: 570, p: 6.0, max: 2 },
    { name: '日中', from: 570, to: 960, p: 2.5, max: 1 },
    { name: '夕ラッシュ', from: 960, to: 1140, p: 5.5, max: 2 },
    { name: '夜間', from: 1140, to: 2000, p: 1.5, max: 1 },
  ],
  recover: 12,   // 遅れているときに区間を1分詰められる確率(%)
  trouble: 0.2,  // 停留所ごとの客とのトラブル発生率(%) 接客態度3のとき
  accident: 0.006, // 区間ごとの事故発生率(%) 運転技術3のとき
  turnaround: 1, // 折返し最小時間(分)
};
const state = {
  ver: 1,
  settings: Object.assign({}, DEFAULT_SETTINGS, LS.get('settings', {})),
  temps: LS.get('temps', []),
  fleet: null,
};
const caches = { trips: new Map(), blocks: new Map(), sim: new Map(), conns: new Map() };
function bump() { state.ver++; caches.trips.clear(); caches.blocks.clear(); caches.sim.clear(); caches.conns.clear(); }
function saveFleet() { LS.set('fleet', state.fleet); bump(); }
function saveTemps() { LS.set('temps', state.temps); bump(); }
function saveSettings() { LS.set('settings', state.settings); bump(); }

/* ================= trips for a date (base + 臨時便) ================= */
function makeTempTrip(t) {
  const sys = G.sys[t.sys]; if (!sys) return null;
  const from = clamp(t.from, 0, sys.n - 2), to = clamp(t.to, from + 1, sys.n - 1);
  const off = t.dep - sys.stops[from].dep;
  const times = sys.stops.map((st, i) => {
    if (i < from || i > to || (st.pass && i !== from && i !== to)) return null;
    const a = i === from ? t.dep : st.arr + off; const d = i === to ? st.arr + off : (i === from ? t.dep : st.dep + off);
    return [a, d];
  });
  return normTrip({ id: 'tmp_' + t.id, sys, times, temp: true, note: t.note || '', tempId: t.id });
}
function tripsFor(date) {
  if (caches.trips.has(date)) return caches.trips.get(date);
  const list = G.baseTrips.concat(state.temps.filter((t) => t.date === date).map(makeTempTrip).filter(Boolean));
  list.sort((a, b) => a.dep - b.dep);
  const byId = new Map(list.map((t) => [t.id, t]));
  const r = { list, byId }; caches.trips.set(date, r); return r;
}

/* ================= 運用（車両の行路）を自動作成 ================= */
function blocksFor(date) {
  if (caches.blocks.has(date)) return caches.blocks.get(date);
  const { list } = tripsFor(date);
  const turn = state.settings.turnaround ?? 1;
  const blocks = []; const pool = []; // {block, stop, freeAt}
  for (const trip of list) {
    const o = trip.sys.stops[trip.s].stopId, rid = trip.sys.routeId;
    const cands = G.depots.filter((d) => (d.routes || []).includes(rid));
    const okDep = (dep) => !cands.length || cands.some((c) => c.id === dep);
    let best = -1;
    for (let i = 0; i < pool.length; i++) {
      const p = pool[i];
      if (p.stop === o && p.freeAt + turn <= trip.dep && okDep(p.block.depot) && (best < 0 || p.freeAt < pool[best].freeAt)) best = i;
    }
    let blk;
    if (best >= 0) { blk = pool[best].block; pool.splice(best, 1); }
    else {
      const dep = (cands.find((c) => c.stopId === o) || cands[0] || G.depots[0]).id;
      blk = { depot: dep, trips: [] }; blocks.push(blk);
    }
    blk.trips.push(trip);
    pool.push({ block: blk, stop: trip.sys.stops[trip.e].stopId, freeAt: trip.end });
  }
  const counter = {};
  for (const b of blocks) { counter[b.depot] = (counter[b.depot] || 0) + 1; b.no = counter[b.depot]; b.id = b.depot + '-' + b.no; }
  const r = { blocks, perDepot: counter }; caches.blocks.set(date, r); return r;
}
function depotName(id) { return G.depots.find((d) => d.id === id)?.name || '（未設定）'; }
function depotShort(id) { const n = depotName(id); const m = /営業所(.+)$/.exec(n); return m ? m[1] : n; }

/* ================= 運行シミュレーション（遅延・トラブル・事故） ================= */
const F_DELAY = [1.6, 1.25, 1.0, 0.75, 0.5];   // 運転技術1..5 → 遅延発生率の倍率
const F_RECOVER = [0.5, 0.8, 1.0, 1.3, 1.7];   // 運転技術 → 回復のしやすさ
const F_ACC = [6, 2.5, 1.0, 0.4, 0.15];        // 運転技術 → 事故率の倍率
const F_TROUBLE = [3, 1.8, 1.0, 0.5, 0.25];    // 接客態度 → トラブル率の倍率
function bandAt(min) { let m = ((min % 1440) + 1440) % 1440; if (m < 180) m += 1440; return state.settings.bands.find((b) => m >= b.from && m < b.to) || state.settings.bands[state.settings.bands.length - 1]; }

function vehiclesOfDepot(depId) {
  return state.fleet.vehicles.filter((v) => v.depot === depId && v.status !== '休車').sort((a, b) => a.no.localeCompare(b.no, 'ja', { numeric: true }));
}
function driversOfVehicle(vid) {
  return state.fleet.drivers.filter((d) => d.vehicleId === vid && d.status !== '休職').sort((a, b) => String(a.empNo).localeCompare(String(b.empNo), 'ja', { numeric: true }));
}
function simulateTrip(trip, start, driver, rng) {
  const S = state.settings, T = trip.times;
  const skill = clamp(driver?.skill ?? 3, 1, 5) - 1, svc = clamp(driver?.service ?? 3, 1, 5) - 1;
  const arr = new Array(T.length).fill(null), dep = new Array(T.length).fill(null), events = [];
  let prev = trip.s; dep[prev] = Math.max(T[prev][1], start); arr[prev] = dep[prev];
  if (dep[prev] - T[prev][1] >= 1) events.push({ type: 'late', at: prev, min: dep[prev] - T[prev][1], text: '前便の遅れを引き継いで発車' });
  let accident = null;
  for (let j = trip.s + 1; j <= trip.e; j++) {
    if (!T[j]) continue;
    const sRun = Math.max(0, T[j][0] - T[prev][1]);
    const band = bandAt(T[prev][1]);
    let extra = 0;
    const r1 = rng(), r2 = rng(), r3 = rng(), r4 = rng(), r5 = rng();
    if (r1 < (band.p / 100) * F_DELAY[skill]) {
      extra = 1 + Math.floor(r2 * band.max);
      events.push({ type: 'jam', at: j, min: extra, text: `${stopName(trip.sys.stops[prev].stopId)}→${stopName(trip.sys.stops[j].stopId)} 間で混雑` });
    } else if (dep[prev] - T[prev][1] >= 1 && sRun >= 2 && r2 < (S.recover / 100) * F_RECOVER[skill]) extra = -1;
    if (r3 < (S.accident / 100) * F_ACC[skill]) {
      const f = 0.2 + r4 * 0.6;
      accident = { from: prev, to: j, f, t: dep[prev] + Math.max(0.4, sRun + extra) * f };
      events.push({ type: 'accident', at: j, text: `${stopName(trip.sys.stops[prev].stopId)}→${stopName(trip.sys.stops[j].stopId)} 間で事故、運転打ち切り` });
      break;
    }
    arr[j] = dep[prev] + Math.max(0.4, sRun + extra);
    let d = Math.max(T[j][1], arr[j]);
    if (j < trip.e && r5 < (S.trouble / 100) * F_TROUBLE[svc]) {
      const m = 2 + Math.floor(rng() * 4); d += m;
      events.push({ type: 'trouble', at: j, min: m, text: `${stopName(trip.sys.stops[j].stopId)}で乗客対応（${m}分）` });
    }
    dep[j] = j === trip.e ? arr[j] : d;
    prev = j;
  }
  return { arr, dep, events, accident, endT: accident ? accident.t : arr[trip.e] };
}
function simDay(date) {
  if (caches.sim.has(date)) return caches.sim.get(date);
  const { blocks } = blocksFor(date);
  const di = dayIndex(date);
  const byTrip = new Map(); const byBlock = [];
  const turn = state.settings.turnaround ?? 1;
  for (const dep of G.depots) {
    const vehs = vehiclesOfDepot(dep.id);
    const bl = blocks.filter((b) => b.depot === dep.id);
    bl.forEach((b, k) => {
      const vehicle = vehs.length && k < vehs.length ? vehs[(k + di) % vehs.length] : null;
      const ds = vehicle ? driversOfVehicle(vehicle.id) : [];
      const driver = ds.length ? ds[di % ds.length] : null;
      let prevEnd = -Infinity, broke = false; const sims = [];
      for (const trip of b.trips) {
        const rng = rngFrom(hashStr(date + '|' + trip.id));
        const sub = broke;
        const sim = simulateTrip(trip, sub ? trip.dep : Math.max(trip.dep, prevEnd + turn), sub ? null : driver, rng);
        Object.assign(sim, { trip, block: b, vehicle: sub ? null : vehicle, driver: sub ? null : driver, substitute: sub });
        if (sim.accident) broke = true;
        prevEnd = sim.endT; byTrip.set(trip.id, sim); sims.push(sim);
      }
      byBlock.push({ block: b, vehicle, driver, sims });
    });
  }
  const r = { byTrip, byBlock }; caches.sim.set(date, r); return r;
}
/* position of a simulated trip at minute t */
function posAt(sim, t) {
  const { trip, arr, dep, accident } = sim; const st = trip.sys.stops;
  const xy = (i) => G.stop[st[i].stopId];
  if (t < dep[trip.s]) return null;
  if (accident) {
    if (t >= accident.t) {
      if (t > accident.t + 40) return null;
      const a = xy(accident.from), b = xy(accident.to);
      return { state: 'accident', x: a.x + (b.x - a.x) * accident.f, y: a.y + (b.y - a.y) * accident.f, prev: accident.from, next: accident.to, delay: null };
    }
  } else if (t > arr[trip.e]) return null;
  let prev = trip.s;
  for (let j = trip.s + 1; j <= trip.e; j++) {
    if (arr[j] == null) { if (!trip.times[j]) continue; break; }
    if (t < arr[j]) {
      const f = clamp((t - dep[prev]) / Math.max(0.01, arr[j] - dep[prev]), 0, 1);
      const a = xy(prev), b = xy(j);
      return { state: 'run', x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f, prev, next: j, delay: Math.max(0, Math.round(dep[prev] - trip.times[prev][1])) };
    }
    if (t <= dep[j]) {
      const a = xy(j);
      return { state: 'stop', x: a.x, y: a.y, prev: j, next: j, delay: Math.max(0, Math.round(arr[j] - trip.times[j][0])) };
    }
    prev = j;
  }
  const a = xy(prev); return { state: 'stop', x: a.x, y: a.y, prev, next: prev, delay: 0 };
}

/* ================= 現在時刻（実時間 / 指定時刻・倍速） ================= */
const clock = { mode: 'real', base: 0, setAt: 0, speed: 1 };
function nowDate() { return clock.mode === 'real' ? new Date() : new Date(clock.base + (Date.now() - clock.setAt) * clock.speed); }
function serviceNow(real = false) {
  const d = real ? new Date() : nowDate(); let ds = dateStr(d); let t = d.getHours() * 60 + d.getMinutes() + d.getSeconds() / 60;
  if (d.getHours() < 3) { ds = addDays(ds, -1); t += 1440; }
  return { date: ds, t, d };
}
function activeSims(date, t) {
  const out = [];
  for (const s of simDay(date).byTrip.values()) { const p = posAt(s, t); if (p) out.push({ sim: s, pos: p }); }
  return out;
}

/* ================= 乗換検索（Connection Scan） ================= */
function connsFor(date) {
  if (caches.conns.has(date)) return caches.conns.get(date);
  const out = [];
  for (const trip of tripsFor(date).list) {
    let prev = trip.s;
    for (let j = trip.s + 1; j <= trip.e; j++) {
      if (!trip.times[j]) continue;
      out.push({ trip, i: prev, j, from: trip.sys.stops[prev].stopId, to: trip.sys.stops[j].stopId, dep: trip.times[prev][1], arr: trip.times[j][0] });
      prev = j;
    }
  }
  out.sort((a, b) => a.dep - b.dep || a.arr - b.arr);
  caches.conns.set(date, out); return out;
}
function csa(date, A, B, t0, xfer) {
  const C = connsFor(date);
  const lab = new Map(); const get = (s) => lab.get(s) || { arr: Infinity, tr: Infinity };
  const ride = new Map();
  let lo = 0, hi = C.length; while (lo < hi) { const m = (lo + hi) >> 1; if (C[m].dep < t0) lo = m + 1; else hi = m; }
  for (let k = lo; k < C.length; k++) {
    const c = C[k];
    const best = get(B);
    if (best.arr <= c.dep) break;
    let rb = ride.get(c.trip.id);
    let canBoard = false, tr = 0;
    if (c.from === A) { canBoard = true; tr = 0; }
    else { const L = get(c.from); if (L.arr + xfer <= c.dep) { canBoard = true; tr = L.tr + 1; } }
    if (canBoard && (!rb || tr < rb.tr)) { rb = { enter: c, tr }; ride.set(c.trip.id, rb); }
    if (rb && c.to !== A) {
      const L = get(c.to);
      if (c.arr < L.arr || (c.arr === L.arr && rb.tr < L.tr)) lab.set(c.to, { arr: c.arr, tr: rb.tr, enter: rb.enter, exit: c });
    }
  }
  const end = lab.get(B); if (!end) return null;
  const legs = []; let cur = end, guard = 0;
  while (cur && guard++ < 20) {
    legs.unshift({ trip: cur.enter.trip, i: cur.enter.i, j: cur.exit.j });
    if (cur.enter.from === A) break;
    cur = lab.get(cur.enter.from);
  }
  return legs;
}
function searchJourneys(date, A, B, t0, xfer) {
  const found = []; let t = t0;
  for (let n = 0; n < 14 && found.length < 8; n++) {
    const legs = csa(date, A, B, t, xfer); if (!legs) break;
    const dep = legs[0].trip.times[legs[0].i][1], arr = legs[legs.length - 1].trip.times[legs[legs.length - 1].j][0];
    found.push({ legs, dep, arr, tr: legs.length - 1 });
    t = dep + 1;
  }
  const res = found.filter((a) => !found.some((b) => b !== a && b.dep >= a.dep && b.arr <= a.arr && b.tr <= a.tr && (b.dep > a.dep || b.arr < a.arr || b.tr < a.tr)));
  const seen = new Set();
  return res.filter((j) => { const k = j.legs.map((l) => l.trip.id + l.i + '-' + l.j).join(); if (seen.has(k)) return false; seen.add(k); return true; }).slice(0, 5);
}

/* ================= 車両・乗務員データの生成 ================= */
const MODELS = [
  { maker: 'いすゞ', model: 'エルガ', type: '大型', cap: [76, 80], from: 2000, w: 5 },
  { maker: '日野', model: 'ブルーリボン', type: '大型', cap: [76, 79], from: 2000, w: 5 },
  { maker: '三菱ふそう', model: 'エアロスター', type: '大型', cap: [77, 82], from: 2000, w: 4 },
  { maker: 'いすゞ', model: 'エルガミオ', type: '中型', cap: [58, 62], from: 2000, w: 2 },
  { maker: '日野', model: 'レインボー', type: '中型', cap: [57, 61], from: 2000, w: 2 },
  { maker: '日野', model: 'ポンチョ', type: '小型', cap: [33, 36], from: 2006, w: 1 },
  { maker: 'BYD', model: 'K8（EV）', type: '大型', cap: [79, 81], from: 2020, w: 1 },
  { maker: 'いすゞ', model: 'エルガEV', type: '大型', cap: [76, 78], from: 2024, w: 1 },
];
const pick = (rng, arr) => arr[Math.floor(rng() * arr.length)];
function gauss(rng) { let u = 0; while (u === 0) u = rng(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * rng()); }
const depotCode = (id) => 'ABCDEFGHJK'[Math.max(0, G.depots.findIndex((d) => d.id === id))] || 'Z';

function genVehicles(n, opt, rng = Math.random) {
  const out = []; const fleet = state.fleet;
  const usedNo = new Set(fleet.vehicles.map((v) => v.no)), usedPlate = new Set(fleet.vehicles.map((v) => v.plate));
  for (let k = 0; k < n; k++) {
    const depot = opt.depot === 'auto' ? G.depots[k % G.depots.length].id : opt.depot;
    const year = opt.yearFrom + Math.floor(rng() * (opt.yearTo - opt.yearFrom + 1));
    const ms = MODELS.filter((m) => m.from <= year); const tw = ms.reduce((a, m) => a + m.w, 0);
    let r = rng() * tw, m = ms[0]; for (const x of ms) { r -= x.w; if (r <= 0) { m = x; break; } }
    const prefix = depotCode(depot) + String(year).slice(2);
    let seq = 1, no; do { no = prefix + pad2(seq++); } while (usedNo.has(no)); usedNo.add(no);
    let plate; do { plate = `${CFG.companyName.slice(0, 2)}200か${pad2(10 + Math.floor(rng() * 89))}-${pad2(Math.floor(rng() * 100))}`; } while (usedPlate.has(plate)); usedPlate.add(plate);
    out.push({
      id: uid('v'), no, plate, maker: m.maker, model: m.model, type: m.type, year,
      depot, capacity: m.cap[0] + Math.floor(rng() * (m.cap[1] - m.cap[0] + 1)),
      floor: year >= 2015 || rng() < 0.6 ? 'ノンステップ' : 'ワンステップ', status: '稼働', note: '',
    });
  }
  return out;
}
const AGE_W = [[19, 29, 0.12], [30, 39, 0.17], [40, 49, 0.24], [50, 59, 0.26], [60, 69, 0.15], [70, 79, 0.05], [80, 90, 0.01]];
function genDrivers(n, opt, rng = Math.random, refDate = dateStr(new Date())) {
  const P = window.NAME_POOL; const out = []; const fleet = state.fleet;
  const usedNames = new Set(fleet.drivers.map((d) => d.sur + d.given));
  let emp = fleet.drivers.reduce((m, d) => Math.max(m, +d.empNo || 0), 100000);
  const ages = []; let tot = 0;
  for (let a = opt.ageMin; a <= opt.ageMax; a++) { const w = (AGE_W.find(([x, y]) => a >= x && a <= y) || [0, 0, 0.01])[2]; ages.push([a, w]); tot += w; }
  const [ry, rm, rd] = refDate.split('-').map(Number);
  for (let k = 0; k < n; k++) {
    let r = rng() * tot, age = ages[0][0]; for (const [a, w] of ages) { r -= w; if (r <= 0) { age = a; break; } }
    const male = rng() * 100 < opt.maleRatio;
    let sur, given, tries = 0;
    do { sur = pick(rng, P.surnames); given = pick(rng, male ? P.male : P.female); } while (usedNames.has(sur + given) && ++tries < 20);
    usedNames.add(sur + given);
    const hi = new Date(ry - age, rm - 1, rd), lo = new Date(ry - age - 1, rm - 1, rd + 1);
    const birth = dateStr(new Date(lo.getTime() + rng() * (hi.getTime() - lo.getTime())));
    const [by, bm, bd] = birth.split('-').map(Number);
    const earliest = new Date(by + 19, bm - 1, bd), ref = new Date(ry, rm - 1, rd);
    const hired = dateStr(new Date(earliest.getTime() + Math.pow(rng(), 0.8) * Math.max(0, ref.getTime() - earliest.getTime())));
    const yrs = (ref - new Date(hired)) / 3.156e10;
    const depot = opt.depot === 'auto' ? G.depots[k % G.depots.length].id : opt.depot;
    out.push({
      id: uid('d'), empNo: String(++emp), sur, given, gender: male ? '男' : '女', birth, hired, depot,
      skill: clamp(Math.round(2.4 + Math.min(yrs, 25) / 12 + gauss(rng) * 0.9), 1, 5),
      service: clamp(Math.round(3.1 + gauss(rng)), 1, 5),
      vehicleId: null, status: '在籍', note: '',
    });
  }
  return out;
}
function autoAssign(onlyDepot) {
  let n = 0;
  for (const dep of G.depots) {
    if (onlyDepot && dep.id !== onlyDepot) continue;
    const vehs = state.fleet.vehicles.filter((v) => v.depot === dep.id && v.status !== '休車');
    if (!vehs.length) continue;
    const ids = new Set(state.fleet.vehicles.map((v) => v.id));
    const cnt = new Map(vehs.map((v) => [v.id, state.fleet.drivers.filter((d) => d.vehicleId === v.id).length]));
    for (const d of state.fleet.drivers) {
      if (d.depot !== dep.id || d.status === '休職' || (d.vehicleId && ids.has(d.vehicleId))) continue;
      let best = vehs[0]; for (const v of vehs) if (cnt.get(v.id) < cnt.get(best.id)) best = v;
      d.vehicleId = best.id; cnt.set(best.id, cnt.get(best.id) + 1); n++;
    }
  }
  return n;
}
function defaultFleet() {
  state.fleet = { vehicles: [], drivers: [] };
  const rng = rngFrom(hashStr('ichika-default-fleet-v1'));
  const { perDepot } = blocksFor('2000-01-01');
  for (const dep of G.depots) {
    const need = Math.ceil((perDepot[dep.id] || 4) * 1.12) + 1;
    state.fleet.vehicles.push(...genVehicles(need, { depot: dep.id, yearFrom: 2008, yearTo: 2026 }, rng));
  }
  for (const dep of G.depots) {
    const nv = state.fleet.vehicles.filter((v) => v.depot === dep.id).length;
    state.fleet.drivers.push(...genDrivers(Math.round(nv * 1.9), { depot: dep.id, ageMin: 19, ageMax: 90, maleRatio: 65 }, rng, '2026-10-27'));
  }
  autoAssign();
  caches.blocks.clear();
  return state.fleet;
}
function loadFleet() {
  const pub = window.FLEET_DATA || null;
  const saved = LS.get('fleet', null);
  if (saved && Array.isArray(saved.vehicles)) state.fleet = saved;
  else if (pub && Array.isArray(pub.vehicles)) {
    state.fleet = { vehicles: pub.vehicles, drivers: pub.drivers || [] };
    if (!LS.get('temps', null) && Array.isArray(pub.temps)) state.temps = pub.temps;
    if (!LS.get('settings', null) && pub.settings) state.settings = Object.assign({}, DEFAULT_SETTINGS, pub.settings);
  } else defaultFleet();
}

/* ================= UI helpers ================= */
const app = () => $('#app');
let cleanupFns = [];
function onCleanup(fn) { cleanupFns.push(fn); }
function modal(title, body, { foot = '', wide = false, onClose } = {}) {
  const d = document.createElement('dialog');
  if (wide) d.style.maxWidth = 'min(980px, calc(100vw - 24px))';
  d.innerHTML = `<div class="dlg-head"><h2>${title}</h2><button class="btn icon sm" data-close aria-label="閉じる">✕</button></div><div class="dlg-body">${body}</div>${foot ? `<div class="dlg-foot">${foot}</div>` : ''}`;
  document.body.append(d);
  d.addEventListener('click', (e) => { if (e.target === d || e.target.closest('[data-close]')) d.close(); });
  d.addEventListener('close', () => { d.remove(); onClose && onClose(); });
  d.showModal();
  return d;
}
function confirmBox(msg, okLabel = '実行する', danger = true) {
  return new Promise((res) => {
    let ok = false;
    const d = modal('確認', `<p style="margin:0">${msg}</p>`, { foot: `<button class="btn" data-close>キャンセル</button><button class="btn ${danger ? 'danger' : 'primary'}" data-ok>${okLabel}</button>`, onClose: () => res(ok) });
    $('[data-ok]', d).onclick = () => { ok = true; d.close(); };
  });
}
function download(name, text, type = 'application/json') {
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], { type })); a.download = name;
  document.body.append(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 500);
}
function readFile(accept) {
  return new Promise((res) => {
    const i = document.createElement('input'); i.type = 'file'; i.accept = accept;
    i.onchange = () => { const f = i.files[0]; if (!f) return res(null); const r = new FileReader(); r.onload = () => res(r.result); r.readAsText(f); };
    i.click();
  });
}
function stars(n) { n = clamp(+n || 0, 0, 5); return `<span class="stars" aria-label="5段階中${n}">${'★'.repeat(n)}<i>${'★'.repeat(5 - n)}</i></span>`; }
function routeDots(stop) {
  const cols = [...new Set((stop.routes || []).map((r) => G.route[r]?.color).filter(Boolean))].slice(0, 6);
  return cols.map((c) => `<i style="background:${esc(c)}"></i>`).join('');
}

/* 停留所の入力候補 */
function stopPicker(input, onPick) {
  const wrap = input.parentElement; const ul = document.createElement('ul'); ul.hidden = true; ul.setAttribute('role', 'listbox'); wrap.append(ul);
  input.setAttribute('role', 'combobox'); input.setAttribute('aria-autocomplete', 'list'); input.autocomplete = 'off';
  let items = [], sel = -1;
  const render = () => {
    const q = input.value.trim();
    if (q) {
      items = G.stopsActive.filter((s) => s.name.includes(q)).sort((a, b) => (b.name.startsWith(q) - a.name.startsWith(q)) || (G.rank[b.id] - G.rank[a.id])).slice(0, 40);
    } else items = G.stopsActive.slice().sort((a, b) => G.rank[b.id] - G.rank[a.id]).slice(0, 12);
    ul.innerHTML = items.length ? items.map((s, i) => `<li role="option" data-i="${i}" aria-selected="${i === sel}"><span>${esc(s.name)}</span><span class="dots">${routeDots(s)}</span></li>`).join('') : '<li aria-disabled="true" class="muted">該当する停留所がありません</li>';
    ul.hidden = false;
  };
  const choose = (s) => { input.value = s.name; input.dataset.id = s.id; ul.hidden = true; onPick && onPick(s); };
  input.addEventListener('focus', () => { sel = -1; render(); input.select(); });
  input.addEventListener('input', () => { sel = -1; delete input.dataset.id; render(); });
  input.addEventListener('blur', () => setTimeout(() => { ul.hidden = true; }, 150));
  input.addEventListener('keydown', (e) => {
    if (ul.hidden && e.key !== 'Enter') return;
    if (e.key === 'ArrowDown') { sel = Math.min(items.length - 1, sel + 1); render(); e.preventDefault(); }
    else if (e.key === 'ArrowUp') { sel = Math.max(0, sel - 1); render(); e.preventDefault(); }
    else if (e.key === 'Enter') { const s = items[sel >= 0 ? sel : 0]; if (s && !ul.hidden) { choose(s); e.preventDefault(); } }
    else if (e.key === 'Escape') ul.hidden = true;
  });
  ul.addEventListener('mousedown', (e) => { const li = e.target.closest('li[data-i]'); if (li) { e.preventDefault(); choose(items[+li.dataset.i]); } });
  return { set(id) { const s = G.stop[id]; if (s) { input.value = s.name; input.dataset.id = id; } } };
}

/* ================= 停留所時刻表 ================= */
function departuresAt(stopId, date) {
  const entries = G.stopSys[stopId] || []; const bySys = new Map();
  for (const e of entries) { if (!bySys.has(e.sys.id)) bySys.set(e.sys.id, []); bySys.get(e.sys.id).push(e.idx); }
  const out = [];
  for (const trip of tripsFor(date).list) {
    const idxs = bySys.get(trip.sys.id); if (!idxs) continue;
    for (const idx of idxs) if (idx >= trip.s && idx < trip.e && trip.times[idx]) out.push({ trip, idx, t: trip.times[idx][1], key: trip.sys.id + ':' + idx });
  }
  out.sort((a, b) => a.t - b.t);
  return out;
}
function groupLabel(sys, idx, stopId) {
  const occ = (G.stopSys[stopId] || []).filter((e) => e.sys.id === sys.id).map((e) => e.idx);
  if (occ.length < 2) return sysLabel(sys);
  if (sys.circular && idx === Math.max(...occ)) return `${stopName(sys.destination)}行（${sys.via ? sys.via + '・' : ''}循環の帰り）`;
  if (sys.circular) return sysLabel(sys);
  return `${sysLabel(sys)}（次は${stopName(sys.stops[idx + 1]?.stopId)}）`;
}
const tt = { stop: LS.get('lastStop', null), date: null, group: 'all' };
function viewTimetable(params) {
  if (params[0] && G.stop[params[0]]) { if (tt.stop !== params[0]) tt.group = 'all'; tt.stop = params[0]; }
  if (!tt.date) tt.date = serviceNow(true).date;
  app().innerHTML = `
    <div class="page-title"><h1>停留所時刻表</h1><p>当面のあいだ、毎日平日ダイヤで運行しています。</p></div>
    <div class="panel">
      <div class="row">
        <label class="field grow picker" style="min-width:220px"><span>停留所</span><input type="search" id="ttStop" placeholder="停留所名を入力（例：一花バスターミナル）"></label>
        <label class="field" style="width:170px"><span>日付</span><input type="date" id="ttDate" value="${tt.date}"></label>
      </div>
      <div id="ttPopular" class="stack" style="margin-top:12px"></div>
    </div>
    <div id="ttBody" style="margin-top:14px"></div>`;
  const pk = stopPicker($('#ttStop'), (s) => { location.hash = '#/timetable/' + s.id; });
  $('#ttDate').onchange = (e) => { if (e.target.value) { tt.date = e.target.value; renderTT(); } };
  if (tt.stop && G.stop[tt.stop]) { pk.set(tt.stop); LS.set('lastStop', tt.stop); }
  const tc = {}; for (const t of G.baseTrips) for (const i of [t.s, t.e]) { const id = t.sys.stops[i].stopId; tc[id] = (tc[id] || 0) + 1; }
  const pop = Object.keys(tc).sort((a, b) => tc[b] - tc[a]).slice(0, 12).map((id) => G.stop[id]);
  $('#ttPopular').innerHTML = `<div class="small muted">主な停留所（始発・終点）</div><div class="chips">${pop.map((s) => `<a class="chip" href="#/timetable/${s.id}" style="text-decoration:none;color:inherit">${esc(s.name)}</a>`).join('')}</div>`;
  renderTT();
}
function renderTT() {
  const box = $('#ttBody'); if (!box) return;
  if (!tt.stop || !G.stop[tt.stop]) { box.innerHTML = `<div class="panel empty">停留所名を入力するか、主な停留所から選んでください。</div>`; return; }
  const deps = departuresAt(tt.stop, tt.date);
  const groups = []; const gk = new Set();
  for (const e of (G.stopSys[tt.stop] || [])) {
    const k = e.sys.id + ':' + e.idx; if (gk.has(k)) continue; gk.add(k);
    const cnt = deps.filter((d) => d.key === k).length;
    groups.push({ k, sys: e.sys, idx: e.idx, cnt });
  }
  groups.sort((a, b) => (b.cnt > 0) - (a.cnt > 0) || a.sys.no.localeCompare(b.sys.no, 'ja', { numeric: true }));
  if (tt.group !== 'all' && !gk.has(tt.group)) tt.group = 'all';
  const shown = tt.group === 'all' ? deps : deps.filter((d) => d.key === tt.group);
  const sn = serviceNow(true); const isToday = sn.date === tt.date;
  const nextIdx = isToday ? shown.findIndex((d) => d.t >= sn.t) : -1;
  const hours = new Map();
  shown.forEach((d, i) => { const h = Math.floor(d.t / 60); if (!hours.has(h)) hours.set(h, []); hours.get(h).push({ ...d, i }); });
  const stop = G.stop[tt.stop];
  const chips = `<div class="chips" role="group" aria-label="系統で絞り込む">
      <button class="chip" data-g="all" aria-pressed="${tt.group === 'all'}">すべて（${deps.length}本）</button>
      ${groups.filter((g) => g.cnt).map((g) => `<button class="chip" data-g="${g.k}" aria-pressed="${tt.group === g.k}"><span class="sw" style="background:${esc(g.sys.color)}"></span>${esc(g.sys.no)} ${esc(groupLabel(g.sys, g.idx, tt.stop))}（${g.cnt}）</button>`).join('')}
    </div>`;
  const rows = [...hours.entries()].map(([h, list]) => `<tr><th scope="row">${h % 24}</th><td><div class="mins">${list.map((d) => {
    const partial = d.trip.e !== d.trip.sys.n - 1;
    const sub = tt.group === 'all' ? esc(d.trip.sys.no.replace(/^[^\d]+/, '')) : (partial ? esc(stopName(d.trip.sys.stops[d.trip.e].stopId)).slice(0, 5) : '');
    return `<button class="min ${isToday && d.t < sn.t ? 'past' : ''} ${d.i === nextIdx ? 'next' : ''}" data-trip="${esc(d.trip.id)}" data-idx="${d.idx}" title="${esc(d.trip.sys.no + ' ' + tripDestName(d.trip))}">
      <b>${pad2(d.t % 60)}</b>${d.trip.temp ? '<small class="tag temp">臨</small>' : ''}${sub ? `<small>${sub}</small>` : ''}${tt.group === 'all' ? `<span class="bar" style="background:${esc(d.trip.sys.color)}"></span>` : ''}</button>`;
  }).join('')}</div></td></tr>`).join('');
  box.innerHTML = `
    <div class="panel" style="margin-bottom:12px">${chips}</div>
    <section class="pole" aria-label="${esc(stop.name)} の時刻表">
      <div class="pole-head"><div><div class="sub">のりば</div><h2>${esc(stop.name)}</h2></div><div class="sub">${dateJa(tt.date)}　平日ダイヤ${isToday && nextIdx >= 0 ? `　次の発車 ${fmt(shown[nextIdx].t)}` : ''}</div></div>
      ${shown.length ? `<table class="tt"><tbody>${rows}</tbody></table>` : `<div class="empty">この日の発車予定はありません。</div>`}
      <div class="tt-legend"><span>時刻を押すと、その便が停車する停留所と運賃を確認できます。</span>${tt.group === 'all' ? '<span>数字の下は系統番号</span>' : ''}<span><span class="tag temp">臨</span> 臨時便</span>${isToday ? '<span>黄色の枠は次に発車する便</span>' : ''}</div>
    </section>`;
  $$('.chip[data-g]', box).forEach((b) => b.onclick = () => { tt.group = b.dataset.g; renderTT(); });
  $$('.min', box).forEach((b) => b.onclick = () => openTrip(b.dataset.trip, tt.date, +b.dataset.idx));
}

/* ================= 便の詳細（停車停留所） ================= */
function liveStatusHTML(sim, pos, t) {
  const trip = sim.trip; const st = trip.sys.stops;
  if (!pos) {
    if (t < sim.dep[trip.s]) return `<b>発車前</b>　${fmt(trip.dep)} に ${esc(stopName(st[trip.s].stopId))} を発車予定です。`;
    if (sim.accident) return `<span class="tag stop">運転打ち切り</span>　事故のため、この便は途中で運転を打ち切りました。`;
    const late = Math.round(sim.arr[trip.e] - trip.times[trip.e][0]);
    return `<b>運行終了</b>　${esc(stopName(st[trip.e].stopId))} に${late > 0 ? `約${late}分遅れて` : 'ほぼ定刻で'}到着しました。`;
  }
  if (pos.state === 'accident') return `<span class="tag stop">運転打ち切り</span>　${esc(stopName(st[pos.prev].stopId))}〜${esc(stopName(st[pos.next].stopId))} 間で事故が発生し、運転を打ち切りました。`;
  const dl = pos.delay > 0 ? `<span class="tag late">約${pos.delay}分遅れ</span>` : '<span class="tag ontime">ほぼ定刻</span>';
  const where = pos.state === 'stop' ? `${esc(stopName(st[pos.prev].stopId))} に停車中` : `次は ${esc(stopName(st[pos.next].stopId))}`;
  const ev = [...sim.events].reverse().find((e) => e.type === 'trouble' && e.at <= pos.prev && t - sim.arr[e.at] < 15);
  return `${dl}　<b>${where}</b>${ev ? `<div class="small muted">車内でのお客さま対応のため遅れが出ています。</div>` : ''}`;
}
function plateHTML(sim) {
  if (sim.substitute) return `<span class="plate"><small>車番</small><b>予備車</b></span>`;
  if (!sim.vehicle) return `<span class="plate"><small>車番</small><b>未登録</b></span>`;
  return `<span class="plate"><small>車番</small><b>${esc(sim.vehicle.no)}</b></span>`;
}
function vehicleInfoHTML(v) {
  if (!v) return '';
  return `<dl class="kv"><dt>車番</dt><dd>${esc(v.no)}</dd><dt>登録番号</dt><dd>${esc(v.plate || '—')}</dd><dt>車種</dt><dd>${esc(v.maker || '')} ${esc(v.model || '')}（${esc(v.type || '—')}）</dd><dt>年式</dt><dd>${esc(v.year || '—')}年</dd><dt>所属</dt><dd>${esc(depotName(v.depot))}</dd><dt>定員</dt><dd>${esc(v.capacity || '—')}人</dd><dt>設備</dt><dd>${esc(v.floor || '—')}</dd></dl>`;
}
function openTrip(tripId, date, boardIdx) {
  const trip = tripsFor(date).byId.get(tripId); if (!trip) { toast('便が見つかりませんでした'); return; }
  const sn = serviceNow(); const sim = sn.date === date ? simDay(date).byTrip.get(tripId) : null;
  const pos = sim ? posAt(sim, sn.t) : null;
  const st = trip.sys.stops; const hasBoard = boardIdx != null && boardIdx >= trip.s && boardIdx <= trip.e;
  let rows = '';
  for (let i = trip.s; i <= trip.e; i++) {
    const tm = trip.times[i]; if (!tm) continue;
    const done = pos && (i < pos.prev || (i === pos.prev && pos.state !== 'stop'));
    const cls = [hasBoard && i < boardIdx ? 'off' : '', hasBoard && i === boardIdx ? 'board' : '', done ? 'done' : ''].join(' ');
    const fa = hasBoard && i > boardIdx ? fareBetween(trip.sys, boardIdx, i) : null;
    const time = tm[1] > tm[0] && i !== trip.s && i !== trip.e ? `${fmt(tm[0])}<small>${fmt(tm[1])}発</small>` : fmt(i === trip.e ? tm[0] : tm[1]);
    rows += `<li class="${cls}"><span class="tm">${time}</span><span class="node"></span><span class="nm"><a href="#/timetable/${st[i].stopId}" data-close style="color:inherit;text-decoration:none">${esc(stopName(st[i].stopId))}</a>${hasBoard && i === boardIdx ? ' <span class="tag">乗車</span>' : ''}${pos && pos.state !== 'run' && i === pos.prev ? ` <span class="tag ${pos.state === 'accident' ? 'stop' : 'late'}">${pos.state === 'accident' ? '事故' : 'バス停車中'}</span>` : ''}</span><span class="fare">${fa != null ? `${yen(fa)}<span class="muted">／小児 ${yen(childFare(fa))}</span>` : ''}</span></li>`;
    if (pos && (pos.state === 'run' || pos.state === 'accident') && i === pos.prev) rows += `<li><span></span><span class="node"></span><span class="nm"><span class="tag ${pos.state === 'accident' ? 'stop' : 'late'}">${pos.state === 'accident' ? 'この区間で事故・運転打ち切り' : 'バス走行中'}</span></span><span></span></li>`;
  }
  const live = sim ? `<div class="livebox"><div class="row" style="align-items:center;justify-content:space-between"><div class="grow">${liveStatusHTML(sim, pos, sn.t)}<div class="small muted">${fmt(sn.t)} 時点</div></div>${pos ? plateHTML(sim) : ''}</div></div>` : '';
  const body = `${live}<p class="small muted" style="margin:0 0 10px">${dateJa(date)}　${esc(trip.sys.route?.name || '')}　${trip.temp ? '<span class="tag temp">臨時便</span> ' + esc(trip.note || '') : ''}${hasBoard ? '　運賃は乗車停留所からの金額（現金・大人／小児）' : ''}</p>
    <ol class="stoplist" style="--rc:${esc(trip.sys.color)}">${rows}</ol>`;
  const foot = pos ? `<a class="btn primary" href="#/live/${encodeURIComponent(trip.id)}" data-close>走行位置を地図で見る</a>` : '';
  modal(`${routeBadge(trip.sys)} ${esc(tripDestName(trip))}　<span class="muted" style="font-size:14px">${fmt(trip.dep)}発</span>`, body, { foot });
}

/* ================= 乗換案内 ================= */
const sr = LS.get('search', { from: null, to: null, xfer: 1 });
function viewSearch() {
  const sn = serviceNow(true);
  app().innerHTML = `
    <div class="page-title"><h1>乗換案内</h1><p>乗り換えを含めて、出発時刻以降で早く着く経路を探します。</p></div>
    <form class="panel" id="srForm" autocomplete="off">
      <div class="row">
        <label class="field grow picker" style="min-width:200px"><span>出発</span><input type="search" id="srFrom" placeholder="出発する停留所" required></label>
        <button type="button" class="btn icon" id="srSwap" aria-label="出発と到着を入れ替える" title="入れ替え">⇄</button>
        <label class="field grow picker" style="min-width:200px"><span>到着</span><input type="search" id="srTo" placeholder="到着する停留所" required></label>
      </div>
      <div class="row" style="margin-top:10px">
        <label class="field" style="width:160px"><span>日付</span><input type="date" id="srDate" value="${sn.date}"></label>
        <label class="field" style="width:120px"><span>出発時刻</span><input type="time" id="srTime" value="${hmInput(sn.t)}"></label>
        <label class="field" style="width:150px"><span>乗換にかける時間</span><select id="srXfer">${[0, 1, 3, 5, 10].map((v) => `<option value="${v}" ${+sr.xfer === v ? 'selected' : ''}>${v}分以上</option>`).join('')}</select></label>
        <button class="btn primary" type="submit" style="min-width:120px">検索する</button>
      </div>
    </form>
    <div id="srRes" style="margin-top:14px"></div>`;
  const pf = stopPicker($('#srFrom')), pt = stopPicker($('#srTo'));
  if (sr.from) pf.set(sr.from); if (sr.to) pt.set(sr.to);
  $('#srSwap').onclick = () => { const a = $('#srFrom'), b = $('#srTo'); const [v, i] = [a.value, a.dataset.id]; a.value = b.value; a.dataset.id = b.dataset.id || ''; b.value = v; b.dataset.id = i || ''; };
  $('#srForm').onsubmit = (e) => { e.preventDefault(); runSearch(); };
  if (sr.from && sr.to) runSearch();
}
function resolveStop(input) {
  if (input.dataset.id && G.stop[input.dataset.id]) return input.dataset.id;
  const s = G.stopsActive.find((x) => x.name === input.value.trim()); return s?.id || null;
}
function runSearch() {
  const box = $('#srRes'); const A = resolveStop($('#srFrom')), B = resolveStop($('#srTo'));
  if (!A || !B) { box.innerHTML = `<div class="panel empty">出発と到着の停留所を候補から選んでください。</div>`; return; }
  if (A === B) { box.innerHTML = `<div class="panel empty">出発と到着に同じ停留所が選ばれています。どちらかを変更してください。</div>`; return; }
  const date = $('#srDate').value || serviceNow(true).date; let t0 = parseHM($('#srTime').value) ?? 0;
  if (t0 < 180) t0 += 1440;
  const xfer = +$('#srXfer').value;
  Object.assign(sr, { from: A, to: B, xfer }); LS.set('search', sr);
  const res = searchJourneys(date, A, B, t0, xfer);
  if (!res.length) { box.innerHTML = `<div class="panel empty">${esc(fmt(t0))} 以降に ${esc(stopName(B))} へ着ける便が見つかりませんでした。時刻を早めるか、日付を変えて検索してください。</div>`; return; }
  box.innerHTML = `<p class="small muted" style="margin:0 0 8px">${esc(stopName(A))} → ${esc(stopName(B))}　${dateJa(date)} ${fmt(t0)} 以降</p>` + res.map((j, n) => {
    let adult = 0, child = 0, fareOk = true;
    const legs = j.legs.map((l, k) => {
      const a = fareBetween(l.trip.sys, l.i, l.j); if (a == null) fareOk = false; else { adult += a; child += childFare(a); }
      const nStops = l.trip.times.slice(l.i + 1, l.j + 1).filter(Boolean).length;
      const nxt = j.legs[k + 1];
      const wait = nxt ? nxt.trip.times[nxt.i][1] - l.trip.times[l.j][0] : null;
      return `<div class="leg" style="--rc:${esc(l.trip.sys.color)}"><span class="t">${fmt(l.trip.times[l.i][1])}</span><span class="rail"></span><div class="body"><b>${esc(stopName(l.trip.sys.stops[l.i].stopId))}</b>
          <div class="ride">${routeBadge(l.trip.sys)} ${esc(tripDestName(l.trip))}${l.trip.temp ? ' <span class="tag temp">臨時</span>' : ''}<span>${nStops}停留所・${l.trip.times[l.j][0] - l.trip.times[l.i][1]}分</span><span>${yen(a)}</span><button class="btn sm" data-trip="${esc(l.trip.id)}" data-idx="${l.i}">停車停留所</button></div></div></div>
        <div class="leg end" style="--rc:${esc(l.trip.sys.color)}"><span class="t">${fmt(l.trip.times[l.j][0])}</span><span class="rail"></span><div class="body"><b>${esc(stopName(l.trip.sys.stops[l.j].stopId))}</b></div></div>
        ${wait != null ? `<div class="wait">ここで乗り換え（待ち ${wait}分）</div>` : ''}`;
    }).join('');
    return `<article class="journey"><div class="journey-head"><span class="times">${fmt(j.dep)} → ${fmt(j.arr)}</span><span>所要 ${j.arr - j.dep}分</span><span>乗換 ${j.tr}回</span><span>運賃 ${fareOk ? `${yen(adult)}（小児 ${yen(child)}）` : '一部不明'}</span>${n === 0 ? '<span class="tag ontime">いちばん早く着く</span>' : ''}</div><div class="legs">${legs}</div></article>`;
  }).join('') + `<p class="note" style="margin-top:12px">時刻はダイヤ上の予定です。運賃は現金での大人運賃を乗車ごとに合計した金額です。</p>`;
  $$('[data-trip]', box).forEach((b) => b.onclick = () => openTrip(b.dataset.trip, date, +b.dataset.idx));
}

/* ================= 走行位置 ================= */
const lv = { sel: null, route: 'all', vb: null };
function viewLive(params) {
  if (params[0]) lv.sel = decodeURIComponent(params[0]);
  const sn = serviceNow();
  const routesOpt = G.D.routes.map((r) => `<option value="${esc(r.id)}" ${lv.route === r.id ? 'selected' : ''}>${esc(r.name)}</option>`).join('');
  app().innerHTML = `
    <div class="page-title"><h1>走行位置</h1><p>バスのいまの位置を地図に表示します。渋滞や乗客対応で遅れることがあります。</p></div>
    <div class="clockbar">
      <div class="clock" id="lvClock" aria-live="off">--:--</div>
      <label class="field" style="width:150px"><span>表示する時刻</span><select id="lvMode"><option value="real">現在時刻</option><option value="custom">時刻を指定</option></select></label>
      <label class="field" id="lvCustomWrap" style="width:210px" ${clock.mode === 'real' ? 'hidden' : ''}><span>日時</span><input type="datetime-local" id="lvAt"></label>
      <label class="field" id="lvSpeedWrap" style="width:120px" ${clock.mode === 'real' ? 'hidden' : ''}><span>進み方</span><select id="lvSpeed">${[1, 10, 30, 60].map((v) => `<option value="${v}" ${clock.speed === v ? 'selected' : ''}>${v === 1 ? '等速' : v + '倍速'}</option>`).join('')}</select></label>
    </div>
    <div class="live">
      <div class="mapwrap" id="lvMap">
        <svg id="lvSvg" role="img" aria-label="路線図とバスの位置"></svg>
        <div class="mapctl"><button class="btn icon" id="zIn" aria-label="拡大">＋</button><button class="btn icon" id="zOut" aria-label="縮小">－</button><button class="btn icon" id="zAll" aria-label="全体を表示" title="全体">⤢</button></div>
      </div>
      <aside class="panel stack">
        <form class="row" id="lvFind" autocomplete="off"><label class="field grow"><span>車番で探す</span><input type="search" id="lvNo" placeholder="例：A1803"></label><button class="btn" type="submit">探す</button></form>
        <label class="field"><span>路線</span><select id="lvRoute"><option value="all">すべての路線</option>${routesOpt}</select></label>
        <div id="lvDetail"></div>
        <div><div class="small muted" id="lvCount"></div><div class="buslist" id="lvList"></div></div>
      </aside>
    </div>`;
  $('#lvMode').value = clock.mode;
  const at = $('#lvAt'); const nd = nowDate(); at.value = `${dateStr(nd)}T${pad2(nd.getHours())}:${pad2(nd.getMinutes())}`;
  $('#lvMode').onchange = (e) => {
    if (e.target.value === 'real') { clock.mode = 'real'; } else { const d = nowDate(); clock.mode = 'custom'; clock.base = d.getTime(); clock.setAt = Date.now(); clock.speed = +$('#lvSpeed').value; }
    $('#lvCustomWrap').hidden = $('#lvSpeedWrap').hidden = clock.mode === 'real'; tick();
  };
  at.onchange = () => { const d = new Date(at.value); if (!isNaN(d)) { clock.mode = 'custom'; clock.base = d.getTime(); clock.setAt = Date.now(); tick(); } };
  $('#lvSpeed').onchange = (e) => { const d = nowDate(); clock.base = d.getTime(); clock.setAt = Date.now(); clock.speed = +e.target.value; };
  $('#lvRoute').onchange = (e) => { lv.route = e.target.value; tick(); };
  $('#lvFind').onsubmit = (e) => { e.preventDefault(); findVehicle($('#lvNo').value.trim()); };
  buildMap();
  tick();
  const iv = setInterval(tick, 1000); onCleanup(() => clearInterval(iv));
  const onRs = () => { lv.upp = null; applyVB(); }; window.addEventListener('resize', onRs); onCleanup(() => window.removeEventListener('resize', onRs));
  void sn;
}
function buildMap() {
  const svg = $('#lvSvg'); const b = G.bounds; const pad = 18;
  const full = { x: b.x0 - pad, y: b.y0 - pad, w: b.x1 - b.x0 + pad * 2, h: b.y1 - b.y0 + pad * 2 };
  lv.full = full; lv.upp = null; if (!lv.vb) lv.vb = { ...full };
  const lines = new Map();
  for (const s of Object.values(G.sys)) {
    const k = s.routeId + '|' + s.lineId; if (lines.has(k) && s.direction === 'up') continue;
    lines.set(k, { color: s.color, rid: s.routeId, pts: s.stops.map((x) => G.stop[x.stopId]).filter(Boolean).map((p) => `${p.x},${p.y}`).join(' ') });
  }
  const terminals = new Set(Object.values(G.sys).flatMap((s) => [s.origin, s.destination]));
  const used = G.stopsActive;
  svg.innerHTML = `<g id="lyRoutes" fill="none" stroke-linejoin="round" stroke-linecap="round">${[...lines.values()].map((l) => `<polyline data-r="${esc(l.rid)}" points="${l.pts}" stroke="${esc(l.color)}" stroke-width="3.5" vector-effect="non-scaling-stroke" opacity=".75"/>`).join('')}</g>
    <g id="lyStops">${used.map((s) => `<circle cx="${s.x}" cy="${s.y}" data-t="${terminals.has(s.id) ? 1 : 0}" r="1" fill="var(--surface)" stroke="var(--ink)" stroke-width="1.2" vector-effect="non-scaling-stroke"><title>${esc(s.name)}</title></circle>`).join('')}</g>
    <g id="lyLabels">${used.map((s) => `<text class="stoplabel ${terminals.has(s.id) || G.rank[s.id] >= 6 ? '' : 'minor'}" data-x="${s.x}" data-y="${s.y}" x="${s.x}" y="${s.y}">${esc(s.name)}</text>`).join('')}</g>
    <g id="lyBuses"></g>`;
  applyVB();
  // pan & zoom
  let drag = null;
  svg.addEventListener('pointerdown', (e) => { if (e.target.closest('.bus')) return; drag = { x: e.clientX, y: e.clientY, vb: { ...lv.vb }, moved: false }; svg.setPointerCapture(e.pointerId); svg.classList.add('drag'); });
  svg.addEventListener('pointermove', (e) => {
    if (!drag) return; const r = svg.getBoundingClientRect(); const s = Math.max(lv.vb.w / r.width, lv.vb.h / r.height);
    lv.vb.x = drag.vb.x - (e.clientX - drag.x) * s; lv.vb.y = drag.vb.y - (e.clientY - drag.y) * s; applyVB();
  });
  const end = () => { drag = null; svg.classList.remove('drag'); };
  svg.addEventListener('pointerup', end); svg.addEventListener('pointercancel', end);
  svg.addEventListener('wheel', (e) => {
    e.preventDefault(); const r = svg.getBoundingClientRect();
    const s = Math.max(lv.vb.w / r.width, lv.vb.h / r.height);
    const ox = (r.width - lv.vb.w / s) / 2, oy = (r.height - lv.vb.h / s) / 2;
    zoomAt(e.deltaY < 0 ? 0.8 : 1.25, lv.vb.x + (e.clientX - r.left - ox) * s, lv.vb.y + (e.clientY - r.top - oy) * s);
  }, { passive: false });
  $('#zIn').onclick = () => zoomAt(0.7); $('#zOut').onclick = () => zoomAt(1.4); $('#zAll').onclick = () => { lv.vb = { ...lv.full }; applyVB(); };
  $('#lyBuses').addEventListener('click', (e) => { const g = e.target.closest('.bus'); if (g) { lv.sel = g.dataset.id; lv.vehMsg = null; tick(); } });
}
function zoomAt(f, cx, cy) {
  const vb = lv.vb; cx ??= vb.x + vb.w / 2; cy ??= vb.y + vb.h / 2;
  const nw = clamp(vb.w * f, 30, lv.full.w * 1.5), k = nw / vb.w;
  lv.vb = { x: cx - (cx - vb.x) * k, y: cy - (cy - vb.y) * k, w: nw, h: vb.h * k }; applyVB();
}
function applyVB() {
  const svg = $('#lvSvg'); if (!svg) return; const v = lv.vb;
  svg.setAttribute('viewBox', `${v.x} ${v.y} ${v.w} ${v.h}`);
  const wrap = $('#lvMap'); const ratio = v.w / lv.full.w;
  wrap.classList.toggle('z1', ratio < 0.5); wrap.classList.toggle('z2', ratio < 0.28);
  const r = svg.getBoundingClientRect(); const upp = Math.max(v.w / (r.width || 800), v.h / (r.height || 600));
  if (lv.upp && Math.abs(lv.upp - upp) < 1e-9) return; lv.upp = upp;
  const far = ratio > 0.5;
  $$('#lyStops circle', svg).forEach((c) => c.setAttribute('r', (c.dataset.t === '1' ? (far ? 3 : 4.2) : (far ? 1.8 : 3)) * upp));
  const lab = $('#lyLabels', svg); lab.style.fontSize = (11.5 * upp) + 'px'; lab.style.strokeWidth = (3 * upp) + 'px';
  $$('text', lab).forEach((t) => { t.setAttribute('x', +t.dataset.x + 6 * upp); t.setAttribute('y', +t.dataset.y - 5 * upp); });
  $$('#lyBuses .bus', svg).forEach((g) => { g.style.scale = String(upp * 2.6); });
}
function centerOn(x, y) {
  const v = lv.vb; if (v.w > lv.full.w * 0.45) { const k = 0.35 * lv.full.w / v.w; v.w *= k; v.h *= k; }
  v.x = x - v.w / 2; v.y = y - v.h / 2; applyVB();
}
function tick() {
  const clk = $('#lvClock'); if (!clk) return;
  const sn = serviceNow();
  clk.innerHTML = `${fmt(sn.t)}<small>${dateJa(dateStr(sn.d))}${clock.mode === 'custom' ? '・指定時刻' : ''}</small>`;
  const all = activeSims(sn.date, sn.t);
  const shown = all.filter((a) => lv.route === 'all' || a.sim.trip.sys.routeId === lv.route);
  $$('#lyRoutes polyline').forEach((p) => p.setAttribute('opacity', lv.route === 'all' || p.dataset.r === lv.route ? '.75' : '.12'));
  // markers
  const layer = $('#lyBuses'); const have = new Map($$('.bus', layer).map((g) => [g.dataset.id, g]));
  for (const { sim, pos } of shown) {
    const id = sim.trip.id; let g = have.get(id);
    const label = sim.trip.sys.no.replace(/^[^\d]+/, '') || sim.trip.sys.no.slice(-2);
    const fill = pos.state === 'accident' ? 'var(--danger)' : sim.trip.sys.color;
    if (!g) {
      g = document.createElementNS('http://www.w3.org/2000/svg', 'g'); g.setAttribute('class', 'bus'); g.dataset.id = id;
      g.innerHTML = `<circle class="ring" r="5.2" fill="none" stroke="var(--sign)" stroke-width="1.4"/><circle class="body" r="3.8" stroke="#fff" stroke-width=".7"/><text text-anchor="middle" y="1.05"></text><title></title>`;
      g.style.translate = `${pos.x}px ${pos.y}px`; g.style.scale = String((lv.upp || 1) * 2.6);
      layer.append(g);
    } else have.delete(id);
    g.style.translate = `${pos.x}px ${pos.y}px`;
    $('.body', g).setAttribute('fill', fill);
    $('text', g).textContent = pos.state === 'accident' ? '!' : label;
    $('text', g).setAttribute('font-size', label.length > 3 ? '2.4' : '3.1');
    $('.ring', g).setAttribute('opacity', lv.sel === id ? '1' : (pos.delay >= 3 ? '.55' : '0'));
    $('.ring', g).setAttribute('stroke', lv.sel === id ? 'var(--ink)' : 'var(--sign)');
    $('title', g).textContent = `${sim.trip.sys.no} ${tripDestName(sim.trip)}${pos.delay ? `（約${pos.delay}分遅れ）` : ''}`;
  }
  for (const g of have.values()) g.remove();
  const selG = layer.querySelector(`.bus[data-id="${CSS.escape(lv.sel || '')}"]`); if (selG) layer.append(selG);
  // list
  shown.sort((a, b) => a.sim.trip.sys.no.localeCompare(b.sim.trip.sys.no, 'ja', { numeric: true }) || a.sim.trip.dep - b.sim.trip.dep);
  $('#lvCount').textContent = `走行中のバス ${shown.length}台${lv.route !== 'all' ? `（全路線 ${all.length}台）` : ''}`;
  const listEl = $('#lvList'); const listHtml = shown.length ? shown.map(({ sim, pos }) => {
    const st = sim.trip.sys.stops;
    const where = pos.state === 'accident' ? '<span class="tag stop">運転打ち切り</span>' : pos.state === 'stop' ? `${esc(stopName(st[pos.prev].stopId))}に停車中` : `次は ${esc(stopName(st[pos.next].stopId))}`;
    return `<div class="busrow ${lv.sel === sim.trip.id ? 'sel' : ''}" data-id="${esc(sim.trip.id)}" tabindex="0"><span>${routeBadge(sim.trip.sys)}</span><span><b>${esc(tripDestName(sim.trip))}</b><div class="w">${where}${pos.delay > 0 ? ` <span class="tag late">${pos.delay}分遅れ</span>` : ''}</div></span><span class="small muted">${sim.vehicle && !sim.substitute ? esc(sim.vehicle.no) : sim.substitute ? '予備車' : ''}</span></div>`;
  }).join('') : `<div class="empty">${sn.t >= 1440 + 60 || sn.t < 240 ? '運行時間外です。「時刻を指定」で日中の様子を見られます。' : 'この路線を走行中のバスはありません。'}</div>`;
  if (listEl._html !== listHtml) { listEl._html = listHtml; listEl.innerHTML = listHtml; }
  $$('#lvList .busrow').forEach((r) => { r.onclick = r.onkeydown = (e) => { if (e.type === 'keydown' && e.key !== 'Enter') return; lv.sel = r.dataset.id; lv.vehMsg = null; const p = all.find((a) => a.sim.trip.id === lv.sel); if (p) centerOn(p.pos.x, p.pos.y); tick(); }; });
  // detail
  const det = $('#lvDetail'); const cur = all.find((a) => a.sim.trip.id === lv.sel);
  if (!cur) { if (lv.vehMsg) { if (det.dataset.msg !== '1') { det.innerHTML = lv.vehMsg; det.dataset.msg = '1'; det._html = null; } return; } det.dataset.msg = ''; det._html = null; det.innerHTML = lv.sel ? '<div class="note">選んだバスは運行を終えました。</div>' : '<div class="note">地図上のバスか一覧の行を選ぶと、行先・遅れ・車番を確認できます。</div>'; return; }
  const { sim, pos } = cur; det.dataset.msg = '';
  const open = det.dataset.open === sim.trip.id && det.dataset.info === '1';
  const html = `<div class="livebox" style="margin:0"><div style="display:flex;justify-content:space-between;gap:10px;align-items:flex-start"><div>${routeBadge(sim.trip.sys)} <b>${esc(tripDestName(sim.trip))}</b><div class="small muted">${fmt(sim.trip.dep)} ${esc(stopName(sim.trip.sys.stops[sim.trip.s].stopId))}発</div></div>${plateHTML(sim)}</div>
    <div style="margin-top:8px">${liveStatusHTML(sim, pos, sn.t)}</div>
    ${sim.substitute ? '<div class="small muted">事故の影響で予備車が代走しています。</div>' : ''}
    <div class="row" style="margin-top:10px"><button class="btn sm" id="lvStops">停車停留所</button>${sim.vehicle && !sim.substitute ? `<button class="btn sm" id="lvVeh" aria-expanded="${open}">${open ? '車両情報を閉じる' : '車両情報'}</button>` : ''}</div>
    ${open && sim.vehicle ? `<div style="margin-top:10px">${vehicleInfoHTML(sim.vehicle)}</div>` : ''}</div>`;
  det.dataset.open = sim.trip.id;
  if (det._html === html) return; det._html = html; det.innerHTML = html;
  $('#lvStops').onclick = () => openTrip(sim.trip.id, sn.date, null);
  const vb = $('#lvVeh'); if (vb) vb.onclick = () => { det.dataset.info = det.dataset.info === '1' ? '0' : '1'; tick(); };
}
function findVehicle(q) {
  if (!q) return;
  const norm = (s) => String(s).normalize('NFKC').toUpperCase().replace(/[\s-]/g, '');
  const v = state.fleet.vehicles.find((x) => norm(x.no) === norm(q)) || state.fleet.vehicles.find((x) => norm(x.no).includes(norm(q)));
  const det = $('#lvDetail');
  if (!v) { lv.vehMsg = `<div class="note">車番「${esc(q)}」の車両は登録されていません。</div>`; det.dataset.msg = ''; lv.sel = null; tick(); return; }
  const sn = serviceNow(); const all = activeSims(sn.date, sn.t);
  const cur = all.find((a) => a.sim.vehicle?.id === v.id && !a.sim.substitute);
  if (cur) { lv.vehMsg = null; lv.sel = cur.sim.trip.id; lv.route = 'all'; $('#lvRoute').value = 'all'; centerOn(cur.pos.x, cur.pos.y); tick(); return; }
  lv.sel = null;
  const blk = simDay(sn.date).byBlock.find((b) => b.vehicle?.id === v.id);
  const next = blk?.sims.find((s) => !s.substitute && s.dep[s.trip.s] > sn.t);
  let msg;
  if (v.status === '休車') msg = 'この車両は休車中です。';
  else if (!blk) msg = 'この車両は本日の運用に入っていません（予備車）。';
  else if (next) msg = `いまは走行していません。次は ${fmt(next.trip.dep)} ${esc(stopName(next.trip.sys.stops[next.trip.s].stopId))}発 ${routeBadge(next.trip.sys)} ${esc(tripDestName(next.trip))} の予定です。`;
  else msg = '本日の運行は終了しました。';
  lv.vehMsg = `<div class="livebox" style="margin:0"><div style="display:flex;justify-content:space-between;gap:10px"><div>${msg}</div><span class="plate"><small>車番</small><b>${esc(v.no)}</b></span></div><div style="margin-top:10px">${vehicleInfoHTML(v)}</div></div>`;
  det.dataset.msg = ''; tick();
}

/* ================= 事業者用 ================= */
const isAdmin = () => sessionStorage.getItem(CFG.storagePrefix + 'admin') === '1';
const currentHash = () => LS.get('pwHash', null) || CFG.adminPasswordHash;
let failCount = 0, lockUntil = 0;
function viewLogin() {
  app().innerHTML = `
    <div class="page-title"><h1>事業者用ページ</h1><p>車両・乗務員・臨時便の管理には8桁のパスワードが必要です。</p></div>
    <form class="panel" id="lgForm" style="max-width:420px" autocomplete="off">
      <label class="field"><span>パスワード（数字8桁）</span><input type="password" id="lgPw" inputmode="numeric" maxlength="8" pattern="\\d{8}" required autocomplete="current-password" style="font-size:22px;letter-spacing:.3em;text-align:center"></label>
      <p id="lgMsg" class="small" style="color:var(--danger);min-height:1.5em;margin:8px 0" role="alert"></p>
      <button class="btn primary" type="submit" style="width:100%">ログインする</button>
    </form>`;
  const pw = $('#lgPw'); pw.focus();
  pw.oninput = () => { pw.value = pw.value.replace(/\D/g, '').slice(0, 8); };
  $('#lgForm').onsubmit = (e) => {
    e.preventDefault(); const msg = $('#lgMsg');
    if (Date.now() < lockUntil) { msg.textContent = `入力の失敗が続いたため、${Math.ceil((lockUntil - Date.now()) / 1000)}秒後にもう一度お試しください。`; return; }
    if (!/^\d{8}$/.test(pw.value)) { msg.textContent = 'パスワードは数字8桁で入力してください。'; return; }
    if (pwHash(pw.value) === currentHash()) { sessionStorage.setItem(CFG.storagePrefix + 'admin', '1'); failCount = 0; route(); return; }
    failCount++; if (failCount >= 5) { lockUntil = Date.now() + 30000; failCount = 0; }
    msg.textContent = 'パスワードが違います。'; pw.value = ''; pw.focus();
  };
}
const ADMIN_TABS = [['vehicles', '車両'], ['drivers', '乗務員'], ['blocks', '運用表'], ['temps', '臨時便'], ['settings', '設定']];
function viewAdmin(params) {
  if (!isAdmin()) return viewLogin();
  const sub = ADMIN_TABS.some(([k]) => k === params[0]) ? params[0] : 'vehicles';
  app().innerHTML = `<div class="page-title" style="justify-content:space-between"><h1>事業者用ページ</h1><button class="btn sm" id="logout">ログアウト</button></div>
    <nav class="subnav">${ADMIN_TABS.map(([k, n]) => `<a href="#/admin/${k}" ${k === sub ? 'aria-current="page"' : ''}>${n}</a>`).join('')}</nav><div id="adm"></div>`;
  $('#logout').onclick = () => { sessionStorage.removeItem(CFG.storagePrefix + 'admin'); location.hash = '#/timetable'; };
  ({ vehicles: admVehicles, drivers: admDrivers, blocks: admBlocks, temps: admTemps, settings: admSettings })[sub]();
}
const depotOptions = (sel, extra = '') => extra + G.depots.map((d) => `<option value="${esc(d.id)}" ${d.id === sel ? 'selected' : ''}>${esc(d.name)}</option>`).join('');
const driverName = (d) => `${d.sur} ${d.given}`;
function sortRows(rows, key, dir, getters) { const g = getters[key]; if (!g) return rows; return rows.slice().sort((a, b) => { const x = g(a), y = g(b); return (typeof x === 'number' && typeof y === 'number' ? x - y : String(x).localeCompare(String(y), 'ja', { numeric: true })) * dir; }); }
function csvLine(arr) { return arr.map((v) => { const s = String(v ?? ''); return /[",\n]/.test(s) ? `"${s.replace(/"/g, '""')}"` : s; }).join(','); }

/* ---- 車両 ---- */
const av = { q: '', depot: 'all', sort: 'no', dir: 1 };
function admVehicles() {
  const box = $('#adm'); const today = serviceNow(true).date; const { perDepot } = blocksFor(today);
  const vehs = state.fleet.vehicles;
  const sum = G.depots.map((d) => { const n = vehs.filter((v) => v.depot === d.id && v.status !== '休車').length; const need = perDepot[d.id] || 0; return `<div class="panel"><div class="small muted">${esc(d.name)}</div><div style="font-size:22px;font-weight:700">${n}台 <span class="small muted" style="font-weight:400">稼働 ／ 本日の運用 ${need}</span></div>${n < need ? `<div class="small" style="color:var(--danger)">${need - n}運用で車両が足りません。足りない運用は「車番未登録」で表示されます。</div>` : ''}</div>`; }).join('');
  box.innerHTML = `<div class="grid2" style="margin-bottom:14px">${sum}</div>
    <div class="row" style="margin-bottom:12px">
      <label class="field grow" style="min-width:180px"><span>検索</span><input type="search" id="vQ" value="${esc(av.q)}" placeholder="車番・登録番号・車種"></label>
      <label class="field" style="width:220px"><span>所属</span><select id="vDep">${depotOptions(av.depot, '<option value="all">すべて</option>')}</select></label>
      <button class="btn primary" id="vAdd">車両を追加</button><button class="btn" id="vRand">ランダムに追加</button><button class="btn" id="vCsv">CSVで書き出す</button>
    </div>
    <div id="vTable"></div>`;
  $('#vDep').value = av.depot;
  $('#vQ').oninput = (e) => { av.q = e.target.value; drawVehicles(); };
  $('#vDep').onchange = (e) => { av.depot = e.target.value; drawVehicles(); };
  $('#vAdd').onclick = () => editVehicle(null);
  $('#vRand').onclick = randomVehicles;
  $('#vCsv').onclick = () => download('vehicles.csv', '\ufeff' + [csvLine(['車番', '登録番号', 'メーカー', '車種', '大きさ', '年式', '所属', '定員', '設備', '状態', '担当乗務員', '備考']), ...state.fleet.vehicles.map((v) => csvLine([v.no, v.plate, v.maker, v.model, v.type, v.year, depotName(v.depot), v.capacity, v.floor, v.status, driversOfVehicleAll(v.id).map(driverName).join(' / '), v.note]))].join('\n'), 'text/csv');
  drawVehicles();
}
const driversOfVehicleAll = (vid) => state.fleet.drivers.filter((d) => d.vehicleId === vid);
function drawVehicles() {
  const q = av.q.trim();
  let rows = state.fleet.vehicles.filter((v) => (av.depot === 'all' || v.depot === av.depot) && (!q || [v.no, v.plate, v.maker, v.model].join(' ').includes(q)));
  rows = sortRows(rows, av.sort, av.dir, { no: (v) => v.no, plate: (v) => v.plate, model: (v) => v.maker + v.model, year: (v) => +v.year, depot: (v) => depotName(v.depot), cap: (v) => +v.capacity, status: (v) => v.status, drv: (v) => driversOfVehicleAll(v.id).length });
  const th = (k, n) => `<th data-sort="${k}" aria-sort="${av.sort === k ? (av.dir > 0 ? 'ascending' : 'descending') : 'none'}">${n}${av.sort === k ? (av.dir > 0 ? ' ▲' : ' ▼') : ''}</th>`;
  $('#vTable').innerHTML = rows.length ? `<p class="small muted" style="margin:0 0 6px">${rows.length}台</p><div class="tablewrap"><table class="data"><thead><tr>${th('no', '車番')}${th('plate', '登録番号')}${th('model', '車種')}${th('year', '年式')}${th('depot', '所属')}${th('cap', '定員')}${th('status', '状態')}${th('drv', '担当乗務員')}<th></th></tr></thead><tbody>${rows.map((v) => {
    const ds = driversOfVehicleAll(v.id);
    return `<tr><td><b>${esc(v.no)}</b></td><td>${esc(v.plate)}</td><td>${esc(v.maker)} ${esc(v.model)} <span class="muted small">${esc(v.type)}・${esc(v.floor)}</span></td><td class="num">${esc(v.year)}</td><td>${esc(depotShort(v.depot))}</td><td class="num">${esc(v.capacity)}</td><td>${v.status === '休車' ? '<span class="tag temp">休車</span>' : '稼働'}</td><td>${ds.length ? ds.map((d) => esc(driverName(d))).join('、') : '<span class="muted">未設定</span>'}</td><td><button class="btn sm" data-ed="${esc(v.id)}">編集</button></td></tr>`;
  }).join('')}</tbody></table></div>` : `<div class="panel empty">条件に合う車両はありません。「車両を追加」または「ランダムに追加」で登録できます。</div>`;
  $$('#vTable th[data-sort]').forEach((t) => t.onclick = () => { av.dir = av.sort === t.dataset.sort ? -av.dir : 1; av.sort = t.dataset.sort; drawVehicles(); });
  $$('#vTable [data-ed]').forEach((b) => b.onclick = () => editVehicle(b.dataset.ed));
}
function editVehicle(id) {
  const v = id ? state.fleet.vehicles.find((x) => x.id === id) : { id: uid('v'), no: '', plate: '', maker: 'いすゞ', model: 'エルガ', type: '大型', year: new Date().getFullYear(), depot: G.depots[0].id, capacity: 78, floor: 'ノンステップ', status: '稼働', note: '' };
  const assigned = new Set(id ? driversOfVehicleAll(id).map((d) => d.id) : []);
  const drvList = (dep) => state.fleet.drivers.filter((d) => d.depot === dep && d.status !== '休職').sort((a, b) => (assigned.has(b.id) - assigned.has(a.id)) || (!a.vehicleId - !b.vehicleId) * -1 || a.empNo.localeCompare(b.empNo, 'ja', { numeric: true }));
  const vehNo = (vid) => state.fleet.vehicles.find((x) => x.id === vid)?.no;
  const sel = (name, opts, cur) => `<select name="${name}">${opts.map((o) => `<option ${o === cur ? 'selected' : ''}>${esc(o)}</option>`).join('')}</select>`;
  const d = modal(id ? `車両を編集（${esc(v.no)}）` : '車両を追加', `
    <form id="vf" class="stack">
      <div class="grid2">
        <label class="field"><span>車番（必須）</span><input type="text" name="no" value="${esc(v.no)}" required maxlength="20"></label>
        <label class="field"><span>登録番号</span><input type="text" name="plate" value="${esc(v.plate)}" maxlength="30"></label>
        <label class="field"><span>メーカー</span><input type="text" name="maker" value="${esc(v.maker)}" list="makerList"></label>
        <label class="field"><span>車種</span><input type="text" name="model" value="${esc(v.model)}"></label>
        <label class="field"><span>年式</span><input type="number" name="year" value="${esc(v.year)}" min="1950" max="2100"></label>
        <label class="field"><span>所属営業所</span><select name="depot">${depotOptions(v.depot)}</select></label>
        <label class="field"><span>定員（人）</span><input type="number" name="capacity" value="${esc(v.capacity)}" min="1" max="200"></label>
        <label class="field"><span>大きさ</span>${sel('type', ['大型', '中型', '小型'], v.type)}</label>
        <label class="field"><span>設備</span>${sel('floor', ['ノンステップ', 'ワンステップ', 'ツーステップ'], v.floor)}</label>
        <label class="field"><span>状態</span>${sel('status', ['稼働', '休車'], v.status)}</label>
      </div>
      <label class="field"><span>備考</span><input type="text" name="note" value="${esc(v.note)}"></label>
      <fieldset style="border:1px solid var(--line);border-radius:8px;padding:10px 12px"><legend class="small" style="font-weight:700">担当乗務員（担当車制度）</legend>
        <p class="small muted" style="margin:0 0 6px">チェックした乗務員がこの車両の担当になります。担当者は日替わりでこの車両に乗務します。ほかの車両の担当から移る乗務員には現在の担当車を表示しています。</p>
        <div id="vfDrv" style="max-height:220px;overflow:auto"></div></fieldset>
      <datalist id="makerList">${[...new Set(MODELS.map((m) => m.maker))].map((m) => `<option value="${esc(m)}">`).join('')}</datalist>
      <p class="small" id="vfErr" style="color:var(--danger);margin:0" role="alert"></p>
    </form>`, { foot: `${id ? '<button class="btn danger" id="vfDel" style="margin-right:auto">削除</button>' : ''}<button class="btn" data-close>キャンセル</button><button class="btn primary" id="vfSave">保存する</button>` });
  const f = $('#vf', d);
  const drawDrv = () => {
    const list = drvList(f.depot.value);
    $('#vfDrv', d).innerHTML = list.length ? list.map((x) => `<label style="display:flex;gap:8px;align-items:center;padding:3px 0"><input type="checkbox" value="${esc(x.id)}" ${assigned.has(x.id) ? 'checked' : ''}> ${esc(driverName(x))} <span class="small muted">${esc(x.empNo)}・運転${x.skill}・接客${x.service}${x.vehicleId && x.vehicleId !== v.id ? `・現在 ${esc(vehNo(x.vehicleId) || '—')} 担当` : ''}</span></label>`).join('') : '<p class="small muted">この営業所に在籍する乗務員がいません。</p>';
    $$('#vfDrv input', d).forEach((c) => c.onchange = () => { if (c.checked) assigned.add(c.value); else assigned.delete(c.value); });
  };
  f.depot.onchange = drawDrv; drawDrv();
  $('#vfSave', d).onclick = () => {
    const no = f.no.value.trim();
    if (!no) { $('#vfErr', d).textContent = '車番を入力してください。'; return; }
    if (state.fleet.vehicles.some((x) => x.no === no && x.id !== v.id)) { $('#vfErr', d).textContent = `車番「${no}」はすでに登録されています。`; return; }
    Object.assign(v, { no, plate: f.plate.value.trim(), maker: f.maker.value.trim(), model: f.model.value.trim(), year: +f.year.value || '', depot: f.depot.value, capacity: +f.capacity.value || '', type: f.type.value, floor: f.floor.value, status: f.status.value, note: f.note.value.trim() });
    if (!id) state.fleet.vehicles.push(v);
    for (const dr of state.fleet.drivers) {
      if (assigned.has(dr.id)) dr.vehicleId = v.id;
      else if (dr.vehicleId === v.id) dr.vehicleId = null;
    }
    saveFleet(); d.close(); toast(id ? '車両を保存しました' : '車両を追加しました'); admVehicles();
  };
  const del = $('#vfDel', d);
  if (del) del.onclick = async () => {
    d.close();
    if (!(await confirmBox(`車番「${esc(v.no)}」を削除します。担当乗務員の紐づけも外れます。`, '削除する'))) return;
    state.fleet.vehicles = state.fleet.vehicles.filter((x) => x.id !== v.id);
    state.fleet.drivers.forEach((x) => { if (x.vehicleId === v.id) x.vehicleId = null; });
    saveFleet(); toast('車両を削除しました'); admVehicles();
  };
}
function randomVehicles() {
  const y = new Date().getFullYear();
  const d = modal('車両をランダムに追加', `<form class="stack" id="rv">
    <div class="grid2"><label class="field"><span>台数</span><input type="number" name="n" value="10" min="1" max="500"></label>
    <label class="field"><span>所属</span><select name="depot">${depotOptions('', '<option value="auto" selected>各営業所に均等</option>')}</select></label>
    <label class="field"><span>年式（から）</span><input type="number" name="y0" value="${y - 15}" min="1950" max="2100"></label>
    <label class="field"><span>年式（まで）</span><input type="number" name="y1" value="${y}" min="1950" max="2100"></label></div>
    <p class="note">車番は「営業所記号＋年式下2桁＋連番」（例：A1803）で付けます。あとから編集できます。</p></form>`,
  { foot: '<button class="btn" data-close>キャンセル</button><button class="btn primary" id="rvGo">追加する</button>' });
  $('#rvGo', d).onclick = () => {
    const f = $('#rv', d); const n = clamp(+f.n.value || 0, 1, 500); let y0 = +f.y0.value, y1 = +f.y1.value; if (y0 > y1) [y0, y1] = [y1, y0];
    state.fleet.vehicles.push(...genVehicles(n, { depot: f.depot.value, yearFrom: y0, yearTo: y1 }));
    saveFleet(); d.close(); toast(`${n}台を追加しました`); admVehicles();
  };
}

/* ---- 乗務員 ---- */
const ad = { q: '', depot: 'all', gender: 'all', sort: 'empNo', dir: 1, page: 0 };
function admDrivers() {
  const box = $('#adm');
  box.innerHTML = `<div id="dStats" class="grid2" style="margin-bottom:14px"></div>
    <div class="row" style="margin-bottom:12px">
      <label class="field grow" style="min-width:160px"><span>検索</span><input type="search" id="dQ" value="${esc(ad.q)}" placeholder="氏名・社員番号・担当車番"></label>
      <label class="field" style="width:200px"><span>所属</span><select id="dDep">${depotOptions(ad.depot, '<option value="all">すべて</option>')}</select></label>
      <label class="field" style="width:100px"><span>性別</span><select id="dGen"><option value="all">すべて</option><option>男</option><option>女</option></select></label>
    </div>
    <div class="row" style="margin-bottom:12px">
      <button class="btn primary" id="dAdd">乗務員を追加</button><button class="btn" id="dRand">ランダムに登録</button><button class="btn" id="dAuto">担当車を自動で割り当て</button><button class="btn" id="dCsv">CSVで書き出す</button><button class="btn danger" id="dClear">全員を削除</button>
    </div>
    <div id="dTable"></div>`;
  $('#dDep').value = ad.depot; $('#dGen').value = ad.gender;
  $('#dQ').oninput = (e) => { ad.q = e.target.value; ad.page = 0; drawDrivers(); };
  $('#dDep').onchange = (e) => { ad.depot = e.target.value; ad.page = 0; drawDrivers(); };
  $('#dGen').onchange = (e) => { ad.gender = e.target.value; ad.page = 0; drawDrivers(); };
  $('#dAdd').onclick = () => editDriver(null);
  $('#dRand').onclick = randomDrivers;
  $('#dAuto').onclick = () => { const n = autoAssign(); saveFleet(); toast(n ? `${n}人に担当車を割り当てました` : '担当車が未設定の乗務員はいません'); drawDrivers(); };
  $('#dCsv').onclick = () => { const today = dateStr(new Date()); download('drivers.csv', '\ufeff' + [csvLine(['社員番号', '姓', '名', '性別', '生年月日', '年齢', '所属', '入社日', '運転技術', '接客態度', '担当車', '状態', '備考']), ...state.fleet.drivers.map((d) => csvLine([d.empNo, d.sur, d.given, d.gender, d.birth, ageOn(d.birth, today), depotName(d.depot), d.hired, d.skill, d.service, state.fleet.vehicles.find((v) => v.id === d.vehicleId)?.no || '', d.status, d.note]))].join('\n'), 'text/csv'); };
  $('#dClear').onclick = async () => { if (!state.fleet.drivers.length) return; if (!(await confirmBox(`登録されている乗務員 ${state.fleet.drivers.length}人をすべて削除します。元に戻せません。`, '全員を削除する'))) return; state.fleet.drivers = []; saveFleet(); toast('乗務員を全員削除しました'); admDrivers(); };
  drawDrivers();
}
function drawDrivers() {
  const today = dateStr(new Date()); const all = state.fleet.drivers;
  const vno = new Map(state.fleet.vehicles.map((v) => [v.id, v.no]));
  const male = all.filter((d) => d.gender === '男').length;
  const avgAge = all.length ? (all.reduce((a, d) => a + ageOn(d.birth, today), 0) / all.length).toFixed(1) : '—';
  const noVeh = all.filter((d) => !vno.has(d.vehicleId) && d.status !== '休職').length;
  $('#dStats').innerHTML = `<div class="panel"><div class="small muted">登録人数</div><div style="font-size:22px;font-weight:700">${all.length}人</div></div>
    <div class="panel"><div class="small muted">男女比</div><div style="font-size:22px;font-weight:700">${all.length ? `${Math.round(male / all.length * 100)} : ${100 - Math.round(male / all.length * 100)}` : '—'}</div><div class="small muted">男性${male}人・女性${all.length - male}人</div></div>
    <div class="panel"><div class="small muted">平均年齢</div><div style="font-size:22px;font-weight:700">${avgAge}歳</div></div>
    <div class="panel"><div class="small muted">担当車が未設定</div><div style="font-size:22px;font-weight:700">${noVeh}人</div></div>`;
  const q = ad.q.trim();
  let rows = all.filter((d) => (ad.depot === 'all' || d.depot === ad.depot) && (ad.gender === 'all' || d.gender === ad.gender) && (!q || [d.empNo, d.sur + d.given, d.sur + ' ' + d.given, vno.get(d.vehicleId) || ''].join(' ').includes(q)));
  rows = sortRows(rows, ad.sort, ad.dir, { empNo: (d) => d.empNo, name: (d) => d.sur + d.given, gender: (d) => d.gender, birth: (d) => d.birth, age: (d) => ageOn(d.birth, today), depot: (d) => depotName(d.depot), hired: (d) => d.hired, skill: (d) => d.skill, service: (d) => d.service, veh: (d) => vno.get(d.vehicleId) || '￿' });
  const per = 100, pages = Math.max(1, Math.ceil(rows.length / per)); ad.page = clamp(ad.page, 0, pages - 1);
  const pageRows = rows.slice(ad.page * per, ad.page * per + per);
  const th = (k, n) => `<th data-sort="${k}" aria-sort="${ad.sort === k ? (ad.dir > 0 ? 'ascending' : 'descending') : 'none'}">${n}${ad.sort === k ? (ad.dir > 0 ? ' ▲' : ' ▼') : ''}</th>`;
  const pager = pages > 1 ? `<div class="row" style="justify-content:center;margin-top:10px;align-items:center"><button class="btn sm" data-pg="-1" ${ad.page === 0 ? 'disabled' : ''}>前の100人</button><span class="small">${ad.page + 1} / ${pages}ページ</span><button class="btn sm" data-pg="1" ${ad.page >= pages - 1 ? 'disabled' : ''}>次の100人</button></div>` : '';
  $('#dTable').innerHTML = rows.length ? `<p class="small muted" style="margin:0 0 6px">${rows.length}人</p><div class="tablewrap"><table class="data"><thead><tr>${th('empNo', '社員番号')}${th('name', '氏名')}${th('gender', '性別')}${th('birth', '生年月日')}${th('age', '年齢')}${th('depot', '所属')}${th('hired', '入社日')}${th('skill', '運転技術')}${th('service', '接客態度')}${th('veh', '担当車')}<th></th></tr></thead><tbody>${pageRows.map((d) => `<tr><td>${esc(d.empNo)}</td><td><b>${esc(driverName(d))}</b>${d.status === '休職' ? ' <span class="tag temp">休職</span>' : ''}</td><td>${esc(d.gender)}</td><td>${esc(d.birth)}</td><td class="num">${ageOn(d.birth, today)}</td><td>${esc(depotShort(d.depot))}</td><td>${esc(d.hired)}</td><td>${stars(d.skill)}</td><td>${stars(d.service)}</td><td>${vno.has(d.vehicleId) ? esc(vno.get(d.vehicleId)) : '<span class="muted">未設定</span>'}</td><td><button class="btn sm" data-ed="${esc(d.id)}">編集</button></td></tr>`).join('')}</tbody></table></div>${pager}` : `<div class="panel empty">条件に合う乗務員はいません。「ランダムに登録」で人数を指定してまとめて登録できます。</div>`;
  $$('#dTable th[data-sort]').forEach((t) => t.onclick = () => { ad.dir = ad.sort === t.dataset.sort ? -ad.dir : 1; ad.sort = t.dataset.sort; drawDrivers(); });
  $$('#dTable [data-ed]').forEach((b) => b.onclick = () => editDriver(b.dataset.ed));
  $$('#dTable [data-pg]').forEach((b) => b.onclick = () => { ad.page += +b.dataset.pg; drawDrivers(); });
}
const SKILL_TXT = ['1 不安あり', '2 やや不安', '3 標準', '4 上手', '5 模範'];
const SERVICE_TXT = ['1 苦情が多い', '2 やや難あり', '3 標準', '4 丁寧', '5 模範'];
function editDriver(id) {
  const today = dateStr(new Date());
  const x = id ? state.fleet.drivers.find((d) => d.id === id) : { id: uid('d'), empNo: String(state.fleet.drivers.reduce((m, d) => Math.max(m, +d.empNo || 0), 100000) + 1), sur: '', given: '', gender: '男', birth: '1985-04-01', hired: today, depot: G.depots[0].id, skill: 3, service: 3, vehicleId: null, status: '在籍', note: '' };
  const vehOpts = (dep) => `<option value="">なし</option>` + state.fleet.vehicles.filter((v) => v.depot === dep).sort((a, b) => a.no.localeCompare(b.no, 'ja', { numeric: true })).map((v) => `<option value="${esc(v.id)}" ${v.id === x.vehicleId ? 'selected' : ''}>${esc(v.no)}（${esc(v.model)}・担当${driversOfVehicleAll(v.id).length}人）</option>`).join('');
  const d = modal(id ? `乗務員を編集（${esc(driverName(x))}）` : '乗務員を追加', `<form id="df" class="stack">
    <div class="grid2">
      <label class="field"><span>社員番号</span><input type="text" name="empNo" value="${esc(x.empNo)}" required maxlength="12"></label>
      <label class="field"><span>状態</span><select name="status"><option ${x.status === '在籍' ? 'selected' : ''}>在籍</option><option ${x.status === '休職' ? 'selected' : ''}>休職</option></select></label>
      <label class="field"><span>姓（必須）</span><input type="text" name="sur" value="${esc(x.sur)}" required maxlength="10"></label>
      <label class="field"><span>名（必須）</span><input type="text" name="given" value="${esc(x.given)}" required maxlength="10"></label>
      <label class="field"><span>性別</span><select name="gender"><option ${x.gender === '男' ? 'selected' : ''}>男</option><option ${x.gender === '女' ? 'selected' : ''}>女</option></select></label>
      <label class="field"><span>生年月日</span><input type="date" name="birth" value="${esc(x.birth)}" required></label>
      <label class="field"><span>所属営業所</span><select name="depot">${depotOptions(x.depot)}</select></label>
      <label class="field"><span>入社日</span><input type="date" name="hired" value="${esc(x.hired)}"></label>
      <label class="field"><span>運転技術</span><select name="skill">${SKILL_TXT.map((t, i) => `<option value="${i + 1}" ${x.skill === i + 1 ? 'selected' : ''}>${t}</option>`).join('')}</select></label>
      <label class="field"><span>接客態度</span><select name="service">${SERVICE_TXT.map((t, i) => `<option value="${i + 1}" ${x.service === i + 1 ? 'selected' : ''}>${t}</option>`).join('')}</select></label>
      <label class="field"><span>担当車</span><select name="vehicleId">${vehOpts(x.depot)}</select></label>
    </div>
    <label class="field"><span>備考</span><input type="text" name="note" value="${esc(x.note)}"></label>
    <p class="note">運転技術が低いと事故による運転打ち切りが起きやすく、高いと遅延が減ります。接客態度が良いと、乗客とのトラブルによる遅延が減ります。</p>
    <p class="small" id="dfErr" style="color:var(--danger);margin:0" role="alert"></p></form>`,
  { foot: `${id ? '<button class="btn danger" id="dfDel" style="margin-right:auto">削除</button>' : ''}<button class="btn" data-close>キャンセル</button><button class="btn primary" id="dfSave">保存する</button>` });
  const f = $('#df', d);
  f.depot.onchange = () => { f.vehicleId.innerHTML = vehOpts(f.depot.value); };
  $('#dfSave', d).onclick = () => {
    const err = (m) => { $('#dfErr', d).textContent = m; };
    if (!f.sur.value.trim() || !f.given.value.trim()) return err('姓と名を入力してください。');
    if (!f.birth.value) return err('生年月日を入力してください。');
    if (ageOn(f.birth.value, today) < 19) return err('バスの運転には19歳以上である必要があります。生年月日を確認してください。');
    if (state.fleet.drivers.some((o) => o.empNo === f.empNo.value.trim() && o.id !== x.id)) return err('この社員番号はすでに使われています。');
    Object.assign(x, { empNo: f.empNo.value.trim(), sur: f.sur.value.trim(), given: f.given.value.trim(), gender: f.gender.value, birth: f.birth.value, hired: f.hired.value, depot: f.depot.value, skill: +f.skill.value, service: +f.service.value, vehicleId: f.vehicleId.value || null, status: f.status.value, note: f.note.value.trim() });
    if (!id) state.fleet.drivers.push(x);
    saveFleet(); d.close(); toast(id ? '乗務員を保存しました' : '乗務員を追加しました'); drawDrivers();
  };
  const del = $('#dfDel', d);
  if (del) del.onclick = async () => { d.close(); if (!(await confirmBox(`${esc(driverName(x))}（${esc(x.empNo)}）を削除します。`, '削除する'))) return; state.fleet.drivers = state.fleet.drivers.filter((o) => o.id !== x.id); saveFleet(); toast('乗務員を削除しました'); drawDrivers(); };
}
function randomDrivers() {
  const d = modal('乗務員をランダムに登録', `<form class="stack" id="rd">
    <div class="grid2">
      <label class="field"><span>人数</span><input type="number" name="n" value="50" min="1" max="3000"></label>
      <label class="field"><span>所属</span><select name="depot">${depotOptions('', '<option value="auto" selected>各営業所に均等</option>')}</select></label>
      <label class="field"><span>年齢（下限）</span><input type="number" name="a0" value="19" min="19" max="90"></label>
      <label class="field"><span>年齢（上限）</span><input type="number" name="a1" value="90" min="19" max="90"></label>
    </div>
    <label class="field"><span>男女比 <output id="rdOut">男性 65 ： 女性 35</output></span><input type="range" name="ratio" min="60" max="70" step="1" value="65"></label>
    <label style="display:flex;gap:8px;align-items:center"><input type="checkbox" name="assign" checked> 登録後、担当車が未設定の乗務員に担当車を自動で割り当てる</label>
    <p class="note">年齢はバスの運転ができる19歳から90歳までの範囲で、40〜50代が多くなるように分布させます。氏名は約1,000種類の姓と約1,000種類の名（男女別）から組み合わせ、同じ氏名ができるだけ重ならないようにします。運転技術は経験年数が長いほど高くなりやすく設定します。</p></form>`,
  { foot: '<button class="btn" data-close>キャンセル</button><button class="btn primary" id="rdGo">登録する</button>' });
  const f = $('#rd', d);
  f.ratio.oninput = () => { $('#rdOut', d).textContent = `男性 ${f.ratio.value} ： 女性 ${100 - f.ratio.value}`; };
  $('#rdGo', d).onclick = () => {
    const n = clamp(+f.n.value || 0, 1, 3000); let a0 = clamp(+f.a0.value || 19, 19, 90), a1 = clamp(+f.a1.value || 90, 19, 90); if (a0 > a1) [a0, a1] = [a1, a0];
    state.fleet.drivers.push(...genDrivers(n, { depot: f.depot.value, ageMin: a0, ageMax: a1, maleRatio: +f.ratio.value }));
    const k = f.assign.checked ? autoAssign() : 0;
    saveFleet(); d.close(); toast(`${n}人を登録しました${k ? `（${k}人に担当車を割り当て）` : ''}`); admDrivers();
  };
}

/* ---- 運用表 ---- */
let blkDate = null;
function admBlocks() {
  blkDate ||= serviceNow(true).date;
  const box = $('#adm');
  const sd = simDay(blkDate);
  const rows = sd.byBlock.slice().sort((a, b) => a.block.depot.localeCompare(b.block.depot) || a.block.no - b.block.no);
  const evCount = (b, type) => b.sims.reduce((n, s) => n + s.events.filter((e) => e.type === type).length, 0);
  const totalAcc = rows.reduce((n, b) => n + evCount(b, 'accident'), 0), totalTr = rows.reduce((n, b) => n + evCount(b, 'trouble'), 0);
  const unassigned = rows.filter((b) => !b.vehicle).length;
  box.innerHTML = `<div class="row" style="margin-bottom:12px;align-items:flex-end"><label class="field" style="width:170px"><span>日付</span><input type="date" id="bDate" value="${blkDate}"></label>
    <p class="small muted grow" style="margin:0">運用は時刻表から自動で組み立てています（同じ停留所で折り返せる便をつなぐ方式）。車両は営業所ごとに日替わりで運用に入り、担当乗務員のうち1人が乗務します。遅延・トラブル・事故は日付ごとに決まった乱数で再現されます。</p></div>
    <div class="grid2" style="margin-bottom:14px">
      <div class="panel"><div class="small muted">運用数</div><div style="font-size:22px;font-weight:700">${rows.length}</div>${unassigned ? `<div class="small" style="color:var(--danger)">車両なし ${unassigned}運用</div>` : ''}</div>
      <div class="panel"><div class="small muted">事故による運転打ち切り</div><div style="font-size:22px;font-weight:700">${totalAcc}件</div></div>
      <div class="panel"><div class="small muted">乗客対応による遅れ</div><div style="font-size:22px;font-weight:700">${totalTr}件</div></div>
    </div>
    <div class="tablewrap"><table class="data"><thead><tr><th>運用</th><th>車番</th><th>乗務員</th><th>運転/接客</th><th>便数</th><th>始発〜最終</th><th>最大の遅れ</th><th>事象</th></tr></thead><tbody>${rows.map((b, i) => {
      const maxDelay = Math.max(0, ...b.sims.map((s) => Math.round((s.accident ? 0 : s.arr[s.trip.e] - s.trip.times[s.trip.e][0]))));
      const acc = evCount(b, 'accident'), tr = evCount(b, 'trouble');
      return `<tr data-i="${i}" style="cursor:pointer"><td><b>${esc(depotShort(b.block.depot))} ${b.block.no}</b></td><td>${b.vehicle ? esc(b.vehicle.no) : '<span style="color:var(--danger)">車両なし</span>'}</td><td>${b.driver ? esc(driverName(b.driver)) : '<span class="muted">担当者なし</span>'}</td><td>${b.driver ? `${b.driver.skill} / ${b.driver.service}` : '—'}</td><td class="num">${b.block.trips.length}</td><td>${fmt(b.block.trips[0].dep)}〜${fmt(b.block.trips[b.block.trips.length - 1].end)}</td><td class="num">${maxDelay ? maxDelay + '分' : '—'}</td><td>${acc ? '<span class="tag stop">事故</span> ' : ''}${tr ? `<span class="tag late">対応${tr}</span>` : ''}</td></tr>`;
    }).join('')}</tbody></table></div>`;
  $('#bDate').onchange = (e) => { if (e.target.value) { blkDate = e.target.value; admBlocks(); } };
  $$('tr[data-i]', box).forEach((tr) => tr.onclick = () => showBlock(rows[+tr.dataset.i]));
}
function showBlock(b) {
  const body = `<p class="small muted" style="margin-top:0">${esc(depotName(b.block.depot))}　車番 ${b.vehicle ? esc(b.vehicle.no) : 'なし'}　乗務員 ${b.driver ? esc(driverName(b.driver)) + `（運転${b.driver.skill}・接客${b.driver.service}）` : 'なし'}</p>
    <div class="tablewrap"><table class="data"><thead><tr><th>系統</th><th>行先</th><th>予定発</th><th>実際の発</th><th>予定着</th><th>実際の着</th><th>できごと</th></tr></thead><tbody>${b.sims.map((s) => {
      const t = s.trip; const a = s.accident ? null : s.arr[t.e];
      return `<tr><td>${routeBadge(t.sys)}${t.temp ? ' <span class="tag temp">臨</span>' : ''}</td><td>${esc(tripDestName(t))}</td><td>${fmt(t.dep)}</td><td>${fmt(s.dep[t.s])}</td><td>${fmt(t.end)}</td><td>${a == null ? '<span class="tag stop">打ち切り</span>' : `${fmt(a)}${a - t.end >= 1 ? ` <span class="tag late">+${Math.round(a - t.end)}</span>` : ''}`}</td><td style="white-space:normal;min-width:200px">${s.substitute ? '予備車で代走　' : ''}${s.events.filter((e) => e.type !== 'jam').map((e) => esc(e.text)).join('<br>')}${s.events.some((e) => e.type === 'jam') ? `<span class="small muted">${s.events.filter((e) => e.type === 'jam').length}区間で混雑</span>` : ''}</td></tr>`;
    }).join('')}</tbody></table></div>`;
  modal(`運用 ${esc(depotShort(b.block.depot))} ${b.block.no}`, body, { wide: true });
}

/* ---- 臨時便 ---- */
function admTemps() {
  const box = $('#adm'); const today = serviceNow(true).date;
  const sysList = Object.values(G.sys).sort((a, b) => a.no.localeCompare(b.no, 'ja', { numeric: true }) || a.direction.localeCompare(b.direction));
  box.innerHTML = `<form class="panel stack" id="tf" autocomplete="off">
      <h2 style="font-size:17px">臨時便を追加</h2>
      <div class="grid2">
        <label class="field"><span>運行日</span><input type="date" name="date" value="${today}" required></label>
        <label class="field" style="grid-column:span 2;min-width:0"><span>系統</span><select name="sys">${sysList.map((s) => `<option value="${esc(s.id)}">${esc(s.no)}　${esc(stopName(s.origin))} → ${esc(sysLabel(s))}${s.via ? `（${esc(s.via)}）` : ''}</option>`).join('')}</select></label>
        <label class="field"><span>始発停留所</span><select name="from"></select></label>
        <label class="field"><span>終着停留所</span><select name="to"></select></label>
        <label class="field"><span>始発の発車時刻</span><input type="time" name="dep" value="10:00" required></label>
        <label class="field"><span>本数</span><input type="number" name="count" value="1" min="1" max="60"></label>
        <label class="field"><span>運行間隔（分）</span><input type="number" name="every" value="15" min="1" max="240"></label>
        <label class="field"><span>理由・備考</span><input type="text" name="note" placeholder="例：花火大会の観客輸送" maxlength="40"></label>
      </div>
      <p class="small muted" id="tfPrev" style="margin:0"></p>
      <div><button class="btn primary" type="submit">臨時便を追加する</button></div>
      <p class="note">各停留所の時刻は、系統の標準的な所要時間から自動で計算します。追加した臨時便は時刻表・乗換案内・走行位置に反映されます。</p>
    </form>
    <div id="tList" style="margin-top:14px"></div>`;
  const f = $('#tf');
  const fillStops = () => {
    const s = G.sys[f.sys.value];
    f.from.innerHTML = s.stops.slice(0, -1).map((x, i) => `<option value="${i}">${esc(stopName(x.stopId))}</option>`).join('');
    f.to.innerHTML = s.stops.map((x, i) => `<option value="${i}" ${i === s.n - 1 ? 'selected' : ''}>${esc(stopName(x.stopId))}</option>`).join('');
    prev();
  };
  const prev = () => {
    const s = G.sys[f.sys.value]; const a = +f.from.value, b = +f.to.value; const dep = parseHM(f.dep.value);
    if (b <= a) { $('#tfPrev').textContent = '終着停留所は始発停留所より後ろの停留所を選んでください。'; return; }
    const dur = s.stops[b].arr - s.stops[a].dep;
    $('#tfPrev').textContent = dep == null ? '' : `所要 約${dur}分（${fmt(dep)} 発 → ${fmt(dep + dur)} 着）${+f.count.value > 1 ? `、最終便 ${fmt(dep + (+f.count.value - 1) * +f.every.value)} 発` : ''}`;
  };
  f.sys.onchange = fillStops; f.from.onchange = f.to.onchange = f.dep.oninput = f.count.oninput = f.every.oninput = prev;
  fillStops();
  f.onsubmit = (e) => {
    e.preventDefault();
    const a = +f.from.value, b = +f.to.value; let dep = parseHM(f.dep.value);
    if (b <= a || dep == null || !f.date.value) { toast('入力内容を確認してください'); return; }
    if (dep < 180) dep += 1440;
    const n = clamp(+f.count.value || 1, 1, 60), ev = clamp(+f.every.value || 15, 1, 240);
    for (let k = 0; k < n; k++) state.temps.push({ id: uid('t'), sys: f.sys.value, date: f.date.value, dep: dep + k * ev, from: a, to: b, note: f.note.value.trim() });
    saveTemps(); toast(`臨時便を${n}本追加しました`); drawTemps();
  };
  drawTemps();
}
function drawTemps() {
  const today = serviceNow(true).date;
  const list = state.temps.slice().sort((a, b) => a.date.localeCompare(b.date) || a.dep - b.dep);
  const past = list.filter((t) => t.date < today).length;
  $('#tList').innerHTML = list.length ? `<div class="row" style="margin-bottom:8px;align-items:center"><span class="small muted grow">${list.length}本（過去の日付 ${past}本）</span>${past ? '<button class="btn sm" id="tPast">過去の臨時便を削除</button>' : ''}</div>
    <div class="tablewrap"><table class="data"><thead><tr><th>運行日</th><th>系統</th><th>区間</th><th>発車</th><th>到着</th><th>備考</th><th></th></tr></thead><tbody>${list.map((t) => {
      const s = G.sys[t.sys]; if (!s) return `<tr><td>${esc(t.date)}</td><td colspan="5" class="muted">系統が見つかりません（案内データが変わった可能性があります）</td><td><button class="btn sm danger" data-del="${esc(t.id)}">削除</button></td></tr>`;
      const tr = makeTempTrip(t);
      return `<tr style="${t.date < today ? 'opacity:.55' : ''}"><td>${dateJa(t.date)}</td><td>${routeBadge(s)}</td><td>${esc(stopName(s.stops[tr.s].stopId))} → ${esc(stopName(s.stops[tr.e].stopId))}</td><td>${fmt(tr.dep)}</td><td>${fmt(tr.end)}</td><td>${esc(t.note)}</td><td><button class="btn sm danger" data-del="${esc(t.id)}">削除</button></td></tr>`;
    }).join('')}</tbody></table></div>` : '<div class="panel empty">臨時便はまだありません。上のフォームから追加できます。</div>';
  $$('#tList [data-del]').forEach((b) => b.onclick = () => { state.temps = state.temps.filter((t) => t.id !== b.dataset.del); saveTemps(); toast('臨時便を削除しました'); drawTemps(); });
  const tp = $('#tPast'); if (tp) tp.onclick = () => { state.temps = state.temps.filter((t) => t.date >= today); saveTemps(); toast('過去の臨時便を削除しました'); drawTemps(); };
}

/* ---- 設定 ---- */
function admSettings() {
  const S = state.settings; const box = $('#adm');
  box.innerHTML = `
    <form class="panel stack" id="sf">
      <h2 style="font-size:17px">遅延の起こりやすさ</h2>
      <p class="small muted" style="margin:0">停留所間を1区間走るたびに、時間帯ごとの確率で所定より時間がかかります（運転技術3のときの値）。運転技術が高いほど起こりにくくなります。</p>
      <div class="tablewrap"><table class="data"><thead><tr><th>時間帯</th><th>時刻</th><th>区間ごとの発生率（%）</th><th>1回の遅れ（最大・分）</th></tr></thead><tbody>${S.bands.map((b, i) => `<tr><td>${esc(b.name)}</td><td>${fmt(b.from)}〜${b.to >= 1440 + 180 ? '終車' : fmt(b.to)}</td><td><input type="number" step="0.1" min="0" max="100" name="p${i}" value="${b.p}" style="width:110px"></td><td><input type="number" min="1" max="15" name="m${i}" value="${b.max}" style="width:90px"></td></tr>`).join('')}</tbody></table></div>
      <div class="grid2">
        <label class="field"><span>事故の発生率（区間ごと・%）</span><input type="number" step="0.001" min="0" max="5" name="acc" value="${S.accident}"></label>
        <label class="field"><span>乗客とのトラブル発生率（停留所ごと・%）</span><input type="number" step="0.01" min="0" max="20" name="tro" value="${S.trouble}"></label>
        <label class="field"><span>遅れを1分取り戻せる確率（%）</span><input type="number" step="1" min="0" max="100" name="rec" value="${S.recover}"></label>
        <label class="field"><span>折返しに必要な時間（分）</span><input type="number" min="0" max="30" name="turn" value="${S.turnaround}"></label>
      </div>
      <p class="note">運転技術1〜5で、遅延の発生率は ${F_DELAY.join('・')} 倍、事故の発生率は ${F_ACC.join('・')} 倍になります。接客態度1〜5で、トラブルの発生率は ${F_TROUBLE.join('・')} 倍になります。</p>
      <div class="row"><button class="btn primary" type="submit">設定を保存する</button><button class="btn" type="button" id="sfReset">初期値に戻す</button></div>
    </form>
    <form class="panel stack" id="pf" autocomplete="off">
      <h2 style="font-size:17px">パスワードの変更</h2>
      <div class="grid2"><label class="field"><span>新しいパスワード（数字8桁）</span><input type="password" name="p1" inputmode="numeric" maxlength="8" autocomplete="new-password"></label>
      <label class="field"><span>もう一度入力</span><input type="password" name="p2" inputmode="numeric" maxlength="8" autocomplete="new-password"></label></div>
      <div><button class="btn primary" type="submit">パスワードを変更する</button></div>
      <div id="pfOut"></div>
    </form>
    <div class="panel stack">
      <h2 style="font-size:17px">データの保存と公開</h2>
      <p class="small muted" style="margin:0">車両・乗務員・臨時便・設定は、このブラウザ内に保存されています。公開サイトの閲覧者にも同じデータを見せるには、「公開用 fleet.js を書き出す」で作ったファイルをリポジトリの fleet.js と置き換えてください。</p>
      <div class="row"><button class="btn" id="exJson">バックアップを書き出す（JSON）</button><button class="btn" id="imJson">バックアップを読み込む</button><button class="btn primary" id="exFleet">公開用 fleet.js を書き出す</button></div>
      <h3 style="font-size:15px;margin-top:8px">案内データ（路線・時刻表）</h3>
      <p class="small muted" style="margin:0">現在のデータ：${esc(G.D.project || '')}（${esc((G.D.generatedAt || '').slice(0, 10))} 作成、停留所 ${G.D.stops.length}・系統 ${G.D.systems.length}・便 ${G.D.trips.length}）${LS.get('guideOverride', null) ? '　<b>このブラウザで差し替え中</b>' : ''}</p>
      <div class="row"><button class="btn" id="imGuide">案内データを差し替える（JSON）</button>${LS.get('guideOverride', null) ? '<button class="btn" id="rsGuide">元の案内データに戻す</button>' : ''}</div>
      <h3 style="font-size:15px;margin-top:8px">初期化</h3>
      <div class="row"><button class="btn danger" id="rsAll">車両・乗務員・臨時便・設定をすべて初期状態に戻す</button></div>
    </div>`;
  const f = $('#sf');
  f.onsubmit = (e) => {
    e.preventDefault();
    S.bands = S.bands.map((b, i) => ({ ...b, p: clamp(+f['p' + i].value || 0, 0, 100), max: clamp(Math.round(+f['m' + i].value || 1), 1, 15) }));
    S.accident = clamp(+f.acc.value || 0, 0, 5); S.trouble = clamp(+f.tro.value || 0, 0, 20); S.recover = clamp(+f.rec.value || 0, 0, 100); S.turnaround = clamp(Math.round(+f.turn.value || 0), 0, 30);
    saveSettings(); toast('設定を保存しました');
  };
  $('#sfReset').onclick = () => { state.settings = JSON.parse(JSON.stringify(DEFAULT_SETTINGS)); saveSettings(); toast('設定を初期値に戻しました'); admSettings(); };
  $('#pf').onsubmit = (e) => {
    e.preventDefault(); const p = e.target;
    if (!/^\d{8}$/.test(p.p1.value)) { toast('パスワードは数字8桁にしてください'); return; }
    if (p.p1.value !== p.p2.value) { toast('2回の入力が一致しません'); return; }
    const hsh = pwHash(p.p1.value); LS.set('pwHash', hsh); p.reset();
    $('#pfOut').innerHTML = `<p class="small" style="margin:0">このブラウザでのパスワードを変更しました。公開サイトでも新しいパスワードにするには、config.js の <code>adminPasswordHash</code> を次の値に書き換えてください。</p><input type="text" readonly value="${hsh}" onclick="this.select()" style="font-family:monospace;font-size:12px">`;
  };
  const bundle = () => ({ format: 'ichika-fleet', version: 1, exportedAt: new Date().toISOString(), vehicles: state.fleet.vehicles, drivers: state.fleet.drivers, temps: state.temps, settings: state.settings });
  $('#exJson').onclick = () => download(`一花交通_事業者データ_${dateStr(new Date())}.json`, JSON.stringify(bundle(), null, 1));
  $('#exFleet').onclick = () => download('fleet.js', `/* 一花交通 事業者データ（公開用）。事業者用ページの「公開用 fleet.js を書き出す」で作成。 */\nwindow.FLEET_DATA = ${JSON.stringify(bundle())};\n`, 'text/javascript');
  $('#imJson').onclick = async () => {
    const txt = await readFile('.json,application/json'); if (!txt) return;
    try {
      const o = JSON.parse(txt); if (!Array.isArray(o.vehicles) || !Array.isArray(o.drivers)) throw new Error();
      if (!(await confirmBox(`車両 ${o.vehicles.length}台・乗務員 ${o.drivers.length}人・臨時便 ${(o.temps || []).length}本のデータで、いまのデータを置き換えます。`, '置き換える'))) return;
      state.fleet = { vehicles: o.vehicles, drivers: o.drivers }; state.temps = o.temps || []; if (o.settings) state.settings = Object.assign({}, DEFAULT_SETTINGS, o.settings);
      LS.set('fleet', state.fleet); LS.set('temps', state.temps); LS.set('settings', state.settings); bump(); toast('バックアップを読み込みました'); admSettings();
    } catch { toast('読み込めませんでした。このアプリで書き出したJSONを選んでください'); }
  };
  $('#imGuide').onclick = async () => {
    const txt = await readFile('.json,application/json'); if (!txt) return;
    try {
      const o = JSON.parse(txt); if (o.format !== 'busplan-guide' || !Array.isArray(o.trips)) throw new Error();
      if (!LS.set('guideOverride', o)) return;
      toast('案内データを差し替えました。再読み込みします'); setTimeout(() => location.reload(), 800);
    } catch { toast('読み込めませんでした。busplan-guide 形式の案内用データを選んでください'); }
  };
  const rg = $('#rsGuide'); if (rg) rg.onclick = () => { LS.del('guideOverride'); location.reload(); };
  $('#rsAll').onclick = async () => {
    if (!(await confirmBox('このブラウザに保存した車両・乗務員・臨時便・設定・変更したパスワードをすべて消して、初期状態に戻します。', '初期状態に戻す'))) return;
    ['fleet', 'temps', 'settings', 'pwHash'].forEach(LS.del); location.reload();
  };
}

/* ================= router & boot ================= */
function route() {
  cleanupFns.forEach((f) => f()); cleanupFns = [];
  $$('dialog').forEach((d) => d.close());
  const parts = location.hash.replace(/^#\/?/, '').split('/').filter(Boolean);
  const name = parts[0] || 'timetable';
  $$('#nav a').forEach((a) => { if (a.dataset.r === name) a.setAttribute('aria-current', 'page'); else a.removeAttribute('aria-current'); });
  const v = { timetable: viewTimetable, search: viewSearch, live: viewLive, admin: viewAdmin }[name] || viewTimetable;
  v(parts.slice(1));
  window.scrollTo(0, 0);
}
function boot() {
  const override = LS.get('guideOverride', null);
  const D = override || window.BUS_GUIDE_DATA;
  if (!D || !Array.isArray(D.trips)) { app().innerHTML = '<div class="panel empty">案内データ（data.js）を読み込めませんでした。</div>'; return; }
  buildIndex(D);
  if (D.project) { CFG.companyName = D.project; $('#brandName').textContent = D.project; document.title = `${D.project} バス案内`; $('.disc').textContent = D.project.slice(0, 1); }
  loadFleet();
  window.addEventListener('hashchange', route);
  route();
}
boot();
