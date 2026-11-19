/* Site Safety VMS: playback of the analysed CCTV clip with every overlay and chart driven by video.currentTime. */
(() => {
  'use strict';
  const $ = (s) => document.querySelector(s);
  const FPS = 25, W0 = 1920, H0 = 1080;
  const ZORDER = ['pipe_stack', 'booths', 'gas_station', 'walkway', 'service', 'fab_floor', 'far_bay', 'other'];
  const ZSHOW = ['fab_floor', 'walkway', 'gas_station', 'booths', 'service', 'pipe_stack', 'far_bay'];
  const HSN = ['OK', 'UNVERIFIED', 'ALERT'];
  const POST = [null, 'upright', 'bent', 'crouched', 'lying'];
  const COLN = [null, 'orange', 'blue', 'white', 'yellow', 'red', 'green', 'dark'];
  const SWATCH = { orange: '#F07A2E', blue: '#3F8CE8', white: '#ECEFF4', yellow: '#F2C230', red: '#E04848', green: '#2EB872', dark: '#4A4F5C' };
  const EVC = { awkward_posture: '--serious', gathering: '--aqua', clutter_increase: '--warn', helmet_alert: '--crit', exclusion_breach: '--crit', running: '--warn', person_down: '--crit' };

  const S = { layers: { boxes: true, labels: true, trails: true, zones: true, heat: false, cables: true, groups: true }, sel: null, filter: 'all', lastUi: 0, lastT: -1, dragging: false };
  const video = $('#video'), ov = $('#ov'), octx = ov.getContext('2d');
  let C = {};

  // ------------------------------------------------------------------ utils
  const css = (v) => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
  function readColors() {
    ['--ok', '--crit', '--neutral', '--faint', '--aqua', '--warn', '--serious', '--mage', '--blue', '--am', '--text', '--muted', '--dim', '--line', '--line2', '--card', '--card2', '--bg', '--brand', '--body']
      .forEach((k) => (C[k.slice(2)] = css(k)));
  }
  const pad = (n) => String(n).padStart(2, '0');
  const clockAt = (t) => { const s = 7 * 3600 + 17 * 60 + 52.6 + t; return `${pad(Math.floor(s / 3600))}:${pad(Math.floor(s % 3600 / 60))}:${pad(Math.floor(s % 60))}`; };
  const mmss = (t) => `${pad(Math.floor(t / 60))}:${pad(Math.floor(t % 60))}`;
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
  function fitCanvas(cv) {
    const r = cv.getBoundingClientRect(), d = window.devicePixelRatio || 1;
    const w = Math.max(10, Math.round(r.width)), h = Math.max(10, Math.round(r.height));
    if (cv.width !== Math.round(w * d) || cv.height !== Math.round(h * d)) { cv.width = Math.round(w * d); cv.height = Math.round(h * d); }
    const ctx = cv.getContext('2d'); ctx.setTransform(d, 0, 0, d, 0, 0);
    return { ctx, w, h, d };
  }
  function rgba(hex, a) {
    const h = hex.replace('#', ''); const n = parseInt(h.length === 3 ? h.split('').map((c) => c + c).join('') : h, 16);
    return `rgba(${(n >> 16) & 255},${(n >> 8) & 255},${n & 255},${a})`;
  }

  // ------------------------------------------------------------------ data
  let META, FR, TL, EV, TR, GEAR, GROUPS = new Map(), CUM = {}, NSEC = 0;
  // per-worker gear: hat from the hard-hat check, coverall/tape/boots from the gear pass
  function gearOf(id, st) {
    const g = (TR[id] || {}).gear || {};
    return [
      ['Hat', st === 'ok' ? 'y' : st === 'alert' ? 'x' : 'q'],
      ['Coverall', g.coverall ? 'y' : 'q'],
      ['Tape', g.tape === 'seen' ? 'y' : g.tape === 'not seen' ? 'n' : 'q'],
      ['Boots', g.boots === 'seen' ? 'y' : 'q'],
    ];
  }
  const GMARK = { y: '✓', q: '?', n: '–', x: '✕' };
  async function load() {
    const get = (p) => fetch(p).then((r) => { if (!r.ok) throw new Error(p + ' ' + r.status); return r.json(); });
    [META, FR, TL, EV, TR, GEAR] = await Promise.all([get('data/meta.json'), get('data/frames.json'), get('data/timeline.json'), get('data/events.json'), get('data/tracks.json?v=2'), get('data/gear.json?v=2')]);
    FR.groups.forEach(([f, gs]) => GROUPS.set(f, gs));
    // timeline columns -> arrays + prefix sums
    const cols = TL.cols; const idx = Object.fromEntries(cols.map((c, i) => [c, i]));
    TL.get = (s, c) => TL.rows[clamp(s, 0, TL.rows.length - 1)][idx[c]];
    NSEC = TL.rows.length;
    ['assess_ok', 'assess_alert', 'assess_unverified', 'people', ...ZORDER.map((z) => 'z_' + z)].forEach((c) => {
      const a = new Float64Array(NSEC + 1); for (let i = 0; i < NSEC; i++) a[i + 1] = a[i] + (TL.rows[i][idx[c]] || 0); CUM[c] = a;
    });
    init();
  }

  // records at time t (interpolated between the 12.5 Hz samples)
  function recsAt(t) {
    const fi = t * FPS / 2; const i = clamp(Math.floor(fi), 0, FR.frames.length - 1); const a = FR.frames[i] || [];
    const b = FR.frames[i + 1]; const al = fi - i;
    if (!b || al <= 0) return a;
    const mb = new Map(b.map((r) => [r[0], r]));
    return a.map((r) => { const q = mb.get(r[0]); if (!q) return r; const o = r.slice(); for (let k = 1; k <= 4; k++) o[k] = r[k] + (q[k] - r[k]) * al; return o; });
  }
  const frameIndex = (t) => clamp(Math.round(t * FPS / 2), 0, FR.frames.length - 1);

  // ------------------------------------------------------------------ overlay
  const zonePaths = {};
  function heatColor(v) { // single-hue orange ramp, light -> dark
    const st = [[255, 214, 153, 0.0], [255, 176, 74, 0.45], [232, 96, 28, 0.7], [156, 42, 6, 0.85]];
    const x = clamp(v, 0, 1) * (st.length - 1); const i = Math.min(st.length - 2, Math.floor(x)); const f = x - i;
    return st[i].map((c, k) => c + (st[i + 1][k] - c) * f);
  }
  const HG = { w: 96, h: 54, grid: new Float32Array(96 * 54), upto: -1, cv: document.createElement('canvas') };
  HG.cv.width = HG.w; HG.cv.height = HG.h;
  function heatUpdate(fi) {
    if (fi < HG.upto) { HG.grid.fill(0); HG.upto = -1; }
    for (let i = HG.upto + 1; i <= fi; i++) {
      for (const r of FR.frames[i]) {
        const fx = (r[1] + r[3]) / 2, fy = r[4];
        const gx = clamp(Math.floor(fx / W0 * HG.w), 0, HG.w - 1), gy = clamp(Math.floor(fy / H0 * HG.h), 0, HG.h - 1);
        HG.grid[gy * HG.w + gx] += 0.08;
      }
    }
    if (fi !== HG.upto) {
      HG.upto = fi;
      let mx = 0; for (const v of HG.grid) mx = Math.max(mx, v);
      const ctx = HG.cv.getContext('2d'); const img = ctx.createImageData(HG.w, HG.h);
      for (let k = 0; k < HG.grid.length; k++) {
        const v = HG.grid[k]; if (!v) continue; const [r, g, b, a] = heatColor(Math.sqrt(v / (mx || 1)));
        img.data[k * 4] = r; img.data[k * 4 + 1] = g; img.data[k * 4 + 2] = b; img.data[k * 4 + 3] = a * 255;
      }
      ctx.putImageData(img, 0, 0);
    }
  }

  const MASKS = new Map(); const tmp = document.createElement('canvas');
  function maskFor(k) {
    if (MASKS.has(k)) return MASKS.get(k);
    MASKS.set(k, null);
    const im = new Image(); im.src = `data/masks/mask_${String(k * 10).padStart(4, '0')}.png`;
    im.onload = () => {
      const c = document.createElement('canvas'); c.width = im.width; c.height = im.height; const x = c.getContext('2d');
      x.drawImage(im, 0, 0); const d = x.getImageData(0, 0, c.width, c.height);
      for (let i = 0; i < d.data.length; i += 4) { const on = d.data[i] > 0; d.data[i] = 224; d.data[i + 1] = 85; d.data[i + 2] = 154; d.data[i + 3] = on ? 200 : 0; }
      x.putImageData(d, 0, 0); MASKS.set(k, c); S.lastT = -1;
    };
    return null;
  }

  function statusOf(r) {
    const h = r[4] - r[2];
    if (r[7] === 0) return 'nogo';
    if (r[5] === 2) return 'alert';
    if (r[6] === 1 && r[5] === 0) return 'ok';
    if (r[6] === 1) return 'unv';
    return 'far';
  }
  const SC = { ok: '--ok', alert: '--crit', nogo: '--crit', unv: '--neutral', far: '--dim' };
  const STXT = { ok: '✓ hard hat', alert: '✕ no hard hat', nogo: '✕ no-go zone', unv: '? hat not visible', far: 'far' };

  function drawOverlay(t) {
    const { ctx, w, h } = fitCanvas(ov); const k = w / W0;
    ctx.clearRect(0, 0, w, h);
    const fi = frameIndex(t); const recs = recsAt(t); const s = Math.floor(t); const narrow = w < 700;
    $('#stage-hint').hidden = narrow;
    // zones
    if (S.layers.zones) {
      const Z = META.zones;
      const poly = (p) => { ctx.beginPath(); p.forEach(([x, y], i) => (i ? ctx.lineTo(x * k, y * k) : ctx.moveTo(x * k, y * k))); ctx.closePath(); };
      ctx.save(); poly(Z.pipe_stack.poly); ctx.clip();
      ctx.strokeStyle = rgba(C.crit, .28); ctx.lineWidth = 3;
      for (let x = -h; x < w; x += 16) { ctx.beginPath(); ctx.moveTo(x, h); ctx.lineTo(x + h, 0); ctx.stroke(); }
      ctx.restore();
      ctx.setLineDash([]); ctx.lineWidth = 1.5;
      [['pipe_stack', C.crit, .9], ['booths', C.warn, .75], ['gas_station', C.blue, .7], ['walkway', C.text, .25]].forEach(([z, c, a]) => { poly(Z[z].poly); ctx.strokeStyle = rgba(c, a); ctx.stroke(); });
      ctx.font = `600 ${Math.max(9, 11 * k * 1.33)}px InterV, Inter, sans-serif`;
      if (!narrow) [['NO-GO · PIPE STACK', 1590, 760, C.crit], ['WELDING BOOTHS', 1530, 165, C.warn], ['GAS & WELDING SETS', 760, 300, C.blue]].forEach(([txt, x, y, c]) => {
        const tw = ctx.measureText(txt).width; ctx.fillStyle = 'rgba(10,14,26,.65)'; ctx.fillRect(x * k - 4, y * k - 12, tw + 8, 16); ctx.fillStyle = c; ctx.fillText(txt, x * k, y * k);
      });
    }
    // heat
    if (S.layers.heat) { heatUpdate(fi); ctx.save(); ctx.globalAlpha = .8; ctx.imageSmoothingEnabled = true; ctx.drawImage(HG.cv, 0, 0, w, h); ctx.restore(); }
    // cables
    const ci = TL.get(s, 'clutter_index') || 0;
    if (S.layers.cables && ci >= 0.008) {
      const m = maskFor(Math.floor(t / 10));
      if (m) {
        tmp.width = Math.round(w); tmp.height = Math.round(h); const x = tmp.getContext('2d');
        x.clearRect(0, 0, w, h); x.drawImage(m, 0, 0, w, h);
        for (const r of recs) x.clearRect(r[1] * k - 4, r[2] * k - 4, (r[3] - r[1]) * k + 8, (r[4] - r[2]) * k + 10);
        ctx.drawImage(tmp, 0, 0);
        const txt = `⚠ Trip hazard · cables/hose on walkway ${(ci * 100).toFixed(1)}%`;
        ctx.font = `600 ${Math.max(10, 12 * k * 1.33)}px InterV, Inter, sans-serif`;
        const tw = ctx.measureText(txt).width, bx = Math.max(8, Math.min(870 * k, w - tw - 16)), by = 990 * k;
        ctx.fillStyle = 'rgba(10,14,26,.78)'; roundRect(ctx, bx - 8, by - 15, tw + 16, 22, 5); ctx.fill();
        ctx.strokeStyle = C.warn; ctx.lineWidth = 1; ctx.stroke(); ctx.fillStyle = '#F3F5FA'; ctx.fillText(txt, bx, by);
      }
    }
    // groups
    let gNow = null;
    if (S.layers.groups) {
      const f2 = fi * 2; let gs = null;
      for (let d = 0; d <= 8 && !gs; d += 2) gs = GROUPS.get(f2 - d) || GROUPS.get(f2 + d);
      const byId = new Map(recs.map((r) => [r[0], r]));
      (gs || []).forEach((g) => {
        const bx = g.map((id) => byId.get(id)).filter(Boolean); if (bx.length < 4) return;
        const x0 = Math.min(...bx.map((r) => r[1])) * k - 10, y0 = Math.min(...bx.map((r) => r[2])) * k - 26, x1 = Math.max(...bx.map((r) => r[3])) * k + 10, y1 = Math.max(...bx.map((r) => r[4])) * k + 8;
        ctx.setLineDash([9, 6]); ctx.strokeStyle = C.aqua; ctx.lineWidth = 2; ctx.strokeRect(x0, y0, x1 - x0, y1 - y0); ctx.setLineDash([]);
        const ev = EV.find((e) => e.kind === 'gathering' && e.f0 <= f2 && f2 <= e.f1 + 10);
        const dur = ev ? (f2 - ev.f0) / FPS : 0; gNow = { n: bx.length, dur };
        const txt = `TOOLBOX TALK · ${bx.length} people${ev ? ' · ' + Math.floor(dur / 60) + ':' + pad(Math.floor(dur % 60)) : ''}`;
        ctx.font = `700 ${Math.max(10, 11.5 * k * 1.33)}px InterV, Inter, sans-serif`; const tw = ctx.measureText(txt).width;
        ctx.fillStyle = C.aqua; roundRect(ctx, x0, y0 - 20, tw + 14, 19, 4); ctx.fill(); ctx.fillStyle = '#fff'; ctx.fillText(txt, x0 + 7, y0 - 6);
      });
    }
    S.gNow = gNow;
    // selected track path
    if (S.sel && S.selPath) {
      ctx.lineWidth = 2; ctx.strokeStyle = rgba(C.brand, .35); ctx.beginPath();
      S.selPath.forEach(([i, x, y], j) => (j ? ctx.lineTo(x * k, y * k) : ctx.moveTo(x * k, y * k))); ctx.stroke();
      ctx.strokeStyle = C.brand; ctx.lineWidth = 2.5; ctx.beginPath(); let started = false;
      for (const [i, x, y] of S.selPath) { if (i > fi) break; started ? ctx.lineTo(x * k, y * k) : ctx.moveTo(x * k, y * k); started = true; } ctx.stroke();
    }
    // people
    const placed = [];
    const sorted = recs.slice().sort((a, b) => b[4] - a[4]);
    for (const r of sorted) {
      const st = statusOf(r); const col = C[SC[st].slice(2)];
      const x1 = r[1] * k, y1 = r[2] * k, x2 = r[3] * k, y2 = r[4] * k, bh = y2 - y1, bw = x2 - x1;
      const isSel = S.sel === r[0];
      if (S.layers.trails) {
        ctx.lineWidth = 2; let prev = null;
        for (let j = Math.max(0, fi - 24); j <= fi; j++) {
          const q = FR.frames[j].find((z) => z[0] === r[0]); if (!q) { prev = null; continue; }
          const p = [(q[1] + q[3]) / 2 * k, q[4] * k];
          if (prev) { ctx.strokeStyle = rgba(col, .15 + .6 * (j - fi + 24) / 24); ctx.beginPath(); ctx.moveTo(prev[0], prev[1]); ctx.lineTo(p[0], p[1]); ctx.stroke(); }
          prev = p;
        }
      }
      if (S.layers.boxes) {
        const L = clamp(.2 * Math.min(bh, bw), 5, 16), lw = isSel ? 3 : (bh > 50 ? 2 : 1.2);
        ctx.strokeStyle = isSel ? C.brand : col; ctx.lineWidth = lw;
        if (isSel) { ctx.shadowColor = C.brand; ctx.shadowBlur = 12; }
        [[x1, y1, 1, 1], [x2, y1, -1, 1], [x1, y2, 1, -1], [x2, y2, -1, -1]].forEach(([cx, cy, sx, sy]) => {
          ctx.beginPath(); ctx.moveTo(cx + sx * L, cy); ctx.lineTo(cx, cy); ctx.lineTo(cx, cy + sy * L); ctx.stroke();
        });
        ctx.shadowBlur = 0;
        ctx.strokeStyle = rgba(isSel ? C.brand : col, .28); ctx.lineWidth = 1; ctx.strokeRect(x1, y1, bw, bh);
      }
      if (S.layers.labels && bh > (narrow ? 34 : 22)) {
        const small = bh < 60 || narrow;
        const post = r[8] === 2 || r[8] === 3 ? POST[r[8]] : null;
        let txt = small ? `${r[0]}` : `ID ${r[0]}  ${STXT[st]}${post ? ' · ' + post : ''}`;
        ctx.font = `600 ${narrow ? 9 : small ? 10 : 11.5}px InterV, Inter, sans-serif`;
        if (narrow) txt = `${st === 'ok' ? '✓' : st === 'unv' ? '?' : st === 'far' ? '' : '✕'}${r[0]}`;
        let tw = ctx.measureText(txt).width; let lh = small ? 15 : 18; let ly = y1 - lh - 2;
        const hit = (a) => placed.some((b) => !(a[2] < b[0] || a[0] > b[2] || a[3] < b[1] || a[1] > b[3]));
        let rect = [x1, ly, x1 + tw + 12, ly + lh];
        if (hit(rect)) {
          txt = `${st === 'ok' ? '✓' : st === 'unv' ? '?' : st === 'far' ? '' : '✕'} ${r[0]}`.trim(); ctx.font = '600 10px InterV, Inter, sans-serif'; tw = ctx.measureText(txt).width; lh = 15;
          for (const dy of [0, 17, 34, 51]) { rect = [x1, y1 - lh - 2 - dy, x1 + tw + 12, y1 - 2 - dy]; if (!hit(rect)) break; }
          ly = rect[1];
        }
        if (!small && !narrow && bh > 150 && rect[1] === y1 - lh - 2 && (st === 'ok' || st === 'unv')) {
          const gl = gearOf(r[0], st).slice(1); const t2 = gl.map(([n, v]) => `${GMARK[v]} ${n.toLowerCase()}`).join('  ');
          ctx.font = '600 10.5px InterV, Inter, sans-serif'; const tw2 = ctx.measureText(t2).width; const r2 = [x1, rect[1] - 16, x1 + tw2 + 12, rect[1] - 1];
          if (!hit(r2)) { placed.push(r2); ctx.fillStyle = 'rgba(10,14,26,.72)'; roundRect(ctx, r2[0], r2[1], r2[2] - r2[0], 15, 4); ctx.fill(); ctx.fillStyle = '#DDE4F2'; ctx.fillText(t2, r2[0] + 6, r2[1] + 11); }
          ctx.font = `600 ${narrow ? 9 : small ? 10 : 11.5}px InterV, Inter, sans-serif`;
        }
        placed.push(rect);
        ctx.fillStyle = 'rgba(10,14,26,.78)'; roundRect(ctx, rect[0], rect[1], rect[2] - rect[0], lh, 4); ctx.fill();
        ctx.fillStyle = isSel ? C.brand : col; ctx.fillRect(rect[0], rect[1], 3, lh);
        ctx.fillStyle = '#F3F5FA'; ctx.fillText(txt, rect[0] + 7, rect[1] + lh - 4.5);
      }
    }
    // extinguisher
    const eb = META.assets.fire_extinguisher.box; const ev = extAt(fi * 2);
    ctx.strokeStyle = ev >= .5 ? C.ok : C.warn; ctx.lineWidth = 1.5; ctx.strokeRect(eb[0] * k - 3, eb[1] * k - 3, (eb[2] - eb[0]) * k + 6, (eb[3] - eb[1]) * k + 6);
    return recs;
  }
  function roundRect(ctx, x, y, w, h, r) { ctx.beginPath(); ctx.moveTo(x + r, y); ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r); ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath(); }
  function extAt(f) { const e = FR.ext; let lo = 0, hi = e.length - 1; while (lo < hi) { const m = (lo + hi + 1) >> 1; if (e[m][0] <= f) lo = m; else hi = m - 1; } return e[lo] ? e[lo][1] : 1; }

  // ------------------------------------------------------------------ charts (static layer + playhead)
  const CH = {};
  function chart(id, drawStatic, opts = {}) {
    const cv = $(id); const st = document.createElement('canvas');
    CH[id] = { cv, st, drawStatic, opts, dims: null };
    const tip = cv.parentElement.querySelector('.tip');
    if (opts.seek) {
      const toT = (ev) => { const r = cv.getBoundingClientRect(); const m = CH[id].dims; const x = ev.clientX - r.left; return clamp((x - m.l) / (r.width - m.l - m.r), 0, 1) * durOf(); };
      cv.addEventListener('pointerdown', (ev) => { cv.setPointerCapture(ev.pointerId); S.dragging = true; seek(toT(ev), true); });
      cv.addEventListener('pointermove', (ev) => {
        const t = toT(ev); if (S.dragging && ev.buttons) seek(t, true);
        if (tip && opts.tip) { tip.hidden = false; tip.textContent = opts.tip(t); const r = cv.getBoundingClientRect(); tip.style.left = clamp(ev.clientX - r.left + 10, 0, r.width - tip.offsetWidth) + 'px'; tip.style.top = (opts.tipTop ?? -30) + 'px'; }
      });
      cv.addEventListener('pointerup', (ev) => { S.dragging = false; seek(toT(ev), false); });
      cv.addEventListener('pointerleave', () => { if (tip) tip.hidden = true; });
    }
  }
  function renderStatic(id) {
    const c = CH[id]; const { w, h, d } = fitCanvas(c.cv);
    c.st.width = c.cv.width; c.st.height = c.cv.height; const x = c.st.getContext('2d'); x.setTransform(d, 0, 0, d, 0, 0);
    c.dims = c.drawStatic(x, w, h); c.wh = [w, h];
  }
  function renderDyn(id, t) {
    const c = CH[id]; if (!c.dims) return; const ctx = c.cv.getContext('2d'); const d = window.devicePixelRatio || 1; const [w, h] = c.wh; const m = c.dims;
    ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.clearRect(0, 0, c.cv.width, c.cv.height); ctx.drawImage(c.st, 0, 0); ctx.setTransform(d, 0, 0, d, 0, 0);
    const X = m.l + (w - m.l - m.r) * (t / durOf());
    ctx.fillStyle = rgba(C.card.startsWith('#') ? C.card : '#131B31', .62); ctx.fillRect(X, m.t, w - m.r - X, h - m.t - m.b);
    ctx.strokeStyle = C.text; ctx.lineWidth = 1.5; ctx.beginPath(); ctx.moveTo(X, m.t - 2); ctx.lineTo(X, h - m.b + 2); ctx.stroke();
    if (c.opts.knob) { ctx.fillStyle = C.brand; ctx.beginPath(); ctx.arc(X, m.t + 2, 5, 0, 7); ctx.fill(); }
  }
  function axesTime(x, w, h, m) {
    x.font = '11px InterV, Inter, sans-serif'; x.fillStyle = C.muted; x.textAlign = 'center';
    const span = w - m.l - m.r; const step = span < 360 ? 120 : 60;
    for (let s = 8; s < NSEC; s += step) { const X = m.l + span * s / NSEC; x.fillText(clockAt(s).slice(0, 5), X, h - m.b + 14); x.strokeStyle = rgba(C.muted, .12); x.beginPath(); x.moveTo(X, m.t); x.lineTo(X, h - m.b); x.stroke(); }
    x.textAlign = 'left';
  }
  function drawPeople(x, w, h) {
    const m = { l: 30, r: 8, t: 8, b: 20 }; const rows = TL.rows; const g = (i, c) => TL.get(i, c);
    const mx = Math.max(4, ...rows.map((_, i) => g(i, 'people'))); const top = Math.ceil(mx / 4) * 4;
    const X = (s) => m.l + (w - m.l - m.r) * s / NSEC, Y = (v) => h - m.b - (h - m.t - m.b) * v / top;
    x.font = '11px InterV, Inter, sans-serif'; x.fillStyle = C.muted; x.textAlign = 'right';
    for (let v = 0; v <= top; v += top / 4) { x.fillText(String(v), m.l - 6, Y(v) + 4); x.strokeStyle = rgba(C.muted, .12); x.beginPath(); x.moveTo(m.l, Y(v)); x.lineTo(w - m.r, Y(v)); x.stroke(); }
    x.textAlign = 'left';
    EV.filter((e) => e.kind === 'gathering').forEach((e) => { x.fillStyle = rgba(C.aqua, .14); x.fillRect(X(e.f0 / FPS), m.t, X(e.f1 / FPS) - X(e.f0 / FPS), h - m.t - m.b); });
    const layers = [['assess_ok', C.ok], ['assess_alert', C.crit], ['assess_unverified', C.neutral]];
    let base = new Float64Array(NSEC);
    layers.forEach(([c, col]) => {
      x.beginPath(); for (let i = 0; i < NSEC; i++) x.lineTo(X(i), Y(base[i] + g(i, c))); for (let i = NSEC - 1; i >= 0; i--) x.lineTo(X(i), Y(base[i]));
      x.closePath(); x.fillStyle = rgba(col, .85); x.fill(); for (let i = 0; i < NSEC; i++) base[i] += g(i, c);
    });
    x.beginPath(); for (let i = 0; i < NSEC; i++) x.lineTo(X(i), Y(Math.max(base[i], g(i, 'people')))); for (let i = NSEC - 1; i >= 0; i--) x.lineTo(X(i), Y(base[i]));
    x.closePath(); x.fillStyle = rgba(C.faint, .9); x.fill();
    axesTime(x, w, h, m); return m;
  }
  function drawClutter(x, w, h) {
    const m = { l: 34, r: 10, t: 10, b: 20 }; const v = TL.rows.map((_, i) => 100 * (TL.get(i, 'clutter_index') || 0));
    const top = Math.max(2, Math.ceil(Math.max(...v)));
    const X = (s) => m.l + (w - m.l - m.r) * s / NSEC, Y = (q) => h - m.b - (h - m.t - m.b) * q / top;
    x.font = '11px InterV, Inter, sans-serif'; x.fillStyle = C.muted; x.textAlign = 'right';
    for (let q = 0; q <= top; q += Math.max(1, Math.round(top / 3))) { x.fillText(q + '%', m.l - 6, Y(q) + 4); x.strokeStyle = rgba(C.muted, .12); x.beginPath(); x.moveTo(m.l, Y(q)); x.lineTo(w - m.r, Y(q)); x.stroke(); }
    x.textAlign = 'left';
    x.beginPath(); v.forEach((q, i) => x.lineTo(X(i), Y(q))); x.lineTo(X(NSEC - 1), Y(0)); x.lineTo(X(0), Y(0)); x.closePath(); x.fillStyle = rgba(C.warn, .2); x.fill();
    x.beginPath(); v.forEach((q, i) => (i ? x.lineTo(X(i), Y(q)) : x.moveTo(X(i), Y(q)))); x.strokeStyle = C.warn; x.lineWidth = 2; x.stroke();
    axesTime(x, w, h, m); return m;
  }
  function drawScrub(x, w, h) {
    const m = { l: 6, r: 6, t: 8, b: 18 }; const X = (s) => m.l + (w - m.l - m.r) * s / NSEC;
    x.fillStyle = C.card2; roundRect(x, m.l, m.t, w - m.l - m.r, h - m.t - m.b, 6); x.fill();
    const mx = Math.max(...TL.rows.map((_, i) => TL.get(i, 'people')));
    x.beginPath(); for (let i = 0; i < NSEC; i++) x.lineTo(X(i), h - m.b - (h - m.t - m.b - 14) * TL.get(i, 'people') / mx); x.lineTo(X(NSEC - 1), h - m.b); x.lineTo(X(0), h - m.b); x.closePath();
    x.fillStyle = rgba(C.blue, .35); x.fill();
    EV.forEach((e) => { x.fillStyle = css(EVC[e.kind] || '--warn'); const a = X(e.f0 / FPS), b = Math.max(a + 3, X(e.f1 / FPS)); roundRect(x, a, m.t + 2, b - a, 7, 2); x.fill(); });
    x.font = '10.5px InterV, Inter, sans-serif'; x.fillStyle = C.muted; x.textAlign = 'center';
    for (let s = 8; s < NSEC; s += (w < 560 ? 120 : 60)) { const lab = clockAt(s).slice(0, 5); const tw = x.measureText(lab).width; if (X(s) - tw / 2 >= 0 && X(s) + tw / 2 <= w) x.fillText(lab, X(s), h - 4); }
    x.textAlign = 'left'; return m;
  }

  // ------------------------------------------------------------------ side panel
  function hbars(el, rows, max, unit) {
    if (!el._built) { el.innerHTML = rows.map((r) => `<div class="hb${r.crit ? ' crit' : ''}" data-k="${r.k}"><span class="n">${r.label}</span><span class="t"><b style="width:0"></b></span><span class="v">0</span></div>`).join(''); el._built = true; }
    rows.forEach((r) => {
      const row = el.querySelector(`[data-k="${r.k}"]`); row.classList.toggle('crit', !!r.crit && r.v > 0);
      row.querySelector('b').style.width = (max ? clamp(100 * r.v / max, 0, 100) : 0) + '%';
      row.querySelector('.v').textContent = unit === 'min' ? r.v.toFixed(1) : String(r.v);
    });
  }
  function updatePanels(t, recs) {
    const s = clamp(Math.floor(t), 0, NSEC - 1); const f = Math.round(t * FPS);
    $('#clock').textContent = clockAt(t); $('#tc-now').textContent = mmss(t);
    const near = recs.filter((r) => r[6] === 1).length;
    $('#k-people').textContent = recs.length; $('#k-people-s').textContent = `${near} close enough to check`;
    const ok = CUM.assess_ok[s + 1], al = CUM.assess_alert[s + 1];
    $('#k-comp').textContent = ok + al > 0.5 ? Math.round(100 * ok / (ok + al)) + '%' : '-';
    $('#k-comp-s').textContent = `of checked time · ${(ok / 60).toFixed(1)} person-min so far`;
    $('#k-alerts').textContent = EV.filter((e) => (e.kind === 'helmet_alert' || e.kind === 'exclusion_breach') && e.f0 <= f).length;
    const ci = 100 * (TL.get(s, 'clutter_index') || 0);
    $('#k-clutter').textContent = ci.toFixed(1) + '%'; $('#clutter-now').textContent = ci.toFixed(1) + '% now';
    $('#k-clutter-s').textContent = `of floor · ${(100 * (TL.get(0, 'clutter_index') || 0)).toFixed(1)}% at 07:18`;
    $('#k-clutter').style.color = ci >= 1 ? 'var(--warn)' : '';
    // group card
    const g = S.gNow; $('#group-card').hidden = !g;
    if (g) { $('#g-n').textContent = g.n; $('#g-dur').textContent = `${Math.floor(g.dur / 60)}:${pad(Math.floor(g.dur % 60))}`; }
    // PPE kit now (workers close enough to check)
    const nearR = recs.filter((r) => r[6] === 1 && r[7] !== 6);
    const kitRows = [['Hard hat', 0], ['Coverall', 1], ['Reflective tape', 2], ['Safety boots', 3]].map(([label, gi]) => {
      const c = { y: 0, q: 0, n: 0, x: 0 }; nearR.forEach((r) => { c[gearOf(r[0], statusOf(r))[gi][1]]++; }); return { label, c };
    });
    const kitEl = $('#kit-now');
    if (!kitEl._built) {
      const ICON = { 'Hard hat': '<path d="M4 15h16M5 15a7 7 0 0 1 14 0M12 8v-2"/>', Coverall: '<path d="M8 4h8l3 5-3 1v10H8V10L5 9z"/>', 'Reflective tape': '<path d="M8 4h8l3 5-3 1v10H8V10L5 9zM8 13h8M8 16h8"/>', 'Safety boots': '<path d="M7 4v10l-2 3v3h14v-2l-6-3V4z"/>' };
      kitEl.innerHTML = kitRows.map((k) => `<div class="kit-row" data-k="${k.label}"><svg viewBox="0 0 24 24">${ICON[k.label]}</svg><span>${k.label}</span><span class="v"></span><div class="bar"><b style="background:var(--ok);width:0"></b><b style="background:var(--warn);width:0"></b><b style="background:var(--crit);width:0"></b><b style="background:var(--faint);width:0"></b></div></div>`).join('');
      kitEl._built = true;
    }
    kitRows.forEach(({ label, c }) => {
      const row = kitEl.querySelector(`[data-k="${label}"]`); const n = nearR.length || 1; const b = row.querySelectorAll('b');
      [c.y, c.n, c.x, c.q].forEach((v, i) => (b[i].style.width = (100 * v / n) + '%'));
      row.querySelector('.v').textContent = nearR.length ? `${c.y} of ${nearR.length} seen${c.x ? ` · ${c.x} missing` : ''}${c.n ? ` · ${c.n} not seen` : ''}` : '-';
    });
    $('#kit-n').textContent = `${nearR.length} close enough to check`;
    // zones now
    const zc = {}; recs.forEach((r) => { const z = ZORDER[r[7]]; zc[z] = (zc[z] || 0) + 1; });
    hbars($('#zones-now'), ZSHOW.map((z) => ({ k: z, label: META.zone_labels[z], v: zc[z] || 0, crit: z === 'pipe_stack' })), 8, 'n');
    // zone time so far
    const zt = ZSHOW.map((z) => ({ k: z, label: META.zone_labels[z], v: CUM['z_' + z][s + 1] / 60, crit: z === 'pipe_stack' }));
    hbars($('#zone-time'), zt, Math.max(...ZSHOW.map((z) => CUM['z_' + z][NSEC] / 60)), 'min');
    // in view list: one stable row per worker (ordered by arrival), updated in place
    const ul = $('#inview'); S.rows = S.rows || new Map();
    if (Math.abs(t - (S.listT ?? t)) > 2) { S.rows.forEach((row) => row.li.remove()); S.rows.clear(); }
    S.listT = t;
    const present = new Map(recs.map((r) => [r[0], r]));
    present.forEach((r, id) => {
      let row = S.rows.get(id);
      if (!row) {
        const tr = TR[id] || {};
        const li = document.createElement('li'); li.addEventListener('click', () => select(id));
        const th = document.createElement('span'); th.className = 'th'; if (tr.crop) th.style.backgroundImage = `url(${tr.crop})`; else th.classList.add('none');
        const mid = document.createElement('div'); const nm = document.createElement('div'); nm.className = 'nm'; nm.textContent = `Worker ${id}`;
        const meta = document.createElement('div'); meta.className = 'meta'; mid.append(nm, meta);
        const chip = document.createElement('span'); li.append(th, mid, chip);
        row = { li, nm, meta, chip, sw: '', m: '', c: '' }; S.rows.set(id, row);
      }
      row.last = t;
      const hc = COLN[r[9]], sc = COLN[r[10]]; const swk = `${hc}|${sc}`;
      if (row.sw !== swk) {
        row.sw = swk; row.nm.querySelectorAll('.sw').forEach((e) => e.remove());
        if (hc) { const sw = document.createElement('i'); sw.className = 'sw round'; sw.style.background = SWATCH[hc]; sw.title = hc + ' hard hat'; row.nm.appendChild(sw); }
        if (sc) { const sw = document.createElement('i'); sw.className = 'sw'; sw.style.background = SWATCH[sc]; sw.title = sc + ' coverall'; row.nm.appendChild(sw); }
      }
      const m = META.zone_labels[ZORDER[r[7]]] + (POST[r[8]] && r[8] > 1 ? ' · ' + POST[r[8]] : '');
      if (row.m !== m) { row.m = m; row.meta.textContent = m; }
      const st = statusOf(r); const gl = gearOf(id, st); const c = st + gl.map((x) => x[1]).join('');
      if (row.c !== c) {
        row.c = c;
        if (st === 'far' || st === 'nogo') { row.chip.className = 'st ' + (st === 'far' ? 'far' : 'al'); row.chip.textContent = st === 'far' ? 'Too far' : '✕ No-go'; }
        else {
          row.chip.className = 'gear'; row.chip.replaceChildren();
          gl.forEach(([n, v]) => { const sp = document.createElement('span'); sp.className = v; sp.textContent = `${GMARK[v]} ${n}`; sp.title = { y: 'seen', q: 'not visible or unclear', n: 'not seen', x: 'missing' }[v]; row.chip.appendChild(sp); });
        }
      }
      row.li.classList.remove('gone'); row.li.classList.toggle('sel', S.sel === id);
    });
    S.rows.forEach((row, id) => {
      if (present.has(id)) return;
      if (Math.abs(t - row.last) > 1.5) { row.li.remove(); S.rows.delete(id); } else row.li.classList.add('gone');
    });
    const order = [...S.rows.keys()].sort((a, b) => ((TR[a] || {}).first ?? 0) - ((TR[b] || {}).first ?? 0) || a - b);
    order.forEach((id, k) => { const li = S.rows.get(id).li; if (ul.children[k] !== li) ul.insertBefore(li, ul.children[k] || null); });
    $('#inview-n').textContent = present.size;
    // events state
    document.querySelectorAll('#events li').forEach((li) => {
      const e = EV[+li.dataset.i]; li.classList.toggle('now', e.f0 <= f && f <= Math.max(e.f1, e.f0 + 3 * FPS)); li.classList.toggle('future', e.f0 > f);
    });
  }
  const PEAK = []; function peakSoFar(s) { if (!PEAK.length) { let m = 0; for (let i = 0; i < NSEC; i++) { m = Math.max(m, TL.get(i, 'people')); PEAK.push(m); } } return PEAK[s].toFixed(1).replace('.0', ''); }

  function buildEvents() {
    const ol = $('#events'); ol.replaceChildren();
    EV.forEach((e, i) => {
      if (S.filter !== 'all' && e.kind !== S.filter) return;
      const li = document.createElement('li'); li.dataset.i = i;
      const mk = document.createElement('i'); mk.className = 'mk'; mk.style.background = `var(${EVC[e.kind] || '--warn'})`;
      const tt = document.createElement('span'); tt.className = 't'; tt.textContent = clockAt(e.f0 / FPS);
      const body = document.createElement('div'); const w = document.createElement('div');
      const dur = (e.f1 - e.f0) / FPS;
      w.textContent = e.kind === 'gathering' ? `Toolbox talk · up to ${e.peak} people · ${(dur / 60).toFixed(1)} min+` : e.kind === 'awkward_posture' ? `Worker ${e.tid} bending or crouching · ${dur.toFixed(0)} s` : e.kind === 'clutter_increase' ? `Cables/hoses now cover ${Math.round(e.level * 100)}% of the walkway` : e.what;
      const dd = document.createElement('div'); dd.className = 'd';
      dd.textContent = e.kind === 'clutter_increase' ? (e.present.length ? `Workers on the walkway just before: ${e.present.slice(0, 6).join(', ')}` : '') : e.kind === 'gathering' ? 'Still going when the recording ends' : e.kind === 'awkward_posture' ? 'Handling cable at floor level' : '';
      body.append(w, dd); li.append(mk, tt, body);
      li.addEventListener('click', () => { seek(Math.max(0, e.f0 / FPS - 2), false); if (e.tid) select(e.tid); if (video.paused) play(); });
      ol.appendChild(li);
    });
  }

  // ------------------------------------------------------------------ selection
  function select(id) {
    S.sel = id; S.selDirty = true; S.lastIds = null;
    const tr = TR[id]; const card = $('#track-card');
    if (!id || !tr) { card.hidden = true; S.selPath = null; return; }
    S.selPath = []; for (let i = Math.floor(tr.first / 2); i <= Math.ceil(tr.last / 2) && i < FR.frames.length; i++) { const q = FR.frames[i].find((z) => z[0] === id); if (q) S.selPath.push([i, (q[1] + q[3]) / 2, q[4]]); }
    card.hidden = false; $('#tc-title').textContent = `Worker ${id}`;
    const img = $('#tc-img'); if (tr.crop) { img.src = tr.crop; img.hidden = false; } else img.hidden = true;
    const dl = document.createElement('dl');
    const pct = tr.checks ? Math.round(100 * tr.hat / tr.checks) + '%' : '-';
    const status = { ok: 'On', partial: 'Hat often hidden from camera', far: 'Too far to check', check: 'Check: possibly no hard hat' }[tr.status];
    [['First seen', clockAt(tr.first / FPS)], ['Last seen', clockAt(tr.last / FPS)], ['On camera', `${((tr.last - tr.first) / FPS).toFixed(0)} s`], ['Hard hat', status],
     ['Hat seen in', tr.checks ? `${pct} of checks` : '-'], ['Hard hat colour', tr.hc || '-'],
     ['Coverall', (tr.gear && tr.gear.coverall) ? `On (${tr.gear.coverall})` : (tr.sc ? `On (${tr.sc})` : 'Not clear')],
     ['Reflective tape', tr.gear ? ({ seen: 'Seen', 'not seen': 'Not seen', unclear: 'Unclear' })[tr.gear.tape] : '-'],
     ['Safety boots', tr.gear ? (tr.gear.boots === 'seen' ? 'Seen' : 'Feet not visible enough') : '-'],
     ['Gloves, glasses', 'Too small to check from this camera']]
      .forEach(([a, b]) => { const dt = document.createElement('dt'); dt.textContent = a; const dd = document.createElement('dd'); dd.textContent = b; dl.append(dt, dd); });
    $('#tc-meta').replaceChildren(dl);
    const zs = Object.entries(tr.zones).slice(0, 4); const zel = $('#tc-zones'); zel._built = false;
    hbars(zel, zs.map(([z, v]) => ({ k: z, label: META.zone_labels[z] || z, v: v, crit: z === 'pipe_stack' })), Math.max(...zs.map(([, v]) => v), 1), 'min');
    zel.querySelectorAll('.v').forEach((el, i) => (el.textContent = zs[i][1].toFixed(0) + ' s'));
    $('#stage-hint').style.opacity = 0;
  }

  // ------------------------------------------------------------------ transport
  function durOf() { return isFinite(video.duration) && video.duration > 0 ? video.duration : NSEC; }
  function seek(t, fast) {
    if (!isFinite(t)) return;
    t = clamp(t, 0, durOf() - 0.05);
    const now = performance.now();
    if (fast) {
      clearTimeout(S.seekTimer);
      if (now - (S.lastSeekAt || 0) < 120) { S.seekTimer = setTimeout(() => seek(t, true), 130); return; }
    }
    S.lastSeekAt = now; S.listT = undefined;
    try { if (fast && video.fastSeek) video.fastSeek(t); else video.currentTime = t; } catch (e) { /* not seekable yet */ }
    S.lastT = -1;
  }
  function play() { video.play().catch(() => {}); }
  function toggle() { video.paused ? play() : video.pause(); }
  function jumpEvent(dir) {
    const f = video.currentTime * FPS; const list = EV.filter((e) => S.filter === 'all' || e.kind === S.filter);
    const e = dir > 0 ? list.find((x) => x.f0 > f + FPS * 2.5) : [...list].reverse().find((x) => x.f0 < f - FPS * 2.5);
    if (e) { seek(Math.max(0, e.f0 / FPS - 2), false); if (e.tid) select(e.tid); }
  }

  // ------------------------------------------------------------------ method drawer
  function buildDrawer() {
    const b = $('#dr-body'); b.replaceChildren();
    const sm = META.summary; const f1 = (v) => (Math.round(v * 10) / 10).toString();
    const sec = (title, node) => { const d = document.createElement('section'); const h = document.createElement('h3'); h.textContent = title; d.appendChild(h); d.appendChild(node); return d; };
    const para = (t, cls) => { const e = document.createElement('p'); e.textContent = t; if (cls) e.className = cls; return e; };
    const list = (items) => {
      const u = document.createElement('ul');
      items.forEach((it) => {
        const li = document.createElement('li'); const [main, act] = Array.isArray(it) ? it : [it]; li.append(main);
        if (act) { const s2 = document.createElement('span'); s2.className = 'act'; s2.textContent = act; li.appendChild(s2); }
        u.appendChild(li);
      });
      return u;
    };
    const g = (sm.gatherings || [])[0];
    const posture = EV.filter((e) => e.kind === 'awkward_posture'); const pw = [...new Set(posture.map((e) => e.tid))];
    const comp = sm.helmet_compliance == null ? '-' : Math.round(100 * sm.helmet_compliance) + '%';
    b.appendChild(para(`Ten minutes at the start of the morning shift in Welding Bay 1, Wed 7 Oct 2026, ${sm.video.clock_start} to ${sm.video.clock_end}. About ${Math.floor(sm.peak_people)} to ${Math.ceil(sm.peak_people + 0.01)} people were on camera at the busiest moment, ${Math.round(sm.person_seconds / 60)} person-minutes in total. Every alert was reviewed by a person.`, 'lead'));
    const two = document.createElement('div'); two.className = 'two';
    two.appendChild(sec('Went well', list([
      `Hard hats on: ${comp} of the time workers were close enough to check, with no hard-hat alerts.`,
      g ? `Toolbox talk from ${g.start} with up to ${g.peak} people, still going when the recording ends.` : 'No toolbox talk seen in this recording.',
      `Coverall on ${Math.round(100 * GEAR.coverall_pm / GEAR.checked_pm)}% of the time workers were close enough to check (orange ${GEAR.coverall_pm_by_colour.orange}, blue ${GEAR.coverall_pm_by_colour.blue} person-minutes).`,
      `Safety boots confirmed on ${Math.round(100 * GEAR.boots_seen_pm / GEAR.boots_feet_visible_pm)}% of the time feet were in view; nobody was seen without them.`,
      'Nobody stepped onto the pipe stack.',
      'The fire extinguisher stayed visible and clear the whole time.',
    ])));
    two.appendChild(sec('Needs attention', list([
      [`Cables and hoses spread across the main walkway, from ${f1(100 * (sm.clutter_start || 0))}% to ${f1(100 * (sm.clutter_end || 0))}% of the floor in ten minutes. That is a trip hazard where people walk.`, 'Action: run leads overhead or along the edge, use cable ramps, and clear the walkway before work starts.'],
      [`Reflective tape not seen for ${GEAR.tape_not_seen_pm} of ${GEAR.checked_pm} checked person-minutes, almost all on blue coveralls (${GEAR.tape_not_seen_pm_by_colour.blue}). Orange coveralls carried tape.`, 'Action: check whether the site requires reflective tape on all coveralls, and issue taped coveralls to the blue-coverall crew if so.'],
      [`Workers bent or crouched at floor level for 3 seconds or more ${posture.length} times (workers ${pw.join(', ')}), mostly pulling cable at the electrical cabinet.`, 'Action: use cable reels or a trolley, and review manual handling for this task.'],
    ])));
    b.appendChild(two);
    b.appendChild(sec('What this camera watches for', list([
      'Hard hat, coverall, reflective tape and safety boots on every worker close enough to check, with hard-hat and coverall colours',
      'People on the pipe stack (no-go), in the welding booths and at the gas cylinders',
      'Bending, crouching, or someone lying on the floor',
      'Toolbox talks and crowding',
      'Cables and hoses spreading onto the walkway',
      'The fire extinguisher being blocked, and welding flashes',
      ['Needs a closer camera', 'Gloves, safety glasses, welding face shields and face coverings are too small to judge reliably from this camera position.'],
      ['Can be added', 'The electrical cabinet left open, gas cylinders not secured, fume fan position, smoke and fire.'],
    ])));
    b.appendChild(sec('Worth tracking over the coming weeks', list([
      ['Hard hats on, by shift, crew and area', 'Shows whether it holds through the day and after the toolbox talk.'],
      ['Repeat issues per worker', 'Needs worker identity from badges or access control.'],
      ['Toolbox talk attendance against shift headcount', 'Shows who started work without the briefing.'],
      ['Walkway clutter at the end of each shift', 'Shows whether cable management is working.'],
      ['Hot-work hours with a fire watch present, and gas cylinders kept away from welding', ''],
      ['Heat stress against work and rest breaks in summer', 'Needs a heat-stress sensor in the bay.'],
      ['Near misses per 1,000 hours worked, compared across bays', ''],
    ].map(([a, c]) => (c ? [a, c] : a)))));
    const keys = document.createElement('div');
    [['Hard hat on', 'var(--ok)'], ['Alert', 'var(--crit)'], ['Hat not visible', 'var(--neutral)'], ['Too far to check', 'var(--dim)'], ['Toolbox talk', 'var(--aqua)'], ['Cables on walkway', 'var(--mage)']].forEach(([l, c]) => {
      const s2 = document.createElement('span'); s2.className = 'key'; const i2 = document.createElement('i'); i2.style.background = c; s2.append(i2, l); keys.appendChild(s2);
    });
    const how = document.createElement('div'); how.append(keys, list([
      'Close enough to check: near enough to the camera to see the head clearly. Workers at the far end of the bay are shown but not judged.',
      'Hat not visible: the worker is close but the head is turned away or hidden. It is not counted as a breach.',
      'Person-minute: one person on camera for one minute.',
      'Click any worker on the video to see when they arrived, their hard-hat and coverall colours, and where they spent time.',
    ]));
    b.appendChild(sec('How to read the screen', how));
  }

  // ------------------------------------------------------------------ init + loop
  function init() {
    readColors();
    chart('#c-people', drawPeople, { seek: true, tip: (t) => { const s = clamp(Math.floor(t), 0, NSEC - 1); return `${clockAt(t)} · ${Math.round(TL.get(s, 'people'))} on camera · ${Math.round(TL.get(s, 'assess_ok'))} hard hat confirmed`; } });
    chart('#c-clutter', drawClutter, { seek: true, tip: (t) => `${clockAt(t)} · ${(100 * (TL.get(clamp(Math.floor(t), 0, NSEC - 1), 'clutter_index') || 0)).toFixed(1)}% of walkway` });
    chart('#scrub', drawScrub, { seek: true, knob: true, tipTop: -32, tip: (t) => { const s = clamp(Math.floor(t), 0, NSEC - 1); const e = EV.find((x) => Math.abs(x.f0 / FPS - t) < 4); return `${clockAt(t)} · ${Math.round(TL.get(s, 'people'))} people${e ? ' · ' + (e.kind === 'gathering' ? 'toolbox talk' : e.kind === 'awkward_posture' ? 'bending/crouching' : 'cables on walkway') : ''}`; } });
    const heatCv = $('#c-heat'); const floor = new Image(); floor.src = 'media/floor.jpg'; floor.onload = () => { S.floor = floor; S.lastT = -1; };
    const reflow = () => { Object.keys(CH).forEach(renderStatic); S.lastT = -1; };
    const ro = new ResizeObserver(() => { clearTimeout(S.rt); S.rt = setTimeout(reflow, 60); }); Object.values(CH).forEach((c) => ro.observe(c.cv)); reflow();
    buildEvents(); buildDrawer();
    // controls
    document.querySelectorAll('.tog').forEach((b) => b.addEventListener('click', () => { const k = b.dataset.layer; S.layers[k] = !S.layers[k]; b.classList.toggle('on', S.layers[k]); S.lastT = -1; }));
    document.querySelectorAll('.sp').forEach((b) => b.addEventListener('click', () => { video.playbackRate = +b.dataset.rate; document.querySelectorAll('.sp').forEach((x) => x.classList.toggle('on', x === b)); }));
    document.querySelectorAll('.chip').forEach((b) => b.addEventListener('click', () => { S.filter = b.dataset.k; document.querySelectorAll('.chip').forEach((x) => x.classList.toggle('on', x === b)); buildEvents(); S.lastT = -1; }));
    $('#b-play').addEventListener('click', toggle); $('#b-back').addEventListener('click', () => seek(video.currentTime - 5)); $('#b-fwd').addEventListener('click', () => seek(video.currentTime + 5));
    $('#b-prev-ev').addEventListener('click', () => jumpEvent(-1)); $('#b-next-ev').addEventListener('click', () => jumpEvent(1));
    $('#tc-close').addEventListener('click', () => select(null));
    $('#tc-first').addEventListener('click', () => { const t = TR[S.sel]; if (t) seek(t.first / FPS); }); $('#tc-last').addEventListener('click', () => { const t = TR[S.sel]; if (t) seek(t.last / FPS - 1); });
    $('#btn-method').addEventListener('click', () => { $('#drawer').hidden = false; $('#dr-close').focus(); });
    $('#dr-close').addEventListener('click', () => ($('#drawer').hidden = true)); $('#drawer').addEventListener('click', (e) => { if (e.target.id === 'drawer') $('#drawer').hidden = true; });
    $('#btn-theme').addEventListener('click', toggleTheme);
    ov.addEventListener('click', (ev) => {
      const r = ov.getBoundingClientRect(); const k = r.width / W0; const x = (ev.clientX - r.left) / k, y = (ev.clientY - r.top) / k;
      const hit = recsAt(video.currentTime).filter((q) => x >= q[1] - 6 && x <= q[3] + 6 && y >= q[2] - 6 && y <= q[4] + 6).sort((a, b) => (a[3] - a[1]) * (a[4] - a[2]) - (b[3] - b[1]) * (b[4] - b[2]));
      if (hit.length) select(hit[0][0]); else if (S.sel) select(null); else toggle();
    });
    ov.addEventListener('dblclick', () => { const st = $('#stage'); (document.fullscreenElement ? document.exitFullscreen() : st.requestFullscreen?.())?.catch?.(() => {}); });
    document.addEventListener('keydown', (e) => {
      if (e.target && e.target.closest && e.target.closest('input,textarea,select')) return;
      const k = e.key;
      if (k === ' ') { e.preventDefault(); toggle(); }
      else if (k === 'ArrowLeft') { e.preventDefault(); seek(video.currentTime - 5); } else if (k === 'ArrowRight') { e.preventDefault(); seek(video.currentTime + 5); }
      else if (k === ',') { video.pause(); seek(video.currentTime - 1 / FPS); } else if (k === '.') { video.pause(); seek(video.currentTime + 1 / FPS); }
      else if (k === '[') jumpEvent(-1); else if (k === ']') jumpEvent(1);
      else if (k === 'h' || k === 'H') document.querySelector('[data-layer="heat"]').click();
      else if (k === 'z' || k === 'Z') document.querySelector('[data-layer="zones"]').click();
      else if (k === 'b' || k === 'B') document.querySelector('[data-layer="boxes"]').click();
      else if (k === 'd' || k === 'D') toggleTheme();
      else if (k === 'Escape') { $('#drawer').hidden = true; select(null); }
    });
    const stage = $('#stage'); const btn = $('#b-play');
    const sync = () => { btn.classList.toggle('playing', !video.paused); stage.classList.toggle('paused', video.paused); };
    video.addEventListener('play', sync); video.addEventListener('pause', sync); sync();
    video.addEventListener('loadedmetadata', () => { $('#tc-dur').textContent = mmss(video.duration); reflow(); });
    video.addEventListener('error', () => ($('#viewer-status').textContent = 'The video could not be played in this browser'), true);
    $('#viewer-status').textContent = `10 min recording · ${EV.length} events`;
    requestAnimationFrame(loop);
  }
  function toggleTheme() {
    const cur = document.documentElement.dataset.theme === 'light' ? 'dark' : 'light';
    document.documentElement.dataset.theme = cur; try { localStorage.setItem('vms-theme', cur); } catch (e) {}
    readColors(); Object.keys(CH).forEach(renderStatic); S.lastT = -1;
  }
  function drawHeatPanel(fi) {
    const cv = $('#c-heat'); const { ctx, w, h } = fitCanvas(cv);
    ctx.clearRect(0, 0, w, h);
    if (S.floor) { ctx.globalAlpha = .55; ctx.drawImage(S.floor, 0, 0, w, h); ctx.globalAlpha = 1; }
    heatUpdate(fi); ctx.imageSmoothingEnabled = true; ctx.drawImage(HG.cv, 0, 0, w, h);
  }
  function loop(now) {
    const t = video.currentTime || 0;
    if (t !== S.lastT) {
      const recs = drawOverlay(t);
      Object.keys(CH).forEach((id) => renderDyn(id, t));
      if (now - S.lastUi > 120 || video.paused) { updatePanels(t, recs); drawHeatPanel(frameIndex(t)); S.lastUi = now; }
      S.lastT = t;
    }
    requestAnimationFrame(loop);
  }

  // ------------------------------------------------------------------ simple sign-in (demo access only; not a security boundary)
  const PASS_HASH = 'c648b007fe010afb3e64b0dcee486e76758f5fba7a1b31ce2d689522cb3ff477';
  async function sha256(t) { const b = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(t)); return [...new Uint8Array(b)].map((x) => x.toString(16).padStart(2, '0')).join(''); }
  let started = false;
  function unlock() {
    $('#gate').hidden = true; document.body.classList.remove('locked');
    if (started) return; started = true;
    video.preload = 'auto'; video.load();
    load().catch((e) => { $('#viewer-status').textContent = 'Could not load the review data. Refresh the page to try again.'; console.error(e); });
  }
  let authed = false; try { authed = sessionStorage.getItem('vms-auth') === '1'; } catch (e) {}
  if (authed) unlock();
  else {
    document.body.classList.add('locked'); setTimeout(() => $('#gate-user').focus(), 50);
    $('#gate-form').addEventListener('submit', async (e) => {
      e.preventDefault();
      const u = $('#gate-user').value.trim().toLowerCase(), pw = $('#gate-pass').value;
      if ((await sha256(u + ':' + pw)) === PASS_HASH) { try { sessionStorage.setItem('vms-auth', '1'); } catch (err) {} $('#gate-err').hidden = true; unlock(); }
      else { $('#gate-err').hidden = false; $('#gate-pass').value = ''; $('#gate-pass').focus(); }
    });
  }
  $('#btn-logout').addEventListener('click', () => { try { sessionStorage.removeItem('vms-auth'); } catch (e) {} location.reload(); });
})();
