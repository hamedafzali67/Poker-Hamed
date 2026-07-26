import React, { useState, useEffect, useRef, useCallback, useMemo } from "react";

/* ============================== POKER ENGINE ============================== */

const SUITS = ["s", "h", "d", "c"];
const SUIT_SYMBOL = { s: "♠", h: "♥", d: "♦", c: "♣" };
const SUIT_COLOR = { s: "#1c2b24", h: "#a3312a", d: "#a3312a", c: "#1c2b24" };
const RANK_LABEL = { 14: "A", 13: "K", 12: "Q", 11: "J", 10: "10" };
const RANK_NAMES = ["High Card","Pair","Two Pair","Trips","Straight","Flush","Full House","Quads","Straight Flush"];

function rankLabel(r) { return RANK_LABEL[r] || String(r); }

function freshDeck() {
  const deck = [];
  for (let r = 2; r <= 14; r++) for (const s of SUITS) deck.push({ r, s });
  return deck;
}

function shuffle(deck, seed) {
  // simple seeded PRNG (mulberry32) so shuffles are reproducible from a stored seed if ever needed
  let a = seed >>> 0;
  function rnd() {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }
  const d = [...deck];
  for (let i = d.length - 1; i > 0; i--) {
    const j = Math.floor(rnd() * (i + 1));
    [d[i], d[j]] = [d[j], d[i]];
  }
  return d;
}

function combinations(arr, k) {
  const results = [];
  (function helper(start, combo) {
    if (combo.length === k) { results.push([...combo]); return; }
    for (let i = start; i < arr.length; i++) { combo.push(arr[i]); helper(i + 1, combo); combo.pop(); }
  })(0, []);
  return results;
}

function evaluate5(cards) {
  const ranks = cards.map((c) => c.r).sort((a, b) => b - a);
  const suits = cards.map((c) => c.s);
  const isFlush = suits.every((s) => s === suits[0]);
  const counts = {};
  for (const r of ranks) counts[r] = (counts[r] || 0) + 1;
  const groups = Object.entries(counts).map(([r, c]) => ({ r: parseInt(r), c })).sort((a, b) => b.c - a.c || b.r - a.r);
  let uniq = [...new Set(ranks)];
  let straightHigh = null;
  if (uniq.length === 5) {
    if (uniq[0] - uniq[4] === 4) straightHigh = uniq[0];
    else if (JSON.stringify(uniq) === JSON.stringify([14, 5, 4, 3, 2])) straightHigh = 5;
  }
  if (straightHigh && isFlush) return [8, straightHigh];
  if (groups[0].c === 4) return [7, groups[0].r, groups.find((g) => g.c === 1).r];
  if (groups[0].c === 3 && groups[1] && groups[1].c === 2) return [6, groups[0].r, groups[1].r];
  if (isFlush) return [5, ...ranks];
  if (straightHigh) return [4, straightHigh];
  if (groups[0].c === 3) return [3, groups[0].r, ...groups.filter((g) => g.c === 1).map((g) => g.r).sort((a, b) => b - a)];
  if (groups[0].c === 2 && groups[1] && groups[1].c === 2) {
    const pairRanks = [groups[0].r, groups[1].r].sort((a, b) => b - a);
    return [2, ...pairRanks, groups.find((g) => g.c === 1).r];
  }
  if (groups[0].c === 2) return [1, groups[0].r, ...groups.filter((g) => g.c === 1).map((g) => g.r).sort((a, b) => b - a)];
  return [0, ...ranks];
}

function compareScore(a, b) {
  for (let i = 0; i < Math.max(a.length, b.length); i++) {
    const av = a[i] ?? -1, bv = b[i] ?? -1;
    if (av !== bv) return av - bv;
  }
  return 0;
}

function bestHand(cards7) {
  let best = null;
  for (const c of combinations(cards7, 5)) {
    const score = evaluate5(c);
    if (!best || compareScore(score, best) > 0) best = score;
  }
  return best;
}

function distributePots(players) {
  // players: [{id, totalBet, folded}]
  const contributions = players.map((p) => ({ id: p.id, amt: p.totalBet, folded: p.folded }));
  const pots = [];
  while (contributions.some((c) => c.amt > 0)) {
    const min = Math.min(...contributions.filter((c) => c.amt > 0).map((c) => c.amt));
    let potAmt = 0;
    const eligible = [];
    for (const c of contributions) {
      if (c.amt > 0) {
        potAmt += min;
        c.amt -= min;
        if (!c.folded) eligible.push(c.id);
      }
    }
    if (potAmt > 0) pots.push({ amount: potAmt, eligible });
  }
  return pots;
}

function randomCode() {
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let s = "";
  for (let i = 0; i < 5; i++) s += chars[Math.floor(Math.random() * chars.length)];
  return s;
}
function randomId() { return Math.random().toString(36).slice(2, 10); }

function activePlayers(room) { return room.players.filter((p) => room.seatOrder.includes(p.id)); }
function seatedActive(room) {
  // players still in the current hand (not folded), in seat order
  return room.seatOrder.map((id) => room.players.find((p) => p.id === id)).filter((p) => p && !p.folded);
}

function nextIndex(room, fromIdx, opts = {}) {
  const n = room.seatOrder.length;
  let i = fromIdx;
  for (let step = 0; step < n; step++) {
    i = (i + 1) % n;
    const p = room.players.find((pl) => pl.id === room.seatOrder[i]);
    if (!p) continue;
    if (p.folded) continue;
    if (opts.skipAllIn && p.allIn) continue;
    return i;
  }
  return fromIdx;
}

function createRoom(code, hostId, hostName, settings) {
  return {
    code,
    hostId,
    createdAt: Date.now(),
    rev: 0,
    settings: { startingChips: settings.startingChips, smallBlind: settings.smallBlind },
    players: [{ id: hostId, name: hostName, chips: settings.startingChips, folded: false, allIn: false, betThisRound: 0, totalBet: 0, cards: [], connected: true, sittingOut: false }],
    seatOrder: [],
    dealerSeat: -1,
    phase: "lobby", // lobby | preflop | flop | turn | river | showdown | handover
    deck: [],
    community: [],
    pot: 0,
    currentBet: 0,
    minRaise: 0,
    actedSet: [],
    currentIdx: -1,
    lastAggressor: null,
    log: ["اتاق ساخته شد."],
    results: null,
  };
}

function addPlayer(room, id, name) {
  if (room.players.some((p) => p.id === id)) return room;
  const players = [...room.players, { id, name, chips: room.settings.startingChips, folded: false, allIn: false, betThisRound: 0, totalBet: 0, cards: [], connected: true, sittingOut: false }];
  return { ...room, players, log: [...room.log, `${name} به اتاق پیوست.`] };
}

function startHand(room) {
  const eligible = room.players.filter((p) => p.chips > 0);
  if (eligible.length < 2) return { ...room, log: [...room.log, "برای شروع حداقل ۲ بازیکن با ژتون لازم است."] };

  // rotate dealer among eligible players
  let order = room.players.map((p) => p.id).filter((id) => eligible.some((p) => p.id === id));
  let dealerPos = 0;
  if (room.dealerSeat >= 0) {
    const prevDealerId = room.seatOrder[room.dealerSeat];
    const idxInOrder = order.indexOf(prevDealerId);
    dealerPos = idxInOrder >= 0 ? (idxInOrder + 1) % order.length : 0;
  }
  // rotate the order array so dealerPos is at index 0, keep relative seating stable
  const seatOrder = [...order.slice(dealerPos), ...order.slice(0, dealerPos)];
  const dealerSeat = 0;

  const deck = shuffle(freshDeck(), Date.now() ^ Math.floor(Math.random() * 1e9));
  let deckIdx = 0;
  const players = room.players.map((p) => {
    if (!seatOrder.includes(p.id)) return { ...p, folded: true, cards: [], betThisRound: 0, totalBet: 0, allIn: false };
    return { ...p, folded: false, allIn: false, betThisRound: 0, totalBet: 0, cards: [deck[deckIdx++], deck[deckIdx++]] };
  });

  const sb = room.settings.smallBlind;
  const bb = sb * 2;
  const n = seatOrder.length;
  let sbSeat, bbSeat, firstToActSeat;
  if (n === 2) {
    sbSeat = 0; bbSeat = 1; firstToActSeat = 0; // heads-up: dealer posts SB and acts first preflop
  } else {
    sbSeat = 1 % n; bbSeat = 2 % n; firstToActSeat = 3 % n;
  }

  function postBlind(plist, seat, amt) {
    const id = seatOrder[seat];
    return plist.map((p) => {
      if (p.id !== id) return p;
      const pay = Math.min(amt, p.chips);
      return { ...p, chips: p.chips - pay, betThisRound: pay, totalBet: pay, allIn: p.chips - pay === 0 };
    });
  }
  let p2 = postBlind(players, sbSeat, sb);
  p2 = postBlind(p2, bbSeat, bb);

  const pot = p2.filter((p) => seatOrder.includes(p.id)).reduce((s, p) => s + p.totalBet, 0);

  const room2 = {
    ...room,
    players: p2,
    seatOrder,
    dealerSeat,
    phase: "preflop",
    deck: deck.slice(deckIdx),
    community: [],
    pot,
    currentBet: bb,
    minRaise: bb,
    actedSet: [],
    currentIdx: firstToActSeat,
    lastAggressor: seatOrder[bbSeat],
    results: null,
    log: [...room.log, `--- دست جدید --- (بلایند کوچک ${sb}, بزرگ ${bb})`],
  };
  return room2;
}

function isRoundOver(room) {
  const contenders = seatedActive(room).filter((p) => !p.allIn);
  if (contenders.length === 0) return true;
  return contenders.every((p) => room.actedSet.includes(p.id) && p.betThisRound === room.currentBet);
}

function collectBetsIntoPot(room) {
  return { ...room, players: room.players.map((p) => ({ ...p, betThisRound: 0 })), currentBet: 0, minRaise: room.settings.smallBlind * 2, actedSet: [] };
}

function dealCommunity(room, count) {
  const cards = room.deck.slice(0, count);
  return { ...room, community: [...room.community, ...cards], deck: room.deck.slice(count) };
}

function computeShowdown(room) {
  const contenders = seatedActive(room);
  const pots = distributePots(room.players.filter((p) => room.seatOrder.includes(p.id)).map((p) => ({ id: p.id, totalBet: p.totalBet, folded: p.folded })));
  const handInfo = {};
  for (const p of contenders) {
    const score = bestHand([...p.cards, ...room.community]);
    handInfo[p.id] = score;
  }
  let players = [...room.players];
  const winnerLines = [];
  for (const pot of pots) {
    const eligibleIds = pot.eligible.filter((id) => handInfo[id]);
    if (eligibleIds.length === 0) continue;
    let best = null;
    for (const id of eligibleIds) if (!best || compareScore(handInfo[id], best) > 0) best = handInfo[id];
    const winners = eligibleIds.filter((id) => compareScore(handInfo[id], best) === 0);
    const share = Math.floor(pot.amount / winners.length);
    let remainder = pot.amount - share * winners.length;
    players = players.map((p) => {
      if (!winners.includes(p.id)) return p;
      let amt = share;
      if (remainder > 0) { amt += 1; remainder -= 1; }
      return { ...p, chips: p.chips + amt };
    });
    const names = winners.map((id) => room.players.find((p) => p.id === id)?.name).join(" و ");
    winnerLines.push(`${names} برنده ${pot.amount} ژتون شد با ${RANK_NAMES[best[0]]}`);
  }
  const results = { handInfo, pots, lines: winnerLines };
  return { ...room, players, phase: "showdown", results, log: [...room.log, ...winnerLines] };
}

function awardUncontested(room) {
  const winner = seatedActive(room)[0];
  const players = room.players.map((p) => p.id === winner.id ? { ...p, chips: p.chips + room.pot } : p);
  return { ...room, players, phase: "handover", results: { lines: [`${winner.name} پات ${room.pot} ژتونی را برد (بقیه فولد کردند)`] }, log: [...room.log, `${winner.name} پات را برد (بقیه فولد کردند).`] };
}

function advance(room) {
  let r = room;
  if (seatedActive(r).length <= 1) return awardUncontested(r);
  if (!isRoundOver(r)) {
    let idx = r.currentIdx;
    idx = nextIndex(r, idx, { skipAllIn: true });
    return { ...r, currentIdx: idx };
  }
  // round over -> collect bets, move to next phase
  r = collectBetsIntoPot(r);
  const remainingActionable = seatedActive(r).filter((p) => !p.allIn).length;
  if (r.phase === "preflop") { r = dealCommunity(r, 3); r = { ...r, phase: "flop" }; }
  else if (r.phase === "flop") { r = dealCommunity(r, 1); r = { ...r, phase: "turn" }; }
  else if (r.phase === "turn") { r = dealCommunity(r, 1); r = { ...r, phase: "river" }; }
  else if (r.phase === "river") { return computeShowdown(r); }

  if (remainingActionable < 2) {
    // everyone (or all but one) is all-in: auto run out the board
    return advance(r);
  }
  const startSeat = nextIndex(r, r.dealerSeat, { skipAllIn: true });
  // nextIndex from dealerSeat itself might land on dealer if only one active; find first active after dealer
  let seat = r.dealerSeat;
  let found = -1;
  for (let step = 0; step < r.seatOrder.length; step++) {
    seat = (seat + 1) % r.seatOrder.length;
    const p = r.players.find((pl) => pl.id === r.seatOrder[seat]);
    if (p && !p.folded && !p.allIn) { found = seat; break; }
  }
  return { ...r, currentIdx: found >= 0 ? found : startSeat };
}

function applyAction(room, playerId, type, amount) {
  const seat = room.seatOrder.indexOf(playerId);
  if (seat === -1 || seat !== room.currentIdx) return room; // not your turn
  const player = room.players.find((p) => p.id === playerId);
  if (!player || player.folded || player.allIn) return room;

  let players = [...room.players];
  let log = [...room.log];
  let currentBet = room.currentBet;
  let minRaise = room.minRaise;
  let pot = room.pot;
  let actedSet = [...room.actedSet];
  let lastAggressor = room.lastAggressor;

  const updatePlayer = (id, patch) => { players = players.map((p) => (p.id === id ? { ...p, ...patch } : p)); };

  if (type === "fold") {
    updatePlayer(playerId, { folded: true });
    log.push(`${player.name} فولد کرد.`);
    actedSet = [...actedSet, playerId];
  } else if (type === "check") {
    if (player.betThisRound !== currentBet) return room;
    log.push(`${player.name} چک کرد.`);
    actedSet = [...actedSet, playerId];
  } else if (type === "call") {
    const need = Math.min(currentBet - player.betThisRound, player.chips);
    const allIn = need === player.chips && need > 0;
    updatePlayer(playerId, { chips: player.chips - need, betThisRound: player.betThisRound + need, totalBet: player.totalBet + need, allIn: allIn || player.chips - need === 0 });
    pot += need;
    log.push(`${player.name} ${need} ژتون کال کرد${allIn ? " (آل‌این)" : ""}.`);
    actedSet = [...actedSet, playerId];
  } else if (type === "raise" || type === "allin") {
    let target = type === "allin" ? player.betThisRound + player.chips : amount;
    target = Math.min(target, player.betThisRound + player.chips);
    const put = target - player.betThisRound;
    if (put <= 0) return room;
    const isAllIn = put >= player.chips;
    const raiseSize = target - currentBet;
    updatePlayer(playerId, { chips: player.chips - put, betThisRound: target, totalBet: player.totalBet + put, allIn: isAllIn });
    pot += put;
    if (target > currentBet) {
      currentBet = target;
      if (raiseSize >= minRaise || isAllIn) { if (raiseSize > 0) minRaise = Math.max(minRaise, raiseSize); }
      lastAggressor = playerId;
      actedSet = [playerId];
      log.push(`${player.name} به ${target} ${isAllIn ? "آل‌این کرد" : "رِیز کرد"}.`);
    } else {
      actedSet = [...actedSet, playerId];
      log.push(`${player.name} آل‌این کرد با ${target}.`);
    }
  } else {
    return room;
  }

  let r = { ...room, players, log, currentBet, minRaise, pot, actedSet, lastAggressor, rev: room.rev + 1 };
  r = advance(r);
  return r;
}

/* ============================== FIREBASE STORAGE (REST + SSE) ============================== */

const DB_URL = "https://poker-hamed-default-rtdb.firebaseio.com";

// Firebase Realtime Database silently drops empty arrays/objects on write (and can turn
// sparse arrays into keyed objects). This restores the shape our game logic expects whenever
// data comes back from Firebase, so a "no community cards yet" or "no log yet" state doesn't
// crash the app.
function toArray(v) {
  if (Array.isArray(v)) return v;
  if (v && typeof v === "object") return Object.keys(v).sort((a, b) => a - b).map((k) => v[k]);
  return [];
}
function normalizeRoom(r) {
  if (!r || r.__error) return r;
  return {
    ...r,
    players: toArray(r.players).map((p) => ({ ...p, cards: toArray(p.cards) })),
    seatOrder: toArray(r.seatOrder),
    deck: toArray(r.deck),
    community: toArray(r.community),
    actedSet: toArray(r.actedSet),
    log: toArray(r.log),
  };
}

async function loadRoom(code) {
  try {
    const res = await fetch(`${DB_URL}/rooms/${code}.json`);
    if (!res.ok) {
      const text = await res.text().catch(() => "");
      return { __error: `HTTP ${res.status} ${text}`.trim() };
    }
    const data = await res.json();
    return data ? normalizeRoom(data) : null;
  } catch (e) {
    return { __error: `fetch failed: ${e?.message || String(e)}` };
  }
}

async function saveRoom(room) {
  try {
    const res = await fetch(`${DB_URL}/rooms/${room.code}.json`, {
      method: "PUT",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(room),
    });
    if (!res.ok) {
      const text = await res.text().catch(() => "");
      return { ok: false, error: `HTTP ${res.status} ${text}`.trim() };
    }
    return { ok: true };
  } catch (e) {
    return { ok: false, error: `fetch failed: ${e?.message || String(e)}` };
  }
}

// Real-time listener using Firebase's SSE endpoint (native EventSource, no SDK needed).
// Falls back to short polling automatically if the stream errors repeatedly.
function listenRoom(code, onUpdate) {
  let closed = false;
  let es = null;
  let fallbackTimer = null;
  let errorCount = 0;

  function startFallbackPolling() {
    if (fallbackTimer) return;
    fallbackTimer = setInterval(async () => {
      const r = await loadRoom(code);
      if (r && !r.__error && !closed) onUpdate(r);
    }, 1500);
  }

  function connect() {
    try {
      es = new EventSource(`${DB_URL}/rooms/${code}.json`);
      es.addEventListener("put", (e) => {
        errorCount = 0;
        try {
          const parsed = JSON.parse(e.data);
          if (parsed && parsed.path === "/" && parsed.data && !closed) onUpdate(normalizeRoom(parsed.data));
        } catch (err) {}
      });
      es.onerror = () => {
        errorCount += 1;
        if (errorCount >= 3 && !closed) startFallbackPolling();
      };
    } catch (e) {
      startFallbackPolling();
    }
  }
  connect();

  return () => {
    closed = true;
    if (es) es.close();
    if (fallbackTimer) clearInterval(fallbackTimer);
  };
}

/* ============================== UI COMPONENTS ============================== */

function Card({ card, faceDown, small }) {
  const w = small ? 34 : 46, h = small ? 48 : 64;
  if (faceDown || !card) {
    return (
      <div style={{
        width: w, height: h, borderRadius: 6, background: "linear-gradient(135deg,#8a6d1f,#c9a227 40%,#8a6d1f)",
        border: "1px solid #6b551a", boxShadow: "0 2px 4px rgba(0,0,0,.4)", flexShrink: 0,
        backgroundImage: "repeating-linear-gradient(45deg, rgba(255,255,255,.06) 0 4px, transparent 4px 8px)"
      }} />
    );
  }
  return (
    <div style={{
      width: w, height: h, borderRadius: 6, background: "#f2ead6", border: "1px solid #cbb98a",
      boxShadow: "0 2px 4px rgba(0,0,0,.4)", display: "flex", flexDirection: "column",
      justifyContent: "space-between", padding: "2px 4px", flexShrink: 0, fontFamily: "'JetBrains Mono', monospace"
    }}>
      <div style={{ fontSize: small ? 12 : 14, fontWeight: 700, color: SUIT_COLOR[card.s], lineHeight: 1 }}>{rankLabel(card.r)}</div>
      <div style={{ fontSize: small ? 16 : 20, color: SUIT_COLOR[card.s], textAlign: "center", lineHeight: 1 }}>{SUIT_SYMBOL[card.s]}</div>
    </div>
  );
}

function ChipStack({ amount }) {
  if (!amount) return null;
  return (
    <div style={{
      background: "rgba(15,10,2,.75)", border: "1px solid #c9a227", borderRadius: 12,
      padding: "2px 8px", fontFamily: "'JetBrains Mono', monospace", fontSize: 12, color: "#f2e9d8",
      whiteSpace: "nowrap"
    }}>{amount}</div>
  );
}

function seatPosition(i, n) {
  // distribute around an ellipse, seat 0 (dealer at time of layout) near bottom-center for the viewer... 
  // we instead rotate so "me" is always at bottom via caller-side reindexing
  const angle = (Math.PI * 2 * i) / n - Math.PI / 2;
  const rx = 44, ry = 40;
  const x = 50 + rx * Math.cos(angle);
  const y = 50 + ry * Math.sin(angle);
  return { left: `${x}%`, top: `${y}%` };
}

function HomeScreen({ onCreate, onJoin, externalError, busy }) {
  const [name, setName] = useState("");
  const [mode, setMode] = useState(null);
  const [chips, setChips] = useState(1000);
  const [sb, setSb] = useState(10);
  const [code, setCode] = useState("");
  const [error, setError] = useState("");
  const shownError = error || externalError;

  const btnStyle = {
    background: "linear-gradient(180deg,#2a5c46,#1b4332)", color: "#f2e9d8", border: "1px solid #3f7a5c",
    borderRadius: 10, padding: "12px 18px", fontSize: 15, fontWeight: 600, cursor: "pointer",
    fontFamily: "'Fraunces', serif", letterSpacing: 0.3,
  };
  const inputStyle = {
    background: "#0d2818", color: "#f2e9d8", border: "1px solid #3f7a5c", borderRadius: 8,
    padding: "10px 12px", fontSize: 15, fontFamily: "'Inter', sans-serif", width: "100%", boxSizing: "border-box",
  };

  return (
    <div style={{ minHeight: "100vh", background: "radial-gradient(ellipse at center, #12331f 0%, #081a10 100%)", display: "flex", alignItems: "center", justifyContent: "center", padding: 20 }}>
      <div style={{ width: 360, maxWidth: "100%" }}>
        <div style={{ textAlign: "center", marginBottom: 28 }}>
          <div style={{ fontFamily: "'Fraunces', serif", fontSize: 42, color: "#c9a227", letterSpacing: 1, fontWeight: 600 }}>میز پوکر</div>
          <div style={{ color: "#8fae9c", fontSize: 13, marginTop: 4, fontFamily: "'Inter', sans-serif" }}>تگزاس هولدم آنلاین با دوستانت</div>
        </div>
        <div style={{ background: "rgba(0,0,0,.25)", border: "1px solid #2d5641", borderRadius: 14, padding: 20 }}>
          <label style={{ color: "#c9d9cf", fontSize: 13, marginBottom: 6, display: "block" }}>اسم تو</label>
          <input style={{ ...inputStyle, marginBottom: 16 }} value={name} onChange={(e) => setName(e.target.value)} placeholder="مثلا علی" maxLength={16} />

          {mode === null && (
            <div style={{ display: "flex", flexDirection: "column", gap: 10 }}>
              <button style={btnStyle} onClick={() => { if (!name.trim()) { setError("اول اسمت رو بنویس"); return; } setError(""); setMode("create"); }}>ساخت اتاق جدید</button>
              <button style={{ ...btnStyle, background: "linear-gradient(180deg,#4a3a15,#3a2d10)", border: "1px solid #c9a227" }} onClick={() => { if (!name.trim()) { setError("اول اسمت رو بنویس"); return; } setError(""); setMode("join"); }}>پیوستن به اتاق</button>
            </div>
          )}

          {mode === "create" && (
            <div style={{ display: "flex", flexDirection: "column", gap: 12 }}>
              <div>
                <label style={{ color: "#c9d9cf", fontSize: 13, marginBottom: 6, display: "block" }}>ژتون شروع هر نفر</label>
                <input style={inputStyle} type="number" value={chips} onChange={(e) => setChips(parseInt(e.target.value) || 0)} />
              </div>
              <div>
                <label style={{ color: "#c9d9cf", fontSize: 13, marginBottom: 6, display: "block" }}>بلایند کوچک</label>
                <input style={inputStyle} type="number" value={sb} onChange={(e) => setSb(parseInt(e.target.value) || 0)} />
              </div>
              <button style={{ ...btnStyle, opacity: busy ? 0.6 : 1 }} disabled={busy} onClick={() => { setError(""); onCreate(name.trim(), { startingChips: chips, smallBlind: sb }); }}>{busy ? "در حال ساخت..." : "ساخت اتاق"}</button>
              <button style={{ background: "none", border: "none", color: "#8fae9c", cursor: "pointer", fontSize: 13 }} onClick={() => setMode(null)}>بازگشت</button>
            </div>
          )}

          {mode === "join" && (
            <div style={{ display: "flex", flexDirection: "column", gap: 12 }}>
              <div>
                <label style={{ color: "#c9d9cf", fontSize: 13, marginBottom: 6, display: "block" }}>کد اتاق</label>
                <input style={{ ...inputStyle, letterSpacing: 3, textAlign: "center", fontSize: 20, fontFamily: "'JetBrains Mono', monospace" }} value={code} onChange={(e) => setCode(e.target.value.toUpperCase())} maxLength={5} placeholder="ABCDE" />
              </div>
              <button style={{ ...btnStyle, opacity: busy ? 0.6 : 1 }} disabled={busy} onClick={() => { setError(""); onJoin(name.trim(), code.trim()); }}>{busy ? "در حال اتصال..." : "پیوستن"}</button>
              <button style={{ background: "none", border: "none", color: "#8fae9c", cursor: "pointer", fontSize: 13 }} onClick={() => setMode(null)}>بازگشت</button>
            </div>
          )}
          {shownError && <div style={{ color: "#e08a7a", fontSize: 13, marginTop: 10 }}>{shownError}</div>}
        </div>
        <div style={{ color: "#5f7d6c", fontSize: 11, textAlign: "center", marginTop: 16, lineHeight: 1.6 }}>
          فقط ژتون مجازی — بدون پول واقعی.<br/>
          توجه: این یه بازی خودمونیه بین دوستا؛ کارت‌های همه در حافظهٔ مشترک ذخیره می‌شن، پس یه بازیکن با ابزار توسعه‌دهنده مرورگر تئوریاً می‌تونه تقلب کنه. برای بازی با آدمای مورد اعتماد مناسبه.
        </div>
      </div>
    </div>
  );
}

function LobbyScreen({ room, myId, onStart, onLeave }) {
  const isHost = room.hostId === myId;
  return (
    <div style={{ minHeight: "100vh", background: "radial-gradient(ellipse at center, #12331f 0%, #081a10 100%)", display: "flex", alignItems: "center", justifyContent: "center", padding: 20 }}>
      <div style={{ width: 380, maxWidth: "100%", background: "rgba(0,0,0,.25)", border: "1px solid #2d5641", borderRadius: 14, padding: 24 }}>
        <div style={{ textAlign: "center", marginBottom: 6, color: "#8fae9c", fontSize: 13 }}>کد اتاق را برای دوستانت بفرست</div>
        <div style={{ textAlign: "center", fontFamily: "'JetBrains Mono', monospace", fontSize: 34, color: "#c9a227", letterSpacing: 6, marginBottom: 20 }}>{room.code}</div>
        <div style={{ color: "#c9d9cf", fontSize: 13, marginBottom: 8 }}>بازیکنان ({room.players.length})</div>
        <div style={{ display: "flex", flexDirection: "column", gap: 8, marginBottom: 20 }}>
          {room.players.map((p) => (
            <div key={p.id} style={{ display: "flex", justifyContent: "space-between", background: "rgba(255,255,255,.04)", borderRadius: 8, padding: "8px 12px" }}>
              <span style={{ color: "#f2e9d8" }}>{p.name}{p.id === room.hostId ? " (میزبان)" : ""}{p.id === myId ? " — تو" : ""}</span>
              <span style={{ color: "#c9a227", fontFamily: "'JetBrains Mono', monospace" }}>{p.chips}</span>
            </div>
          ))}
        </div>
        {isHost ? (
          <button disabled={room.players.length < 2} onClick={onStart} style={{
            width: "100%", background: room.players.length < 2 ? "#2a3a30" : "linear-gradient(180deg,#2a5c46,#1b4332)",
            color: "#f2e9d8", border: "1px solid #3f7a5c", borderRadius: 10, padding: "12px 18px", fontSize: 15,
            fontWeight: 600, cursor: room.players.length < 2 ? "not-allowed" : "pointer", fontFamily: "'Fraunces', serif"
          }}>{room.players.length < 2 ? "منتظر بازیکن بیشتر..." : "شروع بازی"}</button>
        ) : (
          <div style={{ textAlign: "center", color: "#8fae9c", fontSize: 13 }}>منتظر میزبان برای شروع بازی...</div>
        )}
        <button onClick={onLeave} style={{ width: "100%", marginTop: 10, background: "none", border: "none", color: "#6f8d7c", cursor: "pointer", fontSize: 12 }}>ترک اتاق</button>
      </div>
    </div>
  );
}

function TableScreen({ room, myId, onAction }) {
  const [raiseAmt, setRaiseAmt] = useState(null);
  const me = room.players.find((p) => p.id === myId);
  const mySeat = room.seatOrder.indexOf(myId);
  const n = room.seatOrder.length;
  const myTurn = room.currentIdx === mySeat && ["preflop","flop","turn","river"].includes(room.phase);

  // reindex so my seat renders at the bottom
  const displayOrder = useMemo(() => {
    if (mySeat === -1) return room.seatOrder.map((id, i) => ({ id, i }));
    const arr = [];
    for (let k = 0; k < n; k++) arr.push({ id: room.seatOrder[(mySeat + k) % n], i: k });
    return arr;
  }, [room.seatOrder, mySeat, n]);

  const callAmt = me ? Math.min(room.currentBet - me.betThisRound, me.chips) : 0;
  const minRaiseTo = room.currentBet + room.minRaise;
  const maxRaiseTo = me ? me.betThisRound + me.chips : 0;

  useEffect(() => { setRaiseAmt(null); }, [room.currentIdx, room.phase]);

  const logRef = useRef(null);
  useEffect(() => { if (logRef.current) logRef.current.scrollTop = logRef.current.scrollHeight; }, [room.log]);

  return (
    <div style={{ minHeight: "100vh", background: "#081a10", display: "flex", flexDirection: "column" }}>
      <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", padding: "10px 16px", borderBottom: "1px solid #1e3d2c" }}>
        <div style={{ color: "#c9a227", fontFamily: "'JetBrains Mono', monospace", fontSize: 14 }}>اتاق {room.code}</div>
        <div style={{ color: "#8fae9c", fontSize: 12 }}>{{ preflop: "پری‌فلاپ", flop: "فلاپ", turn: "ترن", river: "ریور", showdown: "شوداون", handover: "پایان دست", lobby: "لابی" }[room.phase]}</div>
      </div>

      <div style={{ position: "relative", flex: 1, minHeight: 460 }}>
        {/* felt table */}
        <div style={{
          position: "absolute", left: "50%", top: "50%", transform: "translate(-50%,-50%)",
          width: "82%", height: "62%", borderRadius: "50%", background: "radial-gradient(ellipse at 50% 40%, #1f5b3f, #123726 75%)",
          border: "10px solid #3e2723", boxShadow: "0 0 0 2px #c9a227 inset, 0 10px 30px rgba(0,0,0,.5)"
        }} />

        {/* community cards + pot */}
        <div style={{ position: "absolute", left: "50%", top: "44%", transform: "translate(-50%,-50%)", display: "flex", flexDirection: "column", alignItems: "center", gap: 10 }}>
          <div style={{ display: "flex", gap: 6 }}>
            {[0,1,2,3,4].map((i) => <Card key={i} card={room.community[i]} faceDown={false} small={false} />).map((el, i) => room.community[i] ? el : <div key={i} style={{ width: 46, height: 64, borderRadius: 6, border: "1px dashed rgba(255,255,255,.15)" }} />)}
          </div>
          <div style={{ background: "rgba(0,0,0,.5)", border: "1px solid #c9a227", borderRadius: 20, padding: "4px 16px", color: "#f2e9d8", fontFamily: "'JetBrains Mono', monospace", fontSize: 13 }}>
            پات: {room.pot}
          </div>
        </div>

        {/* seats */}
        {displayOrder.map(({ id, i }) => {
          const p = room.players.find((pl) => pl.id === id);
          if (!p) return null;
          const pos = seatPosition(i, n);
          const isTurn = room.seatOrder.indexOf(id) === room.currentIdx && ["preflop","flop","turn","river"].includes(room.phase);
          const isDealer = room.seatOrder.indexOf(id) === room.dealerSeat;
          const isMe = id === myId;
          const showCards = isMe || room.phase === "showdown" || room.phase === "handover";
          const faceDown = !isMe && room.phase !== "showdown";
          const hand = room.results?.handInfo?.[id];
          return (
            <div key={id} style={{
              position: "absolute", ...pos, transform: "translate(-50%,-50%)", display: "flex", flexDirection: "column",
              alignItems: "center", gap: 4, width: 100
            }}>
              <div style={{
                background: isTurn ? "rgba(201,162,39,.25)" : "rgba(0,0,0,.45)", border: isTurn ? "1px solid #c9a227" : "1px solid #2d5641",
                borderRadius: 10, padding: "5px 9px", textAlign: "center", minWidth: 88
              }}>
                <div style={{ color: p.folded ? "#5f7d6c" : "#f2e9d8", fontSize: 12, fontWeight: 600, whiteSpace: "nowrap", overflow: "hidden", textOverflow: "ellipsis" }}>
                  {isDealer && <span style={{ color: "#c9a227" }}>●</span>} {p.name}
                </div>
                <div style={{ color: "#c9a227", fontFamily: "'JetBrains Mono', monospace", fontSize: 11 }}>{p.chips}</div>
                {p.folded && <div style={{ color: "#8a5a4a", fontSize: 10 }}>فولد</div>}
                {p.allIn && !p.folded && <div style={{ color: "#e0b25a", fontSize: 10 }}>آل‌این</div>}
                {hand && !p.folded && <div style={{ color: "#8fae9c", fontSize: 9 }}>{RANK_NAMES[hand[0]]}</div>}
              </div>
              <div style={{ display: "flex", gap: 3 }}>
                {(p.cards.length ? p.cards : [null, null]).map((c, ci) => showCards && p.cards.length ? <Card key={ci} card={c} small /> : <Card key={ci} faceDown small />)}
              </div>
              <ChipStack amount={p.betThisRound} />
            </div>
          );
        })}
      </div>

      {/* action bar / results */}
      <div style={{ borderTop: "1px solid #1e3d2c", padding: "10px 16px", background: "rgba(0,0,0,.3)" }}>
        {room.phase === "showdown" || room.phase === "handover" ? (
          <div style={{ display: "flex", flexDirection: "column", gap: 8, alignItems: "center" }}>
            {room.results?.lines?.map((l, i) => <div key={i} style={{ color: "#c9a227", fontSize: 13 }}>{l}</div>)}
            {room.hostId === myId ? (
              <button onClick={() => onAction("next_hand")} style={{ background: "linear-gradient(180deg,#2a5c46,#1b4332)", color: "#f2e9d8", border: "1px solid #3f7a5c", borderRadius: 10, padding: "10px 22px", fontFamily: "'Fraunces', serif", fontSize: 14, cursor: "pointer" }}>دست بعدی</button>
            ) : (
              <div style={{ color: "#8fae9c", fontSize: 12 }}>منتظر میزبان برای دست بعدی...</div>
            )}
          </div>
        ) : myTurn ? (
          <div style={{ display: "flex", flexDirection: "column", gap: 8 }}>
            {raiseAmt !== null && (
              <div style={{ display: "flex", alignItems: "center", gap: 10 }}>
                <input type="range" min={minRaiseTo} max={maxRaiseTo} value={Math.min(raiseAmt, maxRaiseTo)} onChange={(e) => setRaiseAmt(parseInt(e.target.value))} style={{ flex: 1 }} />
                <div style={{ color: "#f2e9d8", fontFamily: "'JetBrains Mono', monospace", width: 56, textAlign: "center" }}>{raiseAmt}</div>
              </div>
            )}
            <div style={{ display: "flex", gap: 8, flexWrap: "wrap" }}>
              <button onClick={() => onAction("fold")} style={actBtn("#5c2a2a")}>فولد</button>
              {callAmt === 0 ? (
                <button onClick={() => onAction("check")} style={actBtn("#2a4a5c")}>چک</button>
              ) : (
                <button onClick={() => onAction("call")} style={actBtn("#2a4a5c")}>کال {callAmt}</button>
              )}
              {maxRaiseTo > room.currentBet && (
                raiseAmt === null ? (
                  <button onClick={() => setRaiseAmt(Math.min(minRaiseTo, maxRaiseTo))} style={actBtn("#4a3a15")}>رِیز</button>
                ) : (
                  <button onClick={() => onAction(raiseAmt >= maxRaiseTo ? "allin" : "raise", raiseAmt)} style={actBtn("#4a3a15")}>{raiseAmt >= maxRaiseTo ? "آل‌این" : `رِیز به ${raiseAmt}`}</button>
                )
              )}
              {me && me.chips > 0 && (
                <button onClick={() => onAction("allin")} style={actBtn("#7a3a1a")}>آل‌این ({me.chips + me.betThisRound})</button>
              )}
            </div>
          </div>
        ) : (
          <div style={{ textAlign: "center", color: "#5f7d6c", fontSize: 12 }}>
            {me?.folded ? "فولد کردی — منتظر پایان دست" : "منتظر نوبت..."}
          </div>
        )}
      </div>

      {/* log */}
      <div ref={logRef} style={{ maxHeight: 90, overflowY: "auto", background: "rgba(0,0,0,.4)", padding: "6px 16px", fontSize: 11, color: "#8fae9c", fontFamily: "'Inter', sans-serif" }}>
        {room.log.slice(-30).map((l, i) => <div key={i}>{l}</div>)}
      </div>
    </div>
  );
}

function actBtn(bg) {
  return { background: bg, color: "#f2e9d8", border: "1px solid rgba(255,255,255,.15)", borderRadius: 8, padding: "10px 16px", fontSize: 13, fontWeight: 600, cursor: "pointer", fontFamily: "'Inter', sans-serif" };
}

/* ============================== ROOT APP ============================== */

function PokerApp() {
  const [myId] = useState(() => randomId());
  const [myName, setMyName] = useState("");
  const [room, setRoom] = useState(null);
  const [error, setError] = useState("");
  const [busy, setBusy] = useState(false);
  const unsubRef = useRef(null);

  const stopListening = () => { if (unsubRef.current) { unsubRef.current(); unsubRef.current = null; } };
  const startListeningRoom = useCallback((code) => {
    stopListening();
    unsubRef.current = listenRoom(code, (r) => setRoom(r));
  }, []);

  useEffect(() => () => stopListening(), []);

  async function handleCreate(name, settings) {
    setBusy(true);
    setError("");
    try {
      setMyName(name);
      let code = randomCode();
      let existing = await loadRoom(code);
      let tries = 0;
      while (existing && !existing.__error && tries < 5) { code = randomCode(); existing = await loadRoom(code); tries++; }
      if (existing && existing.__error) { setError("اتصال به دیتابیس برقرار نشد: " + existing.__error); return; }
      const newRoom = createRoom(code, myId, name, settings);
      const res = await saveRoom(newRoom);
      if (!res.ok) { setError("ذخیره‌ی اتاق ناموفق بود: " + res.error); return; }
      setRoom(newRoom);
      startListeningRoom(code);
    } catch (e) {
      setError("یه خطای غیرمنتظره پیش اومد: " + (e?.message || String(e)));
    } finally {
      setBusy(false);
    }
  }

  async function handleJoin(name, code) {
    if (!code) { setError("کد اتاق رو وارد کن."); return; }
    setBusy(true);
    setError("");
    try {
      setMyName(name);
      const existing = await loadRoom(code);
      if (existing && existing.__error) { setError("اتصال به دیتابیس برقرار نشد: " + existing.__error); return; }
      if (!existing) { setError("اتاقی با این کد پیدا نشد."); return; }
      const already = existing.players.find((p) => p.name === name);
      let updated = existing;
      if (!already) {
        updated = addPlayer(existing, myId, name);
        const res = await saveRoom(updated);
        if (!res.ok) { setError("مشکلی پیش اومد: " + res.error); return; }
      }
      setRoom(updated);
      startListeningRoom(code);
    } catch (e) {
      setError("یه خطای غیرمنتظره پیش اومد: " + (e?.message || String(e)));
    } finally {
      setBusy(false);
    }
  }

  const effectiveMyId = room?.players.find((p) => p.name === myName)?.id || myId;

  async function handleStart() {
    const latest = await loadRoom(room.code);
    if (!latest || latest.__error) return;
    const updated = startHand(latest);
    const res = await saveRoom(updated);
    if (res.ok) setRoom(updated);
    else setError("مشکلی در ذخیره پیش اومد: " + res.error);
  }

  async function handleAction(type, amount) {
    const latest = await loadRoom(room.code);
    if (!latest || latest.__error) return;
    let updated;
    if (type === "next_hand") updated = startHand(latest);
    else updated = applyAction(latest, effectiveMyId, type, amount);
    const res = await saveRoom(updated);
    if (res.ok) setRoom(updated);
    else setError("مشکلی در ذخیره پیش اومد: " + res.error);
  }

  async function handleLeave() {
    stopListening();
    setRoom(null);
    setError("");
  }

  if (!room) return <HomeScreen onCreate={handleCreate} onJoin={handleJoin} externalError={error} busy={busy} />;
  if (room.phase === "lobby") return <LobbyScreen room={room} myId={effectiveMyId} onStart={handleStart} onLeave={handleLeave} />;
  return <TableScreen room={room} myId={effectiveMyId} onAction={handleAction} />;
}

class ErrorBoundary extends React.Component {
  constructor(props) {
    super(props);
    this.state = { error: null };
  }
  static getDerivedStateFromError(error) {
    return { error };
  }
  componentDidCatch(error, info) {
    console.error("Poker app crashed:", error, info);
  }
  render() {
    if (this.state.error) {
      return (
        <div style={{ minHeight: "100vh", background: "#081a10", color: "#f2e9d8", padding: 24, fontFamily: "'Inter', sans-serif" }}>
          <div style={{ color: "#e08a7a", fontSize: 18, fontWeight: 700, marginBottom: 12 }}>یه خطا توی برنامه پیش اومد</div>
          <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: 13, background: "rgba(0,0,0,.35)", padding: 14, borderRadius: 8, whiteSpace: "pre-wrap", marginBottom: 16 }}>
            {String(this.state.error?.message || this.state.error)}
          </div>
          <button
            onClick={() => window.location.reload()}
            style={{ background: "linear-gradient(180deg,#2a5c46,#1b4332)", color: "#f2e9d8", border: "1px solid #3f7a5c", borderRadius: 10, padding: "10px 18px", fontSize: 14, cursor: "pointer" }}
          >
            بارگذاری دوباره
          </button>
        </div>
      );
    }
    return this.props.children;
  }
}

export default function App() {
  return (
    <ErrorBoundary>
      <PokerApp />
    </ErrorBoundary>
  );
}
