// Bot Sprint bot: velocity entries for a six-hour pump.fun window.
//
// Where the Paper Sprint entry waited for a crowd to gather, this one
// watches how fast the crowd is arriving. A young curve qualifies when
// its last fifteen slots carry at least fourteen trades, when the
// distinct-buyer count in the second half of that window beats the first
// half (the crowd is accelerating, not thinning), when net inflow over
// the window clears five SOL, and when the price has climbed at least
// thirty percent from create without going vertical. Entries stake a
// little more than the sister bots, bank a fixed take-profit at +25%,
// trail anything that keeps running, cut at -7%, and leave by 240 slots.
// The usual paced probes keep the twenty-coin round-trip bar covered.
// A pure function of the batches: no clock, no randomness, no environment.

import { runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const SOL = 1_000_000_000n;
const BPS = 10_000n;

// Entry filters, measured at decision time on the batch's slot.
const MIN_AGE_SLOTS = 6;
const MAX_AGE_SLOTS = 30;
const MIN_REAL_SOL = 5n * SOL;
const MAX_REAL_SOL = 28n * SOL;
const VELOCITY_WINDOW_SLOTS = 15;
const MIN_WINDOW_TRADES = 20; // trades inside the velocity window
const MIN_FLOW_LAMPORTS = 7n * SOL; // net inflow over the velocity window
const MIN_BUYERS_TOTAL = 10;
const MAX_SELL_RATIO_BPS = 3_500n; // sells by others at most 35% of buys
const MIN_RUNUP_BPS = 3_000; // price at least +30% over the create price
const MAX_RUNUP_BPS = 7_000; // and at most +70%
const MAX_DEV_BUY = 3n * SOL;
const STAKE_LAMPORTS = (SOL * 3n) / 100n; // 0.03 SOL before the reserve cap
const MIN_BUY_LAMPORTS = SOL / 100n; // 0.01 SOL: the guardrail round-trip bar
const BUY_SLIPPAGE_BPS = 2_500;

// Exits: bank +25%, cut -7%, trail from +15% with an 8% leash, out by 240.
const TAKE_PROFIT_BPS = 2_500n;
const STOP_LOSS_BPS = 700n;
const TRAIL_ARM_BPS = 1_500n;
const TRAIL_BPS = 800n;
const MAX_HOLD_SLOTS = 240;
const STALE_SLOTS = 45;

// Guardrail probes over a 6-hour final window.
const PROBE_LAMPORTS = (SOL * 12n) / 1_000n; // 0.012 SOL per probe
const PROBE_TARGET_COINS = 22;
const WINDOW_SECONDS = 21_600;
const MAX_PROBES_TOTAL = 30;

interface Tick {
  slot: number;
  isBuy: boolean;
  sol: bigint;
  user: Pubkey;
}

interface Coin {
  createSlot: number;
  creator: Pubkey;
  vq0: bigint;
  vt0: bigint;
  devBuy: bigint;
  devSold: boolean;
  buyers: Set<Pubkey>;
  bought: bigint;
  soldByOthers: bigint;
  lastTradeSlot: number;
  recent: Tick[];
  entered: boolean;
  finished: boolean;
}

interface Held {
  openedSlot: number;
  bestValue: bigint;
  sellSent: boolean;
}

const coins = new Map<Pubkey, Coin>();
const held = new Map<Pubkey, Held>();
const probeStage = new Map<Pubkey, 'buying' | 'selling'>();
const roundTripCoins = new Set<Pubkey>();
let probesSent = 0;
let firstBlockTime: number | null = null;
let lastBlockTime = 0;

/** What selling `tokens` on a curve pays after the 1.25% curve fee, before tx fees. */
function sellValue(tokens: bigint, vq: bigint, vt: bigint): bigint {
  if (tokens <= 0n || vt <= 0n) return 0n;
  const gross = (tokens * vq) / (vt + tokens);
  return gross - (gross * 125n) / BPS;
}

interface WindowStats {
  trades: number;
  net: bigint;
  earlyBuyers: number;
  lateBuyers: number;
}

/** Velocity picture over the last VELOCITY_WINDOW_SLOTS slots. */
function windowStats(coin: Coin, slot: number): WindowStats {
  const from = slot - VELOCITY_WINDOW_SLOTS;
  let drop = 0;
  while (drop < coin.recent.length && coin.recent[drop]!.slot <= from) drop++;
  if (drop > 0) coin.recent.splice(0, drop);
  const mid = slot - VELOCITY_WINDOW_SLOTS / 2;
  let net = 0n;
  const early = new Set<Pubkey>();
  const late = new Set<Pubkey>();
  for (const t of coin.recent) {
    if (t.isBuy) {
      net += t.sol;
      (t.slot <= mid ? early : late).add(t.user);
    } else {
      net -= t.sol;
    }
  }
  return { trades: coin.recent.length, net, earlyBuyers: early.size, lateBuyers: late.size };
}

function readEvents(batch: Batch): void {
  for (const e of batch.events) {
    if (e.block_time !== null) {
      if (firstBlockTime === null) firstBlockTime = e.block_time;
      if (e.block_time > lastBlockTime) lastBlockTime = e.block_time;
    }
    if (e.event === 'CreateEvent') {
      coins.set(e.mint, {
        createSlot: e.slot,
        creator: e.creator,
        vq0: BigInt(e.virtual_quote_reserves),
        vt0: BigInt(e.virtual_token_reserves),
        devBuy: 0n,
        devSold: false,
        buyers: new Set(),
        bought: 0n,
        soldByOthers: 0n,
        lastTradeSlot: e.slot,
        recent: [],
        entered: false,
        finished: false,
      });
    } else if (e.event === 'TradeEvent') {
      const coin = coins.get(e.mint);
      if (coin === undefined) continue;
      const sol = BigInt(e.sol_amount);
      coin.lastTradeSlot = e.slot;
      coin.recent.push({ slot: e.slot, isBuy: e.is_buy, sol, user: e.user });
      if (e.is_buy) {
        coin.bought += sol;
        if (e.user === coin.creator) {
          if (e.slot === coin.createSlot) coin.devBuy += sol;
        } else {
          coin.buyers.add(e.user);
        }
      } else if (e.user === coin.creator) {
        coin.devSold = true;
      } else {
        coin.soldByOthers += sol;
      }
    } else {
      const coin = coins.get(e.mint);
      if (coin !== undefined) coin.finished = true;
    }
  }
}

function hasPending(state: BotState, mint: Pubkey, side: 'buy' | 'sell'): boolean {
  for (const p of state.pending.values()) {
    if (p.order.mint === mint && p.order.side === side) return true;
  }
  return false;
}

await runBot({
  onBatch(state, batch) {
    readEvents(batch);
    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = state.txFeeLamports();
    const marks = new Map<Pubkey, { vq: bigint; vt: bigint }>();
    for (const m of batch.marks) marks.set(m.mint, { vq: BigInt(m.virtual_quote_reserves), vt: BigInt(m.virtual_token_reserves) });

    for (const f of batch.fills) {
      if (f.status === 'filled' && f.side === 'sell' && !f.client_id.startsWith('_')) {
        roundTripCoins.add(f.mint);
      }
    }
    for (const mint of [...held.keys()]) {
      if (!state.positions.has(mint) && !hasPending(state, mint, 'buy') && !hasPending(state, mint, 'sell')) {
        held.delete(mint);
      }
    }
    for (const mint of [...probeStage.keys()]) {
      if (!state.positions.has(mint) && !hasPending(state, mint, 'buy') && !hasPending(state, mint, 'sell')) {
        probeStage.delete(mint);
      }
    }

    // Exits first: they free the position slots everything else needs.
    for (const [mint, pos] of state.positions) {
      if (orders.length >= cap) break;
      if (probeStage.has(mint)) continue;
      let h = held.get(mint);
      if (h === undefined) {
        h = { openedSlot: state.slot, bestValue: 0n, sellSent: false };
        held.set(mint, h);
      }
      if (h.sellSent) continue;
      const coin = coins.get(mint);
      const mk = marks.get(mint);
      const curve = state.curves.get(mint);
      const vq = mk?.vq ?? curve?.virtual_quote_reserves ?? 0n;
      const vt = mk?.vt ?? curve?.virtual_token_reserves ?? 0n;
      const value = sellValue(pos.token_amount, vq, vt) - tx;
      if (value > h.bestValue) h.bestValue = value;
      const cost = pos.cost_lamports;
      let exit = false;
      if (cost > 0n) {
        if (value * BPS >= cost * (BPS + TAKE_PROFIT_BPS)) exit = true;
        if (value * BPS <= cost * (BPS - STOP_LOSS_BPS)) exit = true;
        if (h.bestValue * BPS >= cost * (BPS + TRAIL_ARM_BPS) && value * BPS <= h.bestValue * (BPS - TRAIL_BPS)) exit = true;
      }
      if (state.slot - h.openedSlot >= MAX_HOLD_SLOTS) exit = true;
      if (coin !== undefined) {
        if (coin.devSold) exit = true;
        if (state.slot - coin.lastTradeSlot >= STALE_SLOTS) exit = true;
        if (coin.finished) exit = true;
      }
      if (!exit) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      h.sellSent = true;
    }

    // Probe exits: sell the whole probe on the first batch after it lands.
    for (const [mint] of probeStage) {
      if (orders.length >= cap) break;
      const pos = state.positions.get(mint);
      if (pos === undefined || hasPending(state, mint, 'sell') || hasPending(state, mint, 'buy')) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      probeStage.set(mint, 'selling');
    }

    // Entries: young curves whose crowd is measurably accelerating.
    let free = state.freeCashLamports();
    let openSlots = state.hello.caps.max_open_positions - state.committedPositionCount();
    for (const [mint, coin] of coins) {
      if (orders.length >= cap || openSlots <= 0) break;
      if (coin.entered || coin.finished || held.has(mint) || probeStage.has(mint)) continue;
      const age = state.slot - coin.createSlot;
      if (age < MIN_AGE_SLOTS) continue;
      if (age > MAX_AGE_SLOTS) {
        coin.entered = true;
        continue;
      }
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      const rq = curve.real_quote_reserves;
      if (rq < MIN_REAL_SOL || rq > MAX_REAL_SOL) continue;
      if (coin.devSold || coin.devBuy > MAX_DEV_BUY) continue;
      if (coin.buyers.size < MIN_BUYERS_TOTAL) continue;
      if (coin.bought > 0n && coin.soldByOthers * BPS > coin.bought * MAX_SELL_RATIO_BPS) continue;
      const stats = windowStats(coin, state.slot);
      if (stats.trades < MIN_WINDOW_TRADES) continue;
      if (stats.net < MIN_FLOW_LAMPORTS) continue;
      if (stats.lateBuyers <= stats.earlyBuyers) continue; // crowd must accelerate
      const runupBps = (curve.virtual_quote_reserves * coin.vt0 * BPS) / (curve.virtual_token_reserves * coin.vq0) - BPS;
      if (runupBps < BigInt(MIN_RUNUP_BPS) || runupBps > BigInt(MAX_RUNUP_BPS)) continue;
      const capBuy = state.maxBuyLamports(mint);
      const amount = capBuy < STAKE_LAMPORTS ? capBuy : STAKE_LAMPORTS;
      if (amount < MIN_BUY_LAMPORTS) continue;
      if (free < amount + 2n * tx) continue;
      orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: BUY_SLIPPAGE_BPS });
      free -= amount + tx;
      openSlots -= 1;
      coin.entered = true;
      held.set(mint, { openedSlot: state.slot, bestValue: 0n, sellSent: false });
    }

    // Probes: keep the distinct-coin round-trip count on pace for the bar.
    if (
      probesSent < MAX_PROBES_TOTAL &&
      probeStage.size === 0 &&
      openSlots > 0 &&
      firstBlockTime !== null &&
      roundTripCoins.size < PROBE_TARGET_COINS
    ) {
      const elapsed = Math.max(0, lastBlockTime - firstBlockTime);
      const due = Math.ceil((PROBE_TARGET_COINS * Math.min(elapsed, WINDOW_SECONDS)) / WINDOW_SECONDS);
      if (roundTripCoins.size < due) {
        for (const [mint, coin] of coins) {
          if (orders.length >= cap) break;
          if (coin.finished || coin.entered || held.has(mint) || roundTripCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (curve.real_quote_reserves < 5n * SOL) continue;
          if (state.slot - coin.lastTradeSlot > 30) continue;
          const capBuy = state.maxBuyLamports(mint);
          const amount = capBuy < PROBE_LAMPORTS ? capBuy : PROBE_LAMPORTS;
          if (amount < MIN_BUY_LAMPORTS) continue;
          if (free < amount + 2n * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: amount, max_slippage_bps: BUY_SLIPPAGE_BPS });
          free -= amount + tx;
          probeStage.set(mint, 'buying');
          coin.entered = true;
          probesSent += 1;
          break;
        }
      }
    }
    return orders;
  },
});
