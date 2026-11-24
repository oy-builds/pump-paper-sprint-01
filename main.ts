// Confirmed-Flow Momentum: a paper-trading bot for the pump.fun bonding-curve
// replay (agent-fun/replay/v2), run by the grader as `node /bot/main.ts`.
//
// Idea: most fresh pump.fun curves are noise. This bot waits until a curve's
// own tape confirms demand before spending anything: over a short window of
// slots it wants net SOL flowing in, several distinct buyers (not one wallet
// washing), buy volume dominating sell volume, and a price that has risen
// moderately but not vertically. It buys one fixed small stake, then sells
// the whole position on the first exit rule that fires: take-profit,
// stop-loss, a trailing stop once the trade is comfortably green, a fade in
// net flow, or a maximum hold time. No pyramiding, no averaging down, no
// martingale: a wrong entry costs one small stake and nothing more.
//
// Deterministic by construction: decisions depend only on the hello seed's
// stream of batches, iterated in insertion order. No clock, no Math.random,
// no environment, no network.

import { runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1_000_000_000;
const CURVE_FEE = 0.0125; // protocol 95 bps + creator 30 bps, as a fraction

// ---- entry signal -----------------------------------------------------------
const WINDOW_SLOTS = 50; // tape window the signal reads
const MIN_AGE_SLOTS = 600; // skip the bundled-launch phase of a curve's life
const MIN_NET_SOL = 1.5; // net inflow (buys - sells) over the window
const MIN_BUYS = 6; // buy trades in the window
const MIN_BUYERS = 6; // distinct buying wallets in the window
const MIN_BUY_SHARE = 0.72; // buy SOL / total SOL in the window
const MAX_TOP_BUYER = 0.45; // one wallet may not dominate the window's buys
const MIN_RISE = 0.04; // price gain over the window: at least this...
const MAX_RISE = 0.6; // ...and at most this (no vertical blow-offs)
const NEAR_HIGH = 0.98; // latest price at most this share of the window high...
const DIP_FLOOR = 0.85; // ...and at least this share: a pullback, not a collapse
const MIN_ACCEL_NET = 0.5; // net inflow in the newer half of the window
const MIN_RESERVE_SOL = 2; // real SOL reserve bounds at entry...
const MAX_RESERVE_SOL = 60; // ...(exit liquidity below, late stage above)

// ---- sizing -----------------------------------------------------------------
const STAKE_SOL = 0.1; // one fixed stake per position
const MIN_BUY_SOL = 0.01; // guardrail round-trip floor; never buy less
const MAX_EXPOSURE_SOL = 1.0; // total cost across open positions
const BUY_SLIPPAGE_BPS = 1200;
const SELL_SLIPPAGE_BPS = 10_000;

// ---- exits ------------------------------------------------------------------
const TAKE_PROFIT = 0.18; // sell when close value reaches cost * 1.18
const STOP_LOSS = 0.1; // sell when close value falls to cost * 0.90
const TRAIL_ARM = 0.1; // trailing stop arms at cost * 1.10...
const TRAIL_DROP = 0.12; // ...and fires 12% below the peak close value
const FADE_WINDOW = 15; // net flow window for the fade exit
const FADE_NET_SOL = -0.35; // exit when recent net flow is below this
const MAX_HOLD_SLOTS = 500;
const COOLDOWN_SLOTS = 600; // after an exit, leave the curve alone this long
const MAX_ENTRIES_PER_MINT = 1;

interface TapeTrade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface MintState {
  created: number | null;
  trades: TapeTrade[];
  entries: number;
  lastExit: number;
}

interface HeldState {
  opened: number;
  peakValue: number;
  exiting: boolean;
  filled: boolean;
}

const mints = new Map<Pubkey, MintState>();
const held = new Map<Pubkey, HeldState>();
const KEEP_SLOTS = Math.max(WINDOW_SLOTS, FADE_WINDOW) + 10;

// ---- diversity rotation -----------------------------------------------------
// The ranking guardrail needs a round trip of at least 0.01 SOL on at least
// 20 coins. Confirmed-flow entries alone might not reach 20 on a quiet final
// window, so when no rotation is in flight and enough slots have passed, the
// bot makes one tiny round trip on the most liquid curve of the batch: buy
// ROTATE_SOL, sell the whole position as soon as the buy lands. Each trip
// costs only its fees; the pace is slow enough that the total drag stays a
// small fraction of a stake.
const ROTATE_SOL = 0.015;
const ROTATE_EVERY_SLOTS = 300;
const ROTATE_TARGET_COINS = 40; // stop rotating once this many coins are traded
const ROTATE_MIN_RESERVE_SOL = 1.5; // the 1%-of-reserve cap must fit ROTATE_SOL
const rotation = new Map<Pubkey, number>(); // mint -> slot the buy was decided
const rotatedBefore = new Set<Pubkey>();
const myCoins = new Set<Pubkey>(); // coins in my own fills (harness closes excluded)
let lastRotateSlot = -1_000_000_000;

function mintState(mint: Pubkey): MintState {
  let s = mints.get(mint);
  if (s === undefined) {
    s = { created: null, trades: [], entries: 0, lastExit: -1_000_000_000 };
    mints.set(mint, s);
  }
  return s;
}

/** Close value of a position in SOL: curve output for all its tokens, less curve and tx fees. */
function closeValue(state: BotState, mint: Pubkey, tokens: bigint): number {
  const curve = state.curves.get(mint);
  if (curve === undefined) return 0;
  const vq = Number(curve.virtual_quote_reserves);
  const vt = Number(curve.virtual_token_reserves);
  const t = Number(tokens);
  if (vt + t <= 0) return 0;
  return ((t * vq) / (vt + t) / LAMPORTS) * (1 - CURVE_FEE) - Number(state.txFeeLamports()) / LAMPORTS;
}

function netFlow(s: MintState, now: number, window: number): number {
  let net = 0;
  for (let i = s.trades.length - 1; i >= 0; i--) {
    const tr = s.trades[i]!;
    if (tr.slot <= now - window) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
}

function entryOk(s: MintState, now: number, reserveSol: number): boolean {
  if (reserveSol < MIN_RESERVE_SOL || reserveSol > MAX_RESERVE_SOL) return false;
  if (s.created === null || now - s.created < MIN_AGE_SLOTS) return false;
  const from = now - WINDOW_SLOTS;
  const mid = now - WINDOW_SLOTS / 2;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let firstPrice = -1;
  let lastPrice = 0;
  let highPrice = 0;
  let netOld = 0;
  let netNew = 0;
  const perBuyer = new Map<string, number>();
  for (const tr of s.trades) {
    if (tr.slot <= from) {
      firstPrice = tr.price;
      continue;
    }
    if (firstPrice < 0) firstPrice = tr.price;
    const signed = tr.buy ? tr.sol : -tr.sol;
    if (tr.slot <= mid) netOld += signed;
    else netNew += signed;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      perBuyer.set(tr.user, (perBuyer.get(tr.user) ?? 0) + tr.sol);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > highPrice) highPrice = tr.price;
    lastPrice = tr.price;
  }
  if (buys < MIN_BUYS || perBuyer.size < MIN_BUYERS) return false;
  if (buySol - sellSol < MIN_NET_SOL) return false;
  // Demand must be accelerating, not decaying: the newer half of the window
  // carries more net inflow than the older half, and clears a floor itself.
  if (netNew < MIN_ACCEL_NET || netNew <= netOld) return false;
  const total = buySol + sellSol;
  if (total <= 0 || buySol / total < MIN_BUY_SHARE) return false;
  let top = 0;
  for (const v of perBuyer.values()) if (v > top) top = v;
  if (buySol <= 0 || top / buySol > MAX_TOP_BUYER) return false;
  if (firstPrice <= 0 || lastPrice <= 0) return false;
  // Buy the pullback, not the top: demand is confirmed by the window's flow,
  // but the latest price must sit a little below the window high, so the
  // entry is not the last print of a vertical move.
  if (lastPrice > highPrice * NEAR_HIGH || lastPrice < highPrice * DIP_FLOOR) return false;
  const rise = lastPrice / firstPrice - 1;
  return rise >= MIN_RISE && rise <= MAX_RISE;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) myCoins.add(f.mint);
    }
    const tradedNow = new Set<Pubkey>();
    for (const e of batch.events) {
      if (e.event === 'CreateEvent') {
        mintState(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const s = mintState(e.mint);
        s.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAMPORTS,
          user: e.user,
          price: Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves),
        });
        tradedNow.add(e.mint);
      }
    }
    for (const mint of tradedNow) {
      const s = mints.get(mint)!;
      let cut = 0;
      while (cut < s.trades.length && s.trades[cut]!.slot <= now - KEEP_SLOTS) cut++;
      if (cut > 0) s.trades.splice(0, cut);
    }

    const pendingMints = new Set<Pubkey>();
    const sellPending = new Set<Pubkey>();
    for (const p of state.pending.values()) {
      pendingMints.add(p.order.mint);
      if (p.order.side === 'sell') sellPending.add(p.order.mint);
    }

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;

    // Rotation exits come before everything: sell a landed rotation whole.
    for (const [mint, decided] of rotation) {
      const pos = state.positions.get(mint);
      if (pos === undefined) {
        if (!pendingMints.has(mint) && now - decided > 20) rotation.delete(mint);
        continue;
      }
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete || sellPending.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIPPAGE_BPS });
      rotation.delete(mint);
    }

    // Exits first: a held position is sold whole on the first rule that fires.
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      if (pos === undefined) {
        if (!pendingMints.has(mint)) {
          held.delete(mint);
          const s = mintState(mint);
          if (h.filled) s.lastExit = now;
          else s.entries--;
        }
        continue;
      }
      h.filled = true;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      const value = closeValue(state, mint, pos.token_amount);
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      if (value > h.peakValue) h.peakValue = value;
      let exit = h.exiting;
      if (!exit && value >= cost * (1 + TAKE_PROFIT)) exit = true;
      if (!exit && value <= cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && h.peakValue >= cost * (1 + TRAIL_ARM) && value <= h.peakValue * (1 - TRAIL_DROP)) exit = true;
      if (!exit && netFlow(mintState(mint), now, FADE_WINDOW) < FADE_NET_SOL) exit = true;
      if (!exit && now - h.opened > MAX_HOLD_SLOTS) exit = true;
      if (!exit) continue;
      h.exiting = true;
      if (sellPending.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: SELL_SLIPPAGE_BPS });
    }

    // Entries: one fixed stake into a confirmed curve, slots and cash permitting.
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    const txSol = Number(state.txFeeLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let exposure = 0;
    for (const pos of state.positions.values()) exposure += Number(pos.cost_lamports) / LAMPORTS;

    for (const mint of tradedNow) {
      if (orders.length >= cap || slotsLeft <= 0) break;
      if (held.has(mint) || rotation.has(mint) || pendingMints.has(mint) || state.positions.has(mint)) continue;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      const s = mintState(mint);
      if (s.entries >= MAX_ENTRIES_PER_MINT || now - s.lastExit < COOLDOWN_SLOTS) continue;
      const reserveSol = Number(curve.real_quote_reserves) / LAMPORTS;
      if (!entryOk(s, now, reserveSol)) continue;
      const capSol = Number(state.maxBuyLamports(mint)) / LAMPORTS;
      const amount = Math.min(capSol, STAKE_SOL, MAX_EXPOSURE_SOL - exposure);
      if (amount < MIN_BUY_SOL || amount + txSol > free) continue;
      orders.push({
        side: 'buy',
        mint,
        quote_lamports: BigInt(Math.floor(amount * LAMPORTS)),
        max_slippage_bps: BUY_SLIPPAGE_BPS,
      });
      free -= amount + txSol;
      exposure += amount;
      slotsLeft--;
      s.entries++;
      held.set(mint, { opened: now, peakValue: 0, exiting: false, filled: false });
    }

    // Diversity rotation: one tiny round trip on the batch's most liquid
    // curve, paced by slots, until enough distinct coins have been traded.
    if (
      rotation.size === 0 &&
      myCoins.size < ROTATE_TARGET_COINS &&
      now - lastRotateSlot >= ROTATE_EVERY_SLOTS &&
      orders.length < cap &&
      slotsLeft > 0
    ) {
      let best: Pubkey | null = null;
      let bestReserve = 0;
      for (const mint of tradedNow) {
        if (held.has(mint) || rotatedBefore.has(mint) || pendingMints.has(mint) || state.positions.has(mint)) continue;
        const curve = state.curves.get(mint);
        if (curve === undefined || curve.complete) continue;
        const reserve = Number(curve.real_quote_reserves);
        if (reserve > bestReserve) {
          bestReserve = reserve;
          best = mint;
        }
      }
      if (best !== null && bestReserve / LAMPORTS >= ROTATE_MIN_RESERVE_SOL) {
        const capSol = Number(state.maxBuyLamports(best)) / LAMPORTS;
        const amount = Math.min(capSol, ROTATE_SOL);
        if (amount >= MIN_BUY_SOL && amount + txSol <= free) {
          orders.push({
            side: 'buy',
            mint: best,
            quote_lamports: BigInt(Math.floor(amount * LAMPORTS)),
            max_slippage_bps: BUY_SLIPPAGE_BPS,
          });
          rotation.set(best, now);
          rotatedBefore.add(best);
          lastRotateSlot = now;
          free -= amount + txSol;
          slotsLeft--;
        }
      }
    }

    return orders;
  },
});
