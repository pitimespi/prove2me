# Spot 23: `GetBlockSubsidy` versus `BitcoinSubsidy.coreSubsidy`, `specSubsidy`, `issuedBelow`, `intervalSum`, `zeroHeight`

Core: [`validation.cpp:1833`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833)
(`GetBlockSubsidy`), [`validation.cpp:2608`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2608)
(its consensus use in `ConnectBlock`: `blockReward = nFees + GetBlockSubsidy(pindex->nHeight, …)`,
`bad-cb-amount`), [`consensus/amount.h:12`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h#L12)
(`CAmount = int64_t`, `COIN = 100'000'000`, `MAX_MONEY = 21'000'000 * COIN`),
[`kernel/chainparams.cpp:114`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp#L114)
(`CMainParams`: `consensus.nSubsidyHalvingInterval = 210000`).

Lean: `Definitions/Def_BitcoinSubsidy.lean` (38 lines): `COIN`, `MAX_MONEY`, `halvingInterval`,
`coreSubsidy`, `specSubsidy`, `issuedBelow`, `intervalSum`, `zeroHeight`.

## Verdict

No defect. `coreSubsidy` is `GetBlockSubsidy` at mainnet parameters, test for test: `halvings =
height / 210000`, early `0` when `64 ≤ halvings`, otherwise `50 * COIN >>> halvings`; the constants
`COIN = 100000000`, `MAX_MONEY = 21000000 * COIN` and `halvingInterval = 210000` match
`amount.h` and `CMainParams`. `specSubsidy height = (50 * COIN) / 2 ^ (height / halvingInterval)`
is `floor(50e8 / 2^halvings)` with no 64 branch; it agrees with `coreSubsidy` at every height
because `2^33 > 50e8` makes the quotient zero from halving 33 on, long before the branch at 64
(the vectors check both functions at every listed height including 13439999, 13440000 and
13440001). The read-back (`scratchpad/audit2/readback_Def_BitcoinSubsidy.md`), written blind,
describes exactly this (two-way split at 64, truncating shift, `specSubsidy` without the split,
`issuedBelow n` the sum over heights `0..n-1` of `coreSubsidy`). The total issuance computed in
Python from the C++ is `2099999997690000` satoshi (20,999,999.9769 BTC, `MAX_MONEY − 2,310,000`),
which is the constant in `Thm_BitcoinSubsidy_issuance_total` (`issuedBelow zeroHeight =
2099999997690000`) and `issuance_le_total`, and `intervalSum 33 * halvingInterval` evaluates to it.

## `GetBlockSubsidy(nHeight, params)` — `coreSubsidy height`

Core (`validation.cpp:1833-1844`):

1. `int halvings = nHeight / consensusParams.nSubsidyHalvingInterval;` — `int / int`, truncating
   toward zero; `nHeight` is a block height (`pindex->nHeight`, non-negative on the validation
   path), `nSubsidyHalvingInterval = 210000` on mainnet.
2. `if (halvings >= 64) return 0;` — "Force block reward to zero when right shift is undefined"
   (shifting an `int64_t` by 64 or more is UB).
3. `CAmount nSubsidy = 50 * COIN;` — `int64_t` 5,000,000,000.
4. `nSubsidy >>= halvings;` — arithmetic right shift of a positive `int64_t` by `0..63` bits,
   which is floor division by `2^halvings`.
5. `return nSubsidy;`

Lean:

- `coreSubsidy height := let halvings := height / halvingInterval; if 64 ≤ halvings then 0 else
  (50 * COIN) >>> halvings` — step 1 with `Nat` floor division (equal to C++ truncation for
  non-negative heights); step 2 as `64 ≤ halvings` ≡ `halvings >= 64`; steps 3-5 as
  `Nat.shiftRight`, which is floor division by `2^halvings` and agrees with the C++ shift on a
  positive value. The `Nat` height is unbounded, whereas `nHeight` is `int`; heights ≥ 2^31 are not
  reachable by a chain Core could hold (`nHeight` is an `int` everywhere), and at such heights both
  sides give 0 anyway (vector at `2^31 − 1`).
- `specSubsidy height := (50 * COIN) / 2 ^ (height / halvingInterval)` — the declarative
  `floor(50e8 / 2^halvings)`; identical to `coreSubsidy` for all `Nat` heights: for `halvings ≤ 63`
  the shift equals the division, for `halvings ≥ 64` the division of 5e9 by `2^halvings ≥ 2^64` is 0.
- `issuedBelow n = Σ_{h < n} coreSubsidy h`, `intervalSum m = Σ_{j < m} (50 * COIN) / 2^j`,
  `zeroHeight = 33 * halvingInterval = 6930000`. These are the theorem-side helpers; the sum uses
  `coreSubsidy` (the C++ function), not `specSubsidy`.

Boundary values (Python from the C++, matched by both Lean functions): heights 0, 1, 209999 →
5,000,000,000; 210000, 210001, 419999 → 2,500,000,000; 420000 → 1,250,000,000; 630000 →
625,000,000; 840000 → 312,500,000; 1050000 → 156,250,000; 6719999 → 2; 6720000 (halving 32) → 1
(`5e9 >> 32 = 1`, since 2^32 = 4,294,967,296 ≤ 5e9 < 2^33); 6929999 → 1; 6930000 (halving 33) →
0 by truncation; 13439999 (halving 63) → 0; 13440000 (halving 64) → 0 by the early return;
13440001 → 0. The subsidy is non-zero for exactly halvings 0..32 (33 intervals) and zero for
33..63 and beyond, as the vector over `List.range 64` confirms.

Total issuance: `Σ_{k=0}^{32} 210000 · (5e9 >> k) = 2099999997690000`, cross-checked in Python by a
brute-force sum over the first two intervals. No Lean function computes the grand total as a
closed term usable by `#eval` other than through `issuedBelow zeroHeight`, which is a 6.93-million
step non-tail recursion and was not evaluated; instead `intervalSum 33 * halvingInterval` and
`intervalSum 64 * halvingInterval` are both checked to equal the Python total, and `issuedBelow`
is checked on small prefixes (0, 1, 2, 1000) against brute-force sums. The gap to `MAX_MONEY` is
2,310,000 satoshi; `issuance_bound` (`issuedBelow n < MAX_MONEY`) is consistent with it.

## Vectors

`tests/SubsidyVectors.lean` (93 `#eval` lines, all `true`), generated by
`tests/reference/subsidy_reference.py`: the four constants; `coreSubsidy` and `specSubsidy` at the
23 boundary heights above (including `2^31 − 1`); `coreSubsidy (k * halvingInterval)` for
`k = 0..33`; the non-zero pattern over 64 halvings; the total issuance via `intervalSum`;
`issuedBelow` on small prefixes.

Run: `lake env lean tests/SubsidyVectors.lean | sort | uniq -c` → `93 true`.

## Checks from the guide

- **Order of tests.** Core computes `halvings`, tests `>= 64`, then shifts; the Lean does the
  same. The order is the only thing that avoids the undefined shift, and it is preserved.
- **Constants.** `210000` (`CMainParams`, line 114; testnet/signet also 210000, regtest 150 — not
  modelled), `COIN = 100000000`, `50 * COIN`, `64`, `MAX_MONEY = 21000000 * COIN`: all match.
- **Integer semantics.** `int` division truncating toward zero equals `Nat` floor division on
  non-negative heights; `int64_t >>` on the positive value `5e9` equals `Nat.shiftRight`; no
  overflow is possible (`50 * COIN < 2^63`, and the shift only shrinks it); the `64` guard removes
  the undefined shift exactly as in Core. `Nat` heights beyond `int` range are an accepted limit and
  give 0 on both sides.
- **Defaults.** No `headD`/`getD`; division is by the non-zero constant `210000` and by
  `2^k ≥ 1`, so the `Nat` `x / 0 = 0` convention is never exercised.
- **Policy vs consensus.** `GetBlockSubsidy` is consensus (it bounds the coinbase value in
  `ConnectBlock`); nothing from policy is present.
