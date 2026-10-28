# Spot 15: proof-of-work arithmetic versus `BitcoinPow.setCompact`, `getCompact`, `deriveTarget`, `checkProofOfWork`, `clampTimespan`, `calculateNextWork`, `nextWorkRequired`, `permittedTransition`, and `BitcoinBlockV2.blockProof`

Core: [`arith_uint256.cpp:176`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp#L176)
(`arith_uint256::SetCompact`), [`:196`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp#L196)
(`arith_uint256::GetCompact`), [`:14`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp#L14)
(`operator<<=`), [`:47`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp#L47)
(`operator*=(uint32_t)`), [`:75`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp#L75)
(`operator/=`), [`pow.cpp:14`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L14)
(`GetNextWorkRequired`), [`:50`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L50)
(`CalculateNextWorkRequired`), [`:89`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L89)
(`PermittedDifficultyTransition`), [`:140`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L140)
(`CheckProofOfWork`), [`:146`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L146)
(`DeriveTarget`), [`:161`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L161)
(`CheckProofOfWorkImpl`), [`chain.cpp:120`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.cpp#L120)
(`GetBitsProof`, which `GetBlockProof` in `chain.h:305` forwards to), [`kernel/chainparams.cpp:126`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp#L126)
(`CMainParams`: `powLimit`, `nPowTargetTimespan`, `nPowTargetSpacing`, `fPowAllowMinDifficultyBlocks`, `enforce_BIP94`, `fPowNoRetargeting`),
[`consensus/params.h:130`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/params.h#L130)
(`DifficultyAdjustmentInterval`), [`validation.cpp:3839`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L3839)
and [`:4096`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L4096)
(the consensus call sites: `CheckBlockHeader` and `ContextualCheckBlockHeader`'s `bad-diffbits`).

## Verdict

No consensus defect. `setCompact`, `getCompact`, `deriveTarget`, `checkProofOfWork`,
`clampTimespan`, `calculateNextWork`, `nextWorkRequired` and `permittedTransition` agree with Core
test for test, constant for constant, including the 256-bit wraparound of `bnNew *= nActualTimespan`,
the rounding of `GetCompact`, and the three overflow boundaries of `SetCompact`. The mainnet
parameters (`powLimit = 2^224 - 1`, timespan 1,209,600, spacing 600, interval 2016,
`fPowAllowMinDifficultyBlocks = fPowNoRetargeting = enforce_BIP94 = false`) match
`kernel/chainparams.cpp:126-131`. The read-back describes the Lean exactly as Core reads.

Two differences that do not change any verdict, recorded for completeness:

**D1 (`blockProof`, no verdict impact).** Core's `GetBitsProof` returns 0 only for a negative,
overflowing or zero target; it has *no* `powLimit` test. The Lean `BitcoinBlockV2.blockProof` goes
through `deriveTarget`, which also returns `none` above `powLimit`, so for a non-negative,
non-overflowing nBits whose target exceeds `powLimit` the two differ: `GetBitsProof(0x1e00ffff) =
0x1000100`, `GetBitsProof(0x2000ffff) = 0x100`, `GetBitsProof(0x21000001) = 0xffff`, while
`blockProof` gives 0 for all three (model's work smaller than Core's). This is unreachable in the
model: `blockProof` is only summed by `ChainState.chainWork` over `S.headers`, every one of which
(the genesis, or a header accepted by `validate`) has passed `checkHeaderPow`, which requires
`deriveTarget ≠ none`; and chain work is not a block-validity rule in Core either (it drives fork
choice and the headers anti-DoS, neither modelled). The three cases are in `tests/PowVectors.lean`
as comments (they would print `false`).

**D2 (`compactNegative`, no verdict impact).** In `SetCompact`, for `nSize <= 3` the C++ shifts
`nWord` in place *before* computing `*pfNegative = nWord != 0 && ...`, so a mantissa whose
significant bytes are shifted out (e.g. `0x01803456`: `0x003456 >> 16 = 0`) gives
`fNegative = false`. The Lean `compactNegative` tests the *unshifted* 23-bit word, so it is `true`
there. The difference arises only when the shifted word is 0, i.e. when the target is 0, and every
consumer (`DeriveTarget`, `GetBitsProof`, the `HeaderSpec` conjunction with `0 < specTarget`)
rejects on the zero target regardless of the flag. `compactOverflow` is unaffected (its conditions
need `nSize > 32`, where no shift happens).

## `arith_uint256::SetCompact` — `setCompact`, `compactNegative`, `compactOverflow`

Core: `nSize = nCompact >> 24` (0..255); `nWord = nCompact & 0x007fffff`; if `nSize <= 3`:
`nWord >>= 8 * (3 - nSize)` (a `uint32_t` shift by 0/8/16/24), value `= nWord`; else value `= nWord
<<= 8 * (nSize - 3)` with `operator<<=` discarding every bit shifted past word 7 (shift up to
2016 bits; `i + k < WIDTH` guards), i.e. the value is `nWord * 2^(8(nSize-3)) mod 2^256`;
`fNegative = nWord != 0 && (nCompact & 0x00800000) != 0`; `fOverflow = nWord != 0 && (nSize > 34
|| (nWord > 0xff && nSize > 33) || (nWord > 0xffff && nSize > 32))`.

The Lean: `compactSize c = (c >>> 24).toNat`, `compactWord c = (c &&& 0x007fffff).toNat`;
`setCompact` is `nWord >>> (8 * (3 - nSize))` for `nSize ≤ 3`, else `(nWord <<< (8 * (nSize -
3))) % width` with `width = 2^256`: identical to the word loop (a shift of 233..255 bits keeps the
low bits of the mantissa, 256 or more gives 0; the vectors `0x2100ffff → 0xffff << 240`,
`0x21010000 → 0` (the `0x010000` is shifted out, and the overflow flag is set) and `0x23000001 → 0`
exercise this). `compactOverflow` is the same
three-clause disjunction with the same strict comparisons. `compactNegative` differs only as in D2.

Vectors: `0x00000000` (0), `0x00123456` (0), `0x01003456` (0), `0x01123456` (0x12), `0x02123456`
(0x1234), `0x03123456` (0x123456), `0x04123456` (0x12345600), `0x02008000` (0x80), `0x05009234`
(0x92340000), `0x20123456`, `0x1d00ffff` (`0xffff << 208`), `0x1e00ffff`, `0x207fffff`,
`0x2100ffff` (not overflowing), `0x21010000` (overflowing: `nWord > 0xffff`, `nSize > 32`),
`0x21000001`, `0x220000ff` (not overflowing), `0x22000100` (overflowing), `0x22000001`,
`0x23000000` (zero word: no flags, value 0), `0x23000001` (overflowing, `nSize > 34`),
`0x04923456` (negative), `0x20800000` (sign bit with zero word: not negative), `0xff123456`,
`0xff000000`, the real `0x1b0404cb` and `0x1d00d86a`: value and both flags on each.

## `arith_uint256::GetCompact` — `getCompact`

Core (`fNegative = false` at every consensus call): `nSize = CeilDiv(bits(), 8u)` where `bits()`
is the position of the highest set bit plus one (0 for 0); `nSize <= 3`: `nCompact = GetLow64()
<< 8 * (3 - nSize)` truncated to `uint32_t`; else `nCompact = (*this >> 8 * (nSize - 3)).GetLow64()`
truncated to `uint32_t`; if `nCompact & 0x00800000`: `nCompact >>= 8; nSize++`; `nCompact |= nSize
<< 24`. `CeilDiv` lives in `util/overflow.h`, which is not in the cache; the vectors
(`GetCompact(0x1234) = 0x02123400`, `GetCompact(powLimit) = 0x1d00ffff`, the known
`nProofOfWorkLimit`) pin it to ceiling division.

The Lean: `bitLength v = Nat.log2 v + 1` (0 for 0), `nSize = (bitLength v + 7) / 8`, the two
branches with the `% 2^64` and `% 2^32` reductions (identities for `v < 2^256`, as the read-back
notes), the `0x00800000` adjustment, `BitVec.ofNat 32 (nCompact' ||| (nSize' <<< 24))`. Identical.

Vectors: 0 → `0x00000000`; 1 → `0x01010000`; `0x80` → `0x02008000` (rounding); `0x1234` →
`0x02123400`; `0x8000` → `0x03008000` (`nSize = 2`, `nCompact = 0x800000`, bit 23 set, so the
mantissa is divided by 256 and the exponent incremented); `0x7fffff` → `0x037fffff`; `0x800000` → `0x04008000`; `0xffffff` →
`0x0400ffff`; `0x12345678` → `0x04123456`; `2^255` → `0x21008000`; `2^256 - 1` → `0x2100ffff`;
`powLimit` → `0x1d00ffff`; `0xffff << 208` → `0x1d00ffff`; `0x3fffc0 << 208` → `0x1c3fffc0`;
round trips `setCompact (getCompact powLimit) = 0xffff << 208` (powLimit itself is not
representable) and `getCompact (setCompact 0x1d00ffff) = 0x1d00ffff`.

## `DeriveTarget`, `CheckProofOfWorkImpl` — `deriveTarget`, `checkProofOfWork`

Core: `CheckProofOfWork` is `CheckProofOfWorkImpl` outside fuzzing. `DeriveTarget`: `SetCompact`
with both flags, then `fNegative || bnTarget == 0 || fOverflow || bnTarget > powLimit` → empty.
`CheckProofOfWorkImpl`: empty target → false; `UintToArith256(hash) > bnTarget` → false; else
true. `UintToArith256` reads the 32 bytes as eight little-endian words, i.e. the little-endian
integer value of the hash.

The Lean: `deriveTarget` is the same four-way disjunction in the same order on `setCompact`,
`compactNegative`, `compactOverflow` and `powLimit < t`; `checkProofOfWork hash nBits` is `false`
on `none` and `hash ≤ t` on `some t`. `BitcoinBlockV2.checkHeaderPow` feeds `hashValue h = leVal
(headerHash h)`, the little-endian value. Identical. The `HeaderSpec` predicate's specification
form (`specTarget`, the untruncated value) accepts the same `(hash, nBits)`: `specTarget =
setCompact` whenever `nSize ≤ 32` (the mantissa is below `2^23` and the shift at most 232 bits), and
for `nSize ≥ 33` with a non-zero word either `compactOverflow` holds (`nSize ≥ 35`, or `nSize = 34`
with a word above `0xff`, or `nSize = 33` with a word above `0xffff`) or both values are at least
`2^240 > powLimit`.

Vectors: `deriveTarget` on `0x1d00ffff` (some `0xffff << 208`), `0x1e00ffff` (none, above
`powLimit`), `0x1d01ffff` (none), `0x04923456` (none, negative), `0x00000000` and `0x23000000`
(none, zero), `0x21000001` (none, above `powLimit` though not overflowing), `0x2100ffff` (none),
`0x1b0404cb` (some); `checkProofOfWork` with the hash equal to, one below and one above the target
for `0x1d00ffff` and `0x1b0404cb`, hash 0 against `0x1d00ffff` (true) and against the five invalid
words (false), `hash = powLimit` against `0x1d00ffff` (false: the decoded target is `0xffff <<
208 < powLimit`), and `hash = 2^256 - 1` (false).

## `CalculateNextWorkRequired` — `clampTimespan`, `calculateNextWork`

Core: `fPowNoRetargeting` (false on mainnet) → return `nBits`; `nActualTimespan =
pindexLast->GetBlockTime() - nFirstBlockTime` (`int64_t`); `< nPowTargetTimespan/4` → `302400`;
`> nPowTargetTimespan*4` → `4838400`; `bnNew.SetCompact(pindexLast->nBits)` (`enforce_BIP94`
false, flags ignored); `bnNew *= nActualTimespan`: the `int64_t` argument selects
`operator*=(uint32_t)` (a standard integral conversion beats the user-defined conversion to
`base_uint`), the clamped value fits in 32 bits, and the loop drops the final carry, so the product
is taken modulo `2^256`; `bnNew /= nPowTargetTimespan` is exact integer division (`operator/=`);
`bnNew > bnPowLimit → bnNew = bnPowLimit`; `return bnNew.GetCompact()`.

The Lean: `clampTimespan (lastTime - firstTime)` on `Int`, with `lo = 302400`, `hi = 4838400`
(`1209600 / 4` is exact), the two tests in Core's order; `.toNat` (the clamp is positive, so
exact); `(setCompact lastBits * ts) % width`; `/ targetTimespan`; cap at `powLimit`; `getCompact`.
Identical. No validity test on `lastBits`, as in Core (`0x00000000` and `0x04923456` as `lastBits`
give `0x00000000` and the decoded positive value respectively, in both). On the validation path
the product never wraps (`powLimit * 4838400 < 2^247`); the wrap is reachable only through a
last target above `powLimit`, which `CheckProofOfWork` excludes, but the Lean transcribes it
anyway and the vectors confirm it.

Vectors: the two real mainnet retargets (times fetched from blockstream.info and mempool.space
on 2026-10-28, not from the repository: block 0 time 1231006505, block 2015 time 1233061996 →
block 2016 bits `0x1d00ffff`, the `powLimit` cap; block 30240 (hash
`000000000fa8bfa0f0dd32f956b874b2c7f1772c5fbedcb1b35e03335c7fb0a8`) time 1261130161, block 32255
(hash `00000000984f962134a7291e3693075ae03e521f0ee33378ec30a334d860034b`) time 1262152739 →
block 32256 bits `0x1d00d86a`, the reference computing `0xffff·1022578/1209600 = 55402 = 0xd86a`);
the two mid-range clamp cases `0x1c05a3f4` (times 1279008237, 1279297671) and `0x1c387f6f`
(1263163443, 1269211443); from `0x1b0404cb`: timespans 100, −100, 302399, 302400, 302401,
1209600, 4838399, 4838400, 4838401 and `10^9` (the clamp at both ends, exactly on both boundaries
and one second either side); the cap: `0x1d00ffff` × 4, `0x1d00ffff` × 1209601/1209600,
`0x1c3fffc0` × 4 (exactly `0xffff << 208`, not capped), `0x1c3fffc1` × 4 (above `0xffff << 208`
but below `powLimit`: capped only by `GetCompact`'s rounding to `0x1d00ffff`), `0x1c7fffff` × 4
(capped); wraparound: `0x21008000` (`2^255`) × 4838400 → `2^255 · 4838400 mod 2^256 = 0` → bits
`0x00000000` (un-wrapped arithmetic would give the cap `0x1d00ffff`; the reference asserts this),
`0x21008000` × 302401 (odd: `2^255` survives → cap), `0x2100ffff` × 4838400 and × 1209600 (wrap,
then cap), `0x2000ffff` × 4, `0x20ffffff` × 302400 (the sign bit is ignored by `SetCompact`).

## `GetNextWorkRequired` — `nextWorkRequired`, `ChainState.requiredBits`

Core: `(pindexLast->nHeight + 1) % DifficultyAdjustmentInterval() != 0` → return
`pindexLast->nBits` (the `fPowAllowMinDifficultyBlocks` branch is testnet-only; mainnet is
`false`, `chainparams.cpp:129`); else `nHeightFirst = nHeight - (2016 - 1)`, `pindexFirst =
GetAncestor(nHeightFirst)`, `CalculateNextWorkRequired(pindexLast, pindexFirst->GetBlockTime())`.
`ContextualCheckBlockHeader` compares `block.nBits != GetNextWorkRequired(...)` as 32-bit words.

The Lean: `nextWorkRequired lastHeight lastBits lastTime firstTime` with the same `(lastHeight +
1) % 2016 ≠ 0 → lastBits` test; `BitcoinBlockV2.requiredBits` supplies `firstTime` as
`(S.headers.getD (S.tipHeight - 2015) genesisHeader).time`, `headers` being indexed by height.
The `Nat` subtraction truncates only when `tipHeight < 2015`, where `(tipHeight + 1) % 2016 ≠ 0`
and the time is unused; otherwise `tipHeight - 2015 ≤ tipHeight < length`, so the `getD` default
is unreachable. `HeaderSpec` compares `BitVec.ofNat 32 h.bits = S.requiredBits` bit for bit, as
Core. Identical.

Vectors: heights 2015 and 32255 (retarget, real data), 32254 and 32256 and 2014 and 0 (no
retarget, `lastBits` returned whatever the times), 4031 (retarget with the lower clamp), 100 with
a negative `lastBits` returned unchanged.

## `PermittedDifficultyTransition` — `permittedTransition`

Core: `fPowAllowMinDifficultyBlocks → true` (not mainnet); `height % 2016 == 0`: `observed =
SetCompact(new)`; `largest = SetCompact(old) * 4838400 / 1209600` (same `uint32_t` overload,
modular), capped at `powLimit`, `maximum = SetCompact(GetCompact(largest))`, `maximum < observed
→ false`; `smallest = SetCompact(old) * 302400 / 1209600`, capped, `minimum =
SetCompact(GetCompact(smallest))`, `minimum > observed → false`; else branch: `old != new →
false`; `true`. The Lean is the same computation and the same two comparisons, `decide (oldBits =
newBits)` on the words in the other branch. Identical. This function is not called anywhere in
the cached `validation.cpp`: it serves the headers pre-synchronisation anti-DoS in
`net_processing`/`headerssync` (not cached), so it is not a mainnet consensus rule; the Lean
defines it but `BitcoinBlockV2` does not use it, which is the correct placement.

Vectors: `(32256, 0x1d00ffff, 0x1d00d86a)` true; at 2016 from `0x1d00ffff`: `0x1d00ffff` and
`0x1c3fffc0` (exactly a quarter) and `0x1c3fffc1` true, `0x1e00ffff` and `0x1c3fffbf` false;
height 0 is a boundary; from `0x1b0404cb`: `0x1b010132` (minimum) true, `0x1b010131` false,
`0x1b10132c` (maximum) true, `0x1b10132d` false; off-boundary heights: equal words true, different
words false, a negative word equal to itself true.

## `GetBitsProof` — `BitcoinBlockV2.blockProof`

Core: `SetCompact(bits)` with flags; `fNegative || fOverflow || bnTarget == 0 → 0`; else
`~bnTarget / (bnTarget + 1) + 1` on `arith_uint256` (`bnTarget + 1` cannot wrap: the largest
`SetCompact` value is `0xffff << 240`; the quotient is below `2^255`, so `+ 1` cannot wrap).

The Lean: `0` on `deriveTarget = none`, else `(width - 1 - t) / (t + 1) + 1`, which is `~t / (t +
1) + 1` on `Nat` since `t < 2^256`. Identical on every target at most `powLimit`; see D1 for
targets above it (Lean 0, Core positive), unreachable from a validated header.

Vectors: `0x1d00ffff → 0x100010001` (the genesis chain work), `0x1b0404cb → 0x3fb3ab764c00`,
`0x1d00d86a → 0x12ed3afd2`, `0x03000001 → 2^255`, and 0 for `0x00000000`, `0x04923456`,
`0x21010000`, `0xff123456`, `0x01803456`; the three D1 cases as comments.

## Vectors

`tests/PowVectors.lean` (205 `#eval` lines, all `true`; `sort | uniq -c` of the output: `205
true`), generated by `tests/reference/pow_reference.py`, an independent Python transcription of
the C++ with `arith_uint256` modelled as an integer below `2^256` and the same carry-dropping
`operator<<=` / `operator*=(uint32_t)`. The vectors import `Definitions.Def_BitcoinPow` and
`Definitions.Def_BitcoinBlockV2` (for `blockProof`). The real-chain inputs (block times and bits
at heights 0, 2015, 2016, 30240, 32255, 32256) were fetched from public explorers during the
review and are quoted in the reference; they are not in the repository's own data.

## Checks from the guide

- **Order of tests.** `DeriveTarget`'s four tests, the two clamp tests, the cap after the
  division, `GetCompact`'s rounding before the exponent is ORed in, and the two
  `PermittedDifficultyTransition` comparisons are all in Core's order; every result is a value or
  a `Bool`, so order only matters where it changes the value, and it does not.
- **Constants.** `0x007fffff`, `0x00800000`, the 24-bit exponent shift, 34/33/32 with
  `0xff`/`0xffff`, `powLimit = 00000000ffff…ff`, 1,209,600, 600, 2016, the quarter and quadruple
  clamps, the 8-bit mantissa adjustment: all match.
- **Integer semantics.** `nActualTimespan` is a signed `int64_t` difference, modelled on `Int`
  (negative differences clamp up, as in Core); the product is modulo `2^256` (carry dropped) and
  the Lean reduces modulo `width`; the division is exact in both; `SetCompact`'s left shift drops
  bits past 256 in both; the `uint32_t` truncations in `GetCompact` are identities on the
  reachable range and are transcribed anyway; `compactSize` is 0..255 like `nCompact >> 24`.
- **Defaults.** `Nat` subtraction appears in `3 - nSize` (guarded by `nSize ≤ 3`), `nSize - 3`
  (guarded), `width - 1 - t` (`t < 2^256`), `tipHeight - 2015` (unused when it truncates);
  `getD genesisHeader` in `requiredBits` is unreachable; `Int.toNat` of the clamp is exact; the
  division by `targetTimespan` and by `t + 1` are by non-zero constants. `calculateNextWork` on a
  degenerate `lastBits` mirrors Core, which performs no check there either.
- **Policy vs consensus.** `CheckProofOfWork` (`CheckBlockHeader`) and `GetNextWorkRequired`
  (`bad-diffbits`) are the consensus rules and are what `BitcoinBlockV2` uses. The testnet
  min-difficulty rule, `fPowNoRetargeting`, `enforce_BIP94` (testnet4) and the fuzz shortcut are
  correctly absent. `PermittedDifficultyTransition` and `GetBlockProof`/`nChainWork` are anti-DoS
  and fork-choice machinery, not block validity; the Lean defines them without making them rules
  (D1 is confined to `blockProof`).
