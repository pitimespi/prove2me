# Spot 14: `AcceptBlockHeader` / `ContextualCheckBlockHeader`, `GetNextWorkRequired`, `GetMedianTimePast` versus `BitcoinBlockV2.acceptHeader`, `ChainState.requiredBits`, `ChainState.mtp`

Core: [`validation.cpp:4088`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L4088)
(`ContextualCheckBlockHeader`), [`:4188`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L4188)
(`ChainstateManager::AcceptBlockHeader`), [`:3836`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L3836)
(`CheckBlockHeader`), [`pow.cpp:14`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L14)
(`GetNextWorkRequired`), [`chain.h:233`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h#L233)
(`GetMedianTimePast`, `nMedianTimeSpan = 11`), [`chain.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.cpp)
(`GetBlockProof`).

## Verdict

No defect. The outcomes and their order, the retarget ancestor, the median window and the version
floors agree with Core at mainnet parameters. The read-back (`readback_Def_BitcoinBlockV2.md`,
sections `ChainState` and `AcceptBlockHeader`) describes the Lean as Core reads. The Header
mission's `BitcoinHeader.contextualCheck` is the same four tests, and `acceptHeader_iff` (proved)
ties `acceptHeader` to it.

Vectors: `tests/HeaderPathVectors.lean` (43 lines, all `true`): the real block-170 header against
the real 170-header state (accept; `now + 7200` boundary; `futureTime`; `missingPrev` with the
tip at 168, taking precedence over the clock; a tampered nonce `invalid` before the clock), a
2016-header state whose tip is block 169 (so the next block is at a retarget boundary: the first
block of the period is `headers[0]`, a synthetic header whose time sets the actual timespan:
exactly two weeks keeps `0x1d00ffff`; zero clamps to 3.5 days and quarters the target to
`0x1c3fffc0`, which makes the real header `invalid` for `bad-diffbits` ahead of the clock; eight
weeks clamps to 4× and is capped at `powLimit`; three weeks also exceeds `powLimit`; one week halves
the target to `0x1c7fff80`), a 2015-header state (not at a boundary: the tip's bits), the MTP on
synthetic windows (empty, one, two, three, eleven, fourteen elements, ties on both sides of the
median) and twelve version/height pairs on the three floors. My first hand expectation for the
three-week case forgot the `powLimit` cap; the Lean applied it, as Core does.

## `AcceptBlockHeader` then `ContextualCheckBlockHeader` — `acceptHeader`

Core, in order: `CheckBlockHeader` (= `CheckProofOfWork(hash, nBits)`, `BLOCK_INVALID_HEADER`);
previous block lookup (`prev-blk-not-found`: the header is not stored, not marked invalid); the
previous block invalid (`bad-prevblk`, unreachable in a linear chain of accepted headers);
`ContextualCheckBlockHeader`: `nBits != GetNextWorkRequired(pindexPrev)` (`bad-diffbits`);
`GetBlockTime() <= pindexPrev->GetMedianTimePast()` (`time-too-old`); BIP94 timewarp (testnet4 and
regtest only: `enforce_BIP94` is false on mainnet, limit L8); `block.Time() > NodeClock::now() +
MAX_FUTURE_BLOCK_TIME` (`BLOCK_TIME_FUTURE`, transient); the version floors (`nVersion < 2` with
BIP34 active for this height, `< 3` with BIP66, `< 4` with BIP65).

The Lean: `!checkHeaderPow h → .invalid`; `h.prevBlock ≠ S.tipHash → .missingPrev`; `h.bits ≠
S.requiredBits → .invalid`; `h.time ≤ S.mtp → .invalid`; `now + 7200 < h.time → .futureTime`;
`versionOutdated h.version S.tipHeight → .invalid`; else accept. Same tests, same order, and here
the order carries meaning because the outcomes differ (`futureTime` is the transient one): a bad
nonce or bad bits is `invalid` even when the time is also in the future, and a missing parent is
`missingPrev` whatever the time, as in Core. The `≤` of `time-too-old` and the `>` of
`time-too-new` are transcribed with the boundary values (`time = MTP` rejected, `time = now + 7200`
accepted). `MAX_FUTURE_BLOCK_TIME = 7200`. `NodeClock::now()` is the local clock in this revision
(network-adjusted time was removed before it), which is the model's `now`.

## `GetNextWorkRequired` — `ChainState.requiredBits`

Core: `(pindexLast->nHeight + 1) % 2016 ≠ 0 → pindexLast->nBits` (the `fPowAllowMinDifficultyBlocks`
branch is testnet only: false in `CMainParams`); else `nHeightFirst = nHeight − 2015`, `pindexFirst =
GetAncestor(nHeightFirst)`, `CalculateNextWorkRequired(pindexLast, pindexFirst->GetBlockTime())`.
`DifficultyAdjustmentInterval = nPowTargetTimespan / nPowTargetSpacing = 1209600 / 600 = 2016`.

The Lean: `first := headers.getD (tipHeight − 2015) genesisHeader`; `nextWorkRequired tipHeight
tip.bits tip.time first.time` with `nextWorkRequired` = the modulus test then `calculateNextWork`
(spot 15). `headers[i]` is the ancestor at height `i` because the chain is linear with the genesis
at index 0. The truncated subtraction and the `getD` default only act when `tipHeight < 2015`, where
the modulus test has already returned the tip's bits (the first boundary is `tipHeight = 2015`).
Identical at mainnet parameters.

## `GetMedianTimePast` — `ChainState.mtp`, `BitcoinHeader.medianTimePast`

Core: collect the times of the block and up to 10 ancestors (fewer near genesis), sort, return
`pbegin[(pend − pbegin) / 2]`, i.e. the element at index `size / 2` of the sorted window.

The Lean: `timesTo h` = the times of heights `0..h` most recent first; `medianTimePast` takes the
first 11 (`timeWindow`), merge-sorts ascending, and returns index `length / 2` (default 0 on an empty
window, which the chain never presents: the genesis header is always there). `S.mtp = mtpAt tipHeight`
is `pindexPrev->GetMedianTimePast()`. Identical (two elements → the larger; the ties vector shows the
index-5-of-11 rule).

## Version floors — `BitcoinHeader.versionOutdated`

`version < 2 ∧ 227931 ≤ prev + 1`, `version < 3 ∧ 363725 ≤ prev + 1`, `version < 4 ∧ 388381 ≤ prev +
1`, with `version : Int` (Core's `int32_t nVersion`, so negative versions are below every floor and
`0x20000000` is above them). Identical.

## `GetBlockProof` — `blockProof`

Core: `bnTarget.SetCompact(nBits, &fNegative, &fOverflow)`; `fNegative || fOverflow || bnTarget == 0 →
0`; else `(~bnTarget / (bnTarget + 1)) + 1` on 256-bit words. The Lean: `deriveTarget` (the same three
rejections, plus the `powLimit` test which is `CheckProofOfWork`'s, not `GetBlockProof`'s: a target
above `powLimit` gives `0` work in the model where Core would give a positive value, but such a header
never enters the chain, since `checkHeaderPow` rejects it first, so no chain-work sum differs) then
`(2^256 − 1 − t) / (t + 1) + 1`, which is `~t / (t+1) + 1` since `~t = 2^256 − 1 − t`. `chainWork` sums
it over the chain as `nChainWork` does. The one difference is on headers that cannot be in a chain.

## Checks from the guide

- **Order of tests.** The same as Core and it matters here (transient versus permanent outcomes);
  vectors pin each precedence.
- **Constants.** 7200; 11; 2016 (= 1209600 / 600); 227931, 363725, 388381; the version floors 2, 3, 4.
- **Integer semantics.** Times compared as `Int` (Core `int64_t`); `tipHeight − 2015` truncated but
  unreachable before the first boundary; `version` signed.
- **Defaults.** `getD genesisHeader` for the retarget ancestor and `0` for an empty window, both
  unreachable as explained.
- **Policy vs consensus.** BIP94 (testnet4/regtest), `fPowAllowMinDifficultyBlocks` (testnet),
  `nMinimumChainWork` and checkpoints (node policy for header download, not validity) are correctly
  absent; the version floors are consensus and present.
