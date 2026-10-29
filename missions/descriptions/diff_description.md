## The claim

"Difficulty adjusts by at most a factor of four per period" is the rule everyone states about the retarget, and the timewarp attack is the observation that a miner who controls timestamps can push the adjustment to that limit every period. The proof-of-work mission transcribed `CalculateNextWorkRequired` and proved its output satisfies Core's own `PermittedDifficultyTransition`. This mission states the bound itself, as arithmetic on the target: before the compact rounding, after it, over any number of periods, and for the required target of the next block on a chain.

## What is proved

- **No wraparound** (`no_wrap`): a valid target times the clamped timespan is below $2^{256}$, so `arith_uint256`'s modular multiplication is exact on every valid input.
- **Raw bounds** (`raw_target_bounds`): the raw next target is at most four times the last target and, unless the `powLimit` cap binds, at least a quarter of it.
- **Encoded bounds** (`encoded_target_upper`, `encoded_target_lower`): after the compact rounding the target still at most quadruples, and is at least the encoding of a quarter of the old target.
- **Many periods** (`target_after_upper`, `target_after_le_powLimit`): over $m$ periods the target grows by at most $4^m$ and never exceeds `powLimit`.
- **On a chain** (`requiredBits_le`, the goal): the block mission's `GetNextWorkRequired` on any chain state with a valid tip target returns a target at most four times the tip's, whatever the timestamps.

## What this rests on

The proof-of-work mission's `clamp_bounds`, `getCompact_le`, `round_mono` and `nextWork_le_powLimit`, and the block mission's `requiredBits`. The lower bound after rounding is stated through the encoding of a quarter rather than as a numeric ratio; a numeric form (within one part in $2^{15}$) would need a rounding lemma the proof-of-work mission does not provide. ([`pow.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp))
