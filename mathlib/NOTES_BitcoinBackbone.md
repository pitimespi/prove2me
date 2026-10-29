# NOTES — `BitcoinBackbone`: deterministic core of the Bitcoin backbone analysis

Reference: J. Garay, A. Kiayias, N. Leonardos, *The Bitcoin Backbone Protocol: Analysis and
Applications*, EUROCRYPT 2015 (full version: ePrint 2014/765). Lemma/theorem names below refer to
the full version (synchronous model, "Δ = 1", static difficulty, random-oracle abstraction).

Files: `Definitions/Def_BitcoinBackbone.lean` (model), `Solutions/Sol_BitcoinBackbone_all.lean`
(proofs). No `sorry`; every public theorem depends only on `[propext, Classical.choice, Quot.sound]`
(`chainWork_const_bits` only on `[propext, Quot.sound]`).

## 1. The model

* `Block`: `honest p r` (block found by honest party `p` in round `r`; one block per party per round,
  as the backbone `pow` stops after the first success) or `adv r j` (the `j`-th of the `Z r`
  adversarial blocks of round `r`). `Block.round`, `Block.isHonest`.
* `Chain := List Block`, oldest first, genesis omitted; extension = `C ++ [B]`; `Chain.work C = C.length`
  (fixed difficulty, see §4). `Chain.upTo C t` = the blocks of `C` of round `≤ t` (a `takeWhile`;
  for a valid chain this is the prefix older than `t`, since rounds are nondecreasing).
* `Execution` (the trace): `n` honest parties `0..n-1`; `mined p r : Bool`; `Z r : ℕ`;
  `base p r : Chain` = the chain party `p` adopts at the start of round `r ≥ 1` (result of
  `maxvalid` over its own chain and everything delivered to it, honest or adversarial);
  `advParent r j` = the chain the adversary extended with its `j`-th block of round `r`.
* Derived: `chain p r` = chain held/broadcast by `p` at the **end** of round `r`
  (`[]` at round 0; `base p r ++ [honest p r]` if `p` mined in round `r`, else `base p r`);
  `honestCount r`, `X r ∈ {0,1}` (successful round), `Y r ∈ {0,1}` (uniquely successful round).
* `Extends E parent B` / `ValidChain E C`: every block of `C` sits on top of **exactly** the chain its
  creator extended (`C.take i = base p r` for `C[i] = honest p r`, `C.take i = advParent r j` for
  `adv r j`, with `p < n`, `mined p r`, `j < Z r`). This is the abstraction of the hash chain: a block
  determines its ancestry (the paper's "no copies / no insertions" part of typicality).
* `Execution.Legal E` — the rules of the synchronous model, **all hypotheses**:
  * `mined_zero`: nothing is mined in round 0.
  * `base_valid`, `base_rounds`: what an honest party adopts in round `r` is a valid chain of blocks of
    rounds `< r` (messages sent in round `r-1` arrive at the start of round `r`).
  * `base_length`: `(chain q r).length ≤ (base p (r+1)).length` for all honest `p, q` — every honest
    chain of round `r` is received by everyone by round `r+1` and `maxvalid` picks a longest chain.
    (Only a lower bound on the adopted length is assumed; the adversary may make an honest party
    adopt any valid long chain it chooses to deliver — this only strengthens the adversary.)
  * `advParent_valid`, `advParent_rounds`: the adversary extends valid chains of blocks of rounds
    `≤ r` when working in round `r` (rushing: it may build on the honest blocks of the same round).
* `Execution.Typical E λ` — **the probabilistic part, as a hypothesis**:
  `∀ a b, a + λ ≤ b → ∑_{i ∈ Icc a b} Z i < ∑_{i ∈ Ioo a b} Y i`.
  I.e. on every window `[a, b]` of at least `λ+1` rounds, the uniquely successful rounds strictly
  inside the window outnumber **all** adversarial blocks of the window, the two boundary rounds
  included. This is the deterministic consequence of the paper's Definition 9 (typical execution:
  Chernoff bounds on `X(S), Y(S), Z(S)`) together with the honest-majority assumption
  (`Z(S) < Y(S)` for `|S| ≥ λ`, derived in the paper's Lemma 12/13-type statements). The boundary
  rounds are credited to the adversary because the rushing adversary can mine on the honest block of
  round `a` in round `a` and deliver round-`b` blocks in round `b`; the paper absorbs these two rounds
  in its `(1 ± ε)` slack. Only this inequality is used; the paper's separate bounds on `X(S)` are not
  needed (`Y ≤ X` is immediate). Note `Typical E λ` forces `λ ≥ 1` and also yields the "upper
  bound" `∑_{Icc a b} Z ≤ λ - 2` for `b ≤ a + λ` (private lemma `sum_Z_short_window`), which is
  what replaces the paper's `Z(S) < (1+ε)·…·|S|` bound in the block-count statements.

Conventions vs. the paper: the paper's "chain held at round r" is the chain adopted at the start of
the round; here `chain p r` is the end-of-round chain, so the paper's `∑_{i=r}^{s-1} X_i` becomes
`∑_{i=r+1}^{s-1} X_i` (`Finset.Ico (r+1) s`) in `chain_growth`. Parties are `ℕ` with `p < n`.

## 2. Public theorems (all fully proved)

| Theorem | Statement (informal) | Paper |
|---|---|---|
| `chain_growth` | honest `p, q`, `r < s`: `(chain p r).length + ∑_{i∈Ico (r+1) s} X i ≤ (chain q s).length` | Lemma 7 (chain growth) |
| `chain_growth_self` | same with `q = p`, any `r ≤ s` | — |
| `uniquely_successful_height` | if `Y i = 1` with miner `m`, any honest block at height `(base m i).length + 1` of any valid chain is `honest m i` | Lemma 14 |
| `common_prefix_private` | `C = chain p r`; `D` valid, blocks of rounds `≤ r`, `D[f-1]` honest of round `r₀` (or `f = 0 = r₀`), all blocks of `D` above height `f` adversarial; `r₀ + λ ≤ r` ⇒ `D.length < C.length` | counting argument behind Lemma 15 (private-chain attack) |
| `common_prefix_rounds` | honest `p₁, p₂`, `r₁ ≤ r₂`, `λ ≤ w ≤ r₁`: `(chain p₁ r₁).upTo (r₁ - w) <+: chain p₂ r₂` (blocks older than `w` rounds are a prefix of every later honest chain) | Lemma 15 + Theorem 16 (round form) |
| `common_prefix` | honest `p₁, p₂`, `r₁ ≤ r₂`: `(chain p₁ r₁).take ((chain p₁ r₁).length - 2λ) <+: chain p₂ r₂` | Theorem 16 (common prefix, `k = 2λ`) |
| `chain_quality` | honest `p`, `u + λ ≤ (chain p r).length`: among the `λ` consecutive blocks `((chain p r).drop u).take λ` there is an honest block | Theorem 17 (chain quality, weak form `μ > 0`) |
| `chainWork_const_bits` | all headers of `S : BitcoinBlockV2.ChainState` have the same `bits` ⇒ `S.chainWork = S.headers.length * blockProof bits` | fixed-difficulty remark |

Parameters vs. the paper: the paper has `k ≥ 2λf` (common prefix) and `ℓ ≥ 2λf` (chain quality)
with `f` the per-round success probability, obtained from the upper Chernoff bounds on block counts.
Here, with the single deterministic hypothesis `Typical E λ`, the bounds are `k = 2λ` and `ℓ = λ`:
a valid chain has at most one honest block per round, and `Typical` bounds adversarial blocks in any
`λ+1` rounds by `λ-2`. The round form `common_prefix_rounds` (stability after `λ` rounds) has no
block-count parameter at all and is the statement actually produced by the pairing argument.

## 3. Proof structure (private lemmas)

* `growth_base`: induction on `s`, for all honest `q` simultaneously; uses `base_length` and that a
  successful round's miner extends a chain at least as long as everyone's chain of the previous round.
* `round_mono`, `index_unique`, `honest_round_unique`: rounds are nondecreasing along a valid chain, a
  block occurs at most once, at most one honest block per round (all from `ValidChain`).
* `height_unique` / `height_strict_mono` (Lemma 14): via `chain_growth` in both directions.
* `card_le_sum_Z`, `run_le_sum_Z`: distinct adversarial blocks of rounds in `[a, b]` number at most
  `∑_{Icc a b} Z` (injection into `advBlocks`).
* `pairing_core` (the pairing argument of Lemma 15): `C₁ = chain p r`, `C₂` valid with rounds `≤ r`,
  `|C₁| ≤ |C₂|`, `L` = longest common prefix length, `r*` = round of the last honest block below `L`
  (`lastHonestRound`); every uniquely successful round `i ∈ (r*, r)` yields a distinct adversarial block
  of a round in `[r*, r]` in `C₁ ∪ C₂` (the honest block of round `i` cannot be in the common prefix,
  the block at its height in the other chain is adversarial by `height_unique`, and it lies above the
  honest block of round `r*` so was mined at round `≥ r*`). Hence `∑_{Ioo r* r} Y ≤ ∑_{Icc r* r} Z`,
  contradicting `Typical` when `r* + λ ≤ r`.
* `same_round` (Lemma 15): both prefix directions from `pairing_core`, taking `L` as the first index
  of disagreement (`Nat.find`) and using `round_mono` to bound `r*`.
* `common_prefix_rounds`: `Nat.le_induction` on `r₂` from `r₁`; the step applies `same_round` at
  round `s` to `chain q s` and `base q (s+1)` (any delivered chain), exactly as in Theorem 16.
* `common_prefix`: counts the blocks of `chain p₁ r₁` of rounds `> r₁ - λ` (`card_recent_le`:
  `< 2λ`) and applies `common_prefix_rounds`.
* `run_bound` / `chain_quality`: a run of adversarial blocks between two honest blocks of rounds
  `r₁ < r₂` (or genesis / the honest holder's own round) has `≤ ∑_{Icc r₁ r₂} Z` blocks and
  `≥ ∑_{Ioo r₁ r₂} X` blocks (`growth_base`), so `r₂ - r₁ < λ` and the run has `< λ` blocks.

## 4. Tie to the real rules

`BitcoinBlockV2.blockProof bits` depends only on `bits`, so for a header list at constant `nBits`,
`ChainState.chainWork = length · blockProof bits` (`chainWork_const_bits`); the "longest chain" rule of
the paper and `Chain.work = length` coincide with Bitcoin Core's most-work rule within a difficulty
period. Difficulty adjustment (variable `bits`) is outside the paper's static model and this
formalization.

## 5. What is not proved / limitations (be precise)

* **Probability**: nothing probabilistic is proved. `Typical` is an assumption; the paper's Theorem
  10 (typical executions occur with probability `1 - e^{-Ω(ε²fλ)}`) and the derivation of
  `Z(S) < Y(S)` from the honest-majority bound `t/(n-t) < 1 - δ` are out of scope.
* **Boundary rounds**: `Typical` is the asymmetric form `Z(Icc a b) < Y(Ioo a b)`; the paper's
  symmetric `Z(S) < Y(S)` with `(1±ε)` slack implies it only after adjusting `λ` by a constant, which
  is not formalized.
* **Constants**: `k = 2λ` (common prefix) and `ℓ = λ` (chain quality) replace the paper's `2λf`; the
  quantitative chain-quality fraction `μ = 1 - (1+δ/…)·t/(n-t)` is not proved, only `μ > 0` in the
  form "every `λ` consecutive blocks contain an honest block".
* **Model simplifications (all stated as hypotheses in `Legal`)**: one honest block per party per round;
  honest parties' adopted chains are only required to be at least as long as every honest chain of the
  previous round (no explicit `maxvalid`/tie-breaking rule); no explicit message model — the
  adversary's deliveries are implicit in `base`; the genesis is `[]`; no difficulty adjustment;
  no bound on `Z` beyond `Typical`.
* `common_prefix_private` does not need the prefix `D.take f = C.take f` (any valid chain whose blocks
  above an honest block of round `r₀ ≤ r - λ` are all adversarial is shorter than every honest chain
  of round `r`); the private-chain attack is the special case.
