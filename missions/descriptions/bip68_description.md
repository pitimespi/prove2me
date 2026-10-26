## Why relative lock-time matters

Bitcoin nodes must agree on whether a transaction may spend its inputs yet. Since 2016 that decision includes **relative lock-time**: an input may declare that the output it spends must have been confirmed for a minimum number of blocks or a minimum elapsed time before it becomes spendable. The rule is defined by [BIP68](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki) and enforced on mainnet by three helper functions in Bitcoin Core: `CalculateSequenceLocks`, `EvaluateSequenceLocks`, and `SequenceLocks` ([pinned source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp)). Payment channels, atomic swaps, and vault constructions depend on this rule to enforce dispute windows; a node that decodes a sequence word differently from its peers can accept or reject a block the rest of the network treats the other way.

The specification is short and the implementation is about seventy lines, yet the two are written in different languages. BIP68 speaks of bits, masks, and elapsed delays; the implementation folds inputs into two signed thresholds compared against the candidate height and its ancestor's median time. Whether these agree, for every 32-bit sequence word and every input list, is the question this mission settles. Absolute lock-time (`nLockTime`) already has a Lean treatment in [btc-verified](https://github.com/ProofOfKeags/btc-verified/blob/2fdeb40ca2b3f289896ed14a3340ad231cd16538/BtcVerified/Consensus/LockTime.lean), whose consensus documentation lists BIP68 as outstanding work.

## Sequence words, inputs, and contexts

An **input** is a pair $(s, c)$: an unsigned 32-bit **sequence word** $s$ and the **coin height** $c \in \mathbb N$ of the output being spent. A **context** is a pair $(H, M)$: the candidate block height $H \in \mathbb N$ and a total function $M : \mathbb N \to \mathbb N$ giving the **median time past** of each ancestor height. Write $h^- = \max(h-1, 0)$; natural-number subtraction in Lean truncates at zero and realizes this directly.

Three fields of $s$ matter. The **disable bit** $D$ is bit 31. The **type bit** $T$ is bit 22: set means a time-based lock, clear means a height-based lock. The **delay** $d = s \bmod 65536$ is the low sixteen bits; for a time lock it denotes $512d$ seconds. **Enforcement** $E$ holds when the transaction version is at least 2 and bit 0 of the validation flags is set.

The **declarative model** (`BIP68_Model`) expresses these as arithmetic on $s$ viewed as a natural number: $D \iff \lfloor s / 2^{31} \rfloor = 1$, $T \iff \lfloor s / 2^{22} \rfloor \bmod 2 = 1$. A single input is **satisfied** when
$$D \ \lor\ \begin{cases} M(c^-) + 512d \le M(H^-), & T,\\ c + d \le H, & \neg T.\end{cases}$$
A transaction **satisfies BIP68** when $\neg E$ or every input is satisfied. The model also fixes the **expected height list**: each input's coin height, replaced by $0$ exactly when $E$ holds and $D$ is set.

The **Core transcription** (`BIP68_Core`) uses bit-vector masks `0x80000000`, `0x00400000`, `0x0000ffff` and a left shift by 9. An **accumulator** holds two signed thresholds $(a, b)$ and a reversed height list, starting at $(-1, -1, [\,])$. Each enabled, non-disabled input updates $b \leftarrow \max(b,\ M(c^-) + 512d - 1)$ for a time lock or $a \leftarrow \max(a,\ c + d - 1)$ for a height lock. **Evaluation** succeeds when $a < H$ and $b < M(H^-)$. When $E$ is false, the fold is skipped and the original heights are returned.

## Formalization targets

### Goal — helper correctness
Under the **admissible domain** ($0 < H \le 2^{31}-1$, every $c \le H$, every $M(h) \le 2^{63}-1$ for $h \le H$) and the **no-overflow** condition (for every enforced, non-disabled input, the sum selected by $T$ fits its signed destination before the subtraction of one),
$$\mathrm{sequenceLocks}(v, f, H, M, I) = \mathrm{true} \iff \mathrm{satisfiesBIP68}(v, f, H, M, I),$$
and the height list returned by the fold equals the expected height list. This is `BitcoinBIP68.core_correct`.

### Supporting milestones
1. **Decoding** (`decode_sequence`): for every 32-bit word, the mask tests agree with the quotient-and-remainder tests, the masked delay equals $d$, and the shifted seconds equal $512d$. No hypothesis on unused bits.
2. **Fold acceptance** (`fold_acceptance`): for any starting accumulator, evaluating the fold succeeds iff evaluating the starting accumulator succeeds and every input is satisfied. No range or monotonicity assumptions.
3. **Height vector** (`height_vector`): the returned list has the original length and order, with zeroes exactly at enforced, disabled inputs, including repeated entries and the empty list.
4. **Threshold bounds** (`calculated_bounds`): under admissibility and no-overflow, $-1 \le a \le 2^{31}-1$ and $-1 \le b \le 2^{63}-1$, preserving the $-1$ sentinel.

## What the result establishes

The goal is a kernel-checked statement that a Lean transcription of the pinned Core helpers decides exactly the BIP68 spending condition on the admissible domain, and that its side effect on the per-input height list is the one BIP68 describes. Both directions matter: a lock the implementation accepts is one the specification accepts, and a lock the specification accepts is one the implementation accepts.

Formalizing it adds three things beyond the prose specification. It makes the overflow preconditions explicit, which BIP68 leaves implicit and Core leaves to callers. It separates the bit-level decoding (a `bv_decide`-style fact) from the aggregation logic (an induction over the input list), so each can be audited on its own. And it produces reusable definitions — `Input`, `Context`, the admissibility and overflow predicates — for a later whole-block validation development in which the caller obligations (supplying coin heights, ancestor clocks, activation flags, and coinbase exclusion) are discharged.

Status: the statements compile with intentional `sorry` placeholders and have independent read-backs. Differential checks ran 2,014 cases against extracted Core helper bodies; these test the transcription, not the theorems. No proof of any statement is claimed.

## Where the obvious argument fails

The natural first idea is to prove `core_correct` by unfolding everything and calling a decision procedure. It fails because the two sides live in different arithmetic. The implementation computes thresholds in signed integers after subtracting one; the specification compares unsigned sums with $\le$. The equivalence $a < H \iff \max_i (c_i + d_i - 1) < H$ holds only because the $-1$ sentinel is below every admissible height and because each $c_i + d_i - 1$ is formed without wrap-around. Both facts need the admissibility and no-overflow hypotheses, and the proof must thread them through the fold.

A second trap is the disabled input. In the model, a disabled input is satisfied unconditionally; in the fold, it leaves both thresholds unchanged but still appends $0$ to the height list only when enforcement is on. `height_vector` records this asymmetry; a proof that treats disabled inputs as absent gets the height list wrong.

A third is the median-time function. $M$ is arbitrary: not monotone, not bounded outside $[0, H]$. The theorems are stated for this weaker model deliberately, so any proof that assumes a well-formed chain is proving a different statement.

## Formalization scope

The development commits to the following conventions, all fixed in `BIP68_Model` and `BIP68_Core`. Sequence words, versions, and flags are `BitVec 32`. Heights and times are `Nat` in the model and `Int` in the accumulator. $h - 1$ on `Nat` truncates at zero, matching `max(h-1, 0)` in the source. Input lists are finite `List`s; the empty list is in scope. The predicates `specEnabled`, `specDisabled`, and `specTimeBased` are `Prop` with decidability instances; the Core-side tests are `Bool`. Admissibility and no-overflow are the only hypotheses on `core_correct`; `fold_acceptance` and `height_vector` carry none.

A trivializing formalization would define `satisfiesBIP68` by calling `sequenceLocks`; the model is written independently from the BIP text and must stay that way. Weakening the no-overflow hypothesis to a vacuous one, or restricting to nonempty lists, is out of scope.

Dependencies: Lean 4 core and `Std` only; no Mathlib. The two definitions are published first and imported by every theorem. Proofs of the four milestones in any order are welcome, as are lemmas on `coreStep` reusable by the goal. Out of scope: the C++-to-Lean correspondence (documented, not proved), coinbase exclusion, activation selection, and block-level composition, which belong to a separate whole-consensus mission that will import these results.

## Selected references

- Mark Friedenbach, BtcDrak, Nicolas Dorier, kinoshitajona. *BIP68: Relative lock-time using consensus-enforced sequence numbers*, Bitcoin Improvement Proposals, 2015. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki)
- Bitcoin Core contributors. *`CalculateSequenceLocks`, `EvaluateSequenceLocks`, `SequenceLocks`*, `src/consensus/tx_verify.cpp` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp)
- Bitcoin Core contributors. *Mainnet validation and parameters*, same revision. [validation.cpp](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp), [chainparams.cpp](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp)
- ProofOfKeags contributors. *btc-verified: absolute lock-time in Lean 4*, revision `2fdeb40c`. [LockTime.lean](https://github.com/ProofOfKeags/btc-verified/blob/2fdeb40ca2b3f289896ed14a3340ad231cd16538/BtcVerified/Consensus/LockTime.lean), [consensus coverage](https://github.com/ProofOfKeags/btc-verified/blob/master/BtcVerified/Consensus/README.md)
- Lean FRO. *Bitvectors*, Lean Language Reference. [Documentation](https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/)
