# Claims worth proving next

Saved 2026-10-28 from the discussion after the 23-spot review. Ranked within each group by how much
a proof would change what people believe. The first two of group A are done (missions 14 and 15, published 2026-10-29, all proofs accepted).

## A. Theorems about the rules themselves (provable now against the published definitions)

1. **The 21 million bound as a chain invariant.** On every state reachable from genesis, the total
   value of the UTXO set is at most the subsidy issued so far, hence below `MAX_MONEY`. The subsidy
   schedule's total is already proved; this is the same bound for the whole validation path, which
   is what rules out an inflation bug of the CVE-2018-17144 kind. *Done: `BitcoinSupply.supply_bound`.*
2. **SegWit non-malleability.** A transaction whose inputs all spend native witness programs has
   an empty `scriptSig` on every input whenever its scripts verify, so its txid is a function of
   its version, prevouts, sequences, outputs and lock time alone: no third party can change the
   txid of a valid spend. For P2SH-wrapped programs the `scriptSig` is the single push of a
   `hash160` preimage of the output's hash. This is the property Lightning rests on. *Done: `BitcoinMalleability.txid_determined`.*
3. **Reorganization safety.** Disconnecting any sequence of blocks and reconnecting another valid
   sequence yields a state reachable by direct validation (currently proved one block at a time,
   limit L3). Makes "the UTXO set is a function of the chain, not the path" a theorem. *Done: `BitcoinReorg.reorg_safety` (mission 16).*
4. **BIP30 with BIP34 implies no duplicate txids** on any reachable chain, including the two
   historical exception blocks and the 1,983,702 limit; today this argument is a comment in Core.
   *Partly done (mission 17, `BitcoinUniqueness`, 8 theorems, proposal drafted):* the BIP34 height
   push is a prefix of the coinbase scriptSig, coinbases of distinct heights are distinct, and the
   BIP30 scan runs exactly where Core runs it and guarantees fresh outputs where it runs. Not done:
   the full "no duplicate txids on any reachable chain" needs the hash-collision-freeness of txids
   and the historical blocks 91722/91880 as data, which the model does not carry.
5. **Difficulty is bounded.** Chain work strictly increases, and across one retarget the target
   changes by at most a factor of four in either direction; the exact statement of what an
   adversary can do with timestamps (the timewarp gap) would be new. *Done (mission 18,
   `BitcoinDifficulty`, 7 theorems, proposal drafted):* no wraparound, raw and encoded bounds,
   `4^m` over `m` periods, never above `powLimit`, and `requiredBits ≤ 4 × tip` on any chain
   state. Chain work increasing was already `BitcoinBlockV2.chainWork_increases`.

## B. Protocols built on the rules (need an adversary model)

6. **Lightning channel safety.** A party following the protocol never loses funds if it can get a
   transaction confirmed within the CSV delay; the penalty mechanism (revocation keys,
   `OP_CHECKSEQUENCEVERIFY`) verified directly against the Tapscript and BIP68 definitions.
   Probably the single most valuable unproven claim in the ecosystem. *Core done (mission 20,
   `BitcoinToLocal`, 9 theorems):* the BOLT #3 `to_local` P2WSH output is spent exactly by the
   revocation key, or by the delayed key with version ≥ 2 and `nSequence ≥ to_self_delay`, under
   the published `VerifyScript`. Not done: the protocol-level game (who holds which key when, the
   HTLC scripts, the race against confirmation), which needs an adversary and network model.
7. **Taproot script-path soundness.** No control block opens a leaf not committed in the tree,
   given collision resistance of the tagged hashes; a reduction over the published commitment
   arithmetic. *Done (mission 19, `BitcoinTapSoundness`, 7 theorems, proposal drafted):* any
   verified control block with the honest internal key opens a committed leaf, or exhibits a
   SHA-256 collision, or two tweak scalars for one output key.
8. **MuSig2 and FROST aggregation.** The aggregated key verifies under BIP340 exactly when the
   partial signatures combine correctly. *Not attempted, judged infeasible here:* the statement
   needs associativity and commutativity of the secp256k1 group law over the executable
   `padd`/`pmul` of the signature mission (the Jacobian-free affine formulas with the model's
   `finv`), which is a Mathlib-scale algebraic development (Weierstrass curve group law), not a
   transcription; without it no identity of the form `(a+b)·G = a·G + b·G` is available.
9. **Miniscript correctness.** Every compiled policy satisfies its spending conditions and only
   those, and the script is consensus-valid and within the size limits, against the real
   interpreter. *Not attempted, judged out of scope:* Miniscript is a language with a type system
   and a compiler; its correctness theorem is a soundness proof of that type system against the
   interpreter for every fragment (dozens of combinators with their malleability and resource
   properties), a project of its own. Mission 20 is the hand-done instance for one fixed script.

## C. Claims about the system (the famous results)

10. **Nakamoto consensus security** (common prefix, chain quality, chain growth) tied to the
    actual header rules rather than an abstract model. *Done in the synchronous model (mission 21,
    `BitcoinBackbone`, Mathlib, 8 theorems):* chain growth, common prefix (with `k = 2λ`) and chain
    quality from the deterministic typical-execution hypothesis, plus the tie `chainWork = length ×
    blockProof` at constant difficulty. Not done: the probabilistic part (Chernoff bounds), the
    Δ-synchronous model, and difficulty adjustment.
11. **Selfish-mining thresholds**, a Markov-chain argument redone several times with different
    numbers. *Done (mission 22, `BitcoinSelfishMining`, Mathlib, 17 theorems, proposal drafted):*
    the Eyal–Sirer chain, its stationary distribution verified (invariance and total mass), the
    revenues as genuine infinite sums, the closed form, and `R > α ↔ α > (1-γ)/(3-2γ)`.
12. **Replace-by-fee and pinning**: a precise statement of the property the mempool rules are
    meant to guarantee (no free relay, bounded pinning cost). *Done (mission 23,
    `BitcoinReplacement`, Mathlib, 15 theorems, proposal drafted):* `PaysForRBF` transcribed from
    the pinned revision (`GetFee` as the exact ceiling, 100 sat/kvB default); no free relay along
    any replacement chain in four forms, replacement-count bounds, pinning cost exactly the
    attached descendants' fees, and rule 3 (from v29.0, absent at the pinned revision where the
    cluster mempool replaced it) as fee-rate domination.

## Also worth doing on the existing work

- A second review of the script layer (spots 1, 7, 8) by someone outside this session. *Done
  (`REVIEW2_SPOT1/7/8.md`).*
- Differential testing of the Lean interpreter against Core's `script_tests.json` and
  `tx_valid.json` / `tx_invalid.json`. *Done (`REVIEW_DIFFTEST.md`, 994 cases, only L1/L10 diverge).*
- Closing limits L1 and L10 with a revision of the Script definition.
