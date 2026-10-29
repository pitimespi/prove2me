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
   limit L3). Makes "the UTXO set is a function of the chain, not the path" a theorem.
4. **BIP30 with BIP34 implies no duplicate txids** on any reachable chain, including the two
   historical exception blocks and the 1,983,702 limit; today this argument is a comment in Core.
5. **Difficulty is bounded.** Chain work strictly increases, and across one retarget the target
   changes by at most a factor of four in either direction; the exact statement of what an
   adversary can do with timestamps (the timewarp gap) would be new.

## B. Protocols built on the rules (need an adversary model)

6. **Lightning channel safety.** A party following the protocol never loses funds if it can get a
   transaction confirmed within the CSV delay; the penalty mechanism (revocation keys,
   `OP_CHECKSEQUENCEVERIFY`) verified directly against the Tapscript and BIP68 definitions.
   Probably the single most valuable unproven claim in the ecosystem.
7. **Taproot script-path soundness.** No control block opens a leaf not committed in the tree,
   given collision resistance of the tagged hashes; a reduction over the published commitment
   arithmetic.
8. **MuSig2 and FROST aggregation.** The aggregated key verifies under BIP340 exactly when the
   partial signatures combine correctly.
9. **Miniscript correctness.** Every compiled policy satisfies its spending conditions and only
   those, and the script is consensus-valid and within the size limits, against the real
   interpreter.

## C. Claims about the system (the famous results)

10. **Nakamoto consensus security** (common prefix, chain quality, chain growth) tied to the
    actual header rules rather than an abstract model.
11. **Selfish-mining thresholds**, a Markov-chain argument redone several times with different
    numbers.
12. **Replace-by-fee and pinning**: a precise statement of the property the mempool rules are
    meant to guarantee (no free relay, bounded pinning cost).

## Also worth doing on the existing work

- A second review of the script layer (spots 1, 7, 8) by someone outside this session.
- Differential testing of the Lean interpreter against Core's `script_tests.json` and
  `tx_valid.json` / `tx_invalid.json`.
- Closing limits L1 and L10 with a revision of the Script definition.
