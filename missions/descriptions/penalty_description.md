## The claim

Lightning's security against a counterparty who broadcasts an old, revoked commitment transaction rests on the penalty: the honest party, who holds the revocation secret for that commitment, can take every output at once, while the cheater can take nothing before `to_self_delay` blocks. The script missions proved what each commitment output's script enforces; this mission puts the pieces together at the script level, output by output, in both directions.

## What is proved

- **Completeness** (`to_local_penalty_sig`, `to_local_penalty`, the four HTLC penalty theorems, `revoked_commitment_penalty`, the goal): if the oracle accepts a signature for the revocation key, every penalisable output of the commitment transaction (`to_local`, offered and received HTLCs, legacy and anchors forms) has a witness `VerifyScript` accepts, with no delay and no condition on the spending transaction. `to_remote_honest_only` and the two anchor theorems state the facts for the outputs that have no revocation path.
- **Safety** (`to_local_cheater_delayed`, `cheater_delay_in_tx_terms`, `cheater_delay_any_sequence`, `cheater_needs_delay`, the four `*_cheater_no_revocation` theorems, `htlc_cheater_one_block_anchors`, `received_cheater_height`): if the oracle accepts no signature for the revocation key and knows no other preimage of its hash, every spend the cheater can make takes a non-revocation path: the balance only after `to_self_delay` (version 2, `nSequence ≥ to_self_delay`), the HTLCs only by preimage, success or timeout, with the one-block delay in the anchors form and the expiry bound for timeouts.
- **The race** (`penalty_any_block`): the penalty transaction is final in any block, so the honest party wins whenever it confirms within the delay.

## What this rests on and what it does not say

The hypotheses are unforgeability stated on the oracle for one key (`NoRevocationSig`) and second-preimage resistance of `hash160` for the revocation hash (`NoRevHashPreimage`); there is no model of key derivation (BOLT #3's per-commitment secrets), no signing oracle, no ECDSA security proof, and no network or fee model. The BIP68 consequence of `nSequence ≥ to_self_delay` (the cheater's transaction cannot enter a block within the delay) is stated in transaction terms, not composed with the block mission's sequence-lock check. The legacy (P2WPKH) `to_remote` has no published theorem and is not covered. ([BOLT #5](https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling))
