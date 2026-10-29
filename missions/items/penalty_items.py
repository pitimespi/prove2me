SRC = ("BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): "
       "https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; "
       "Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx "
       "(src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141")
TAGS = ["bitcoin", "lightning", "bolt3", "bolt5", "penalty", "revocation", "channel-safety", "csv", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinPenalty",
    "definition_title": "A revoked commitment transaction's outputs, the holder of the revocation key, and the cheater",
    "natural_language_statement": r"""Names over the `to_local`, HTLC, anchor, funding and lock-time missions.

**`CommitmentKeys`** — the keys of one commitment transaction: `revPk` and its hash `revHash`, `localDelayedPk`, `remoteKey`, `localHtlcKey`, `remoteHtlcKey`, the two funding keys, and `toSelfDelay`; **`Htlc`** — a payment hash and an expiry; **`WellFormed K`**, **`HtlcWellFormed h`** — the 520-byte bounds, $0 \le$ `toSelfDelay` $< 2^{16}$, $|{\rm expiry}| < 2^{32}$.

**Output scripts** — `toLocalBytes K`, `offeredBytes K h`, `receivedBytes K h`, their anchors forms, `toRemoteBytes K`, `anchorLocalBytes K`, `anchorRemoteBytes K`, all through the published constructors; **`p2wshOf sc`** — the pay-to-witness-script-hash program of a script; **`oracleOf c sc`** — the signature mission's `legacyOracle` for context $c$ with witness-v0 sighash on `sc`.

**`HoldsRevocation o K`** — the oracle accepts some signature (at most 520 bytes) for `revPk`, and `hash160 revPk = revHash`: the honest party after a revocation. **`NoRevocationSig o K`** — the oracle accepts no signature for `revPk`: the cheater, who never learned the revocation secret. **`NoRevHashPreimage o K`** — `revPk` is the only `hash160` preimage of `revHash` the oracle knows (second-preimage resistance, needed because the HTLC scripts test the hash of the pushed key).

**Witnesses** — `toLocalPenaltyWitness K sigR = [sigR, [1], script]`, `htlcPenaltyWitness K sigR sc = [sigR, revPk, sc]`. **Cheater paths** — `DelayedSpend` (the `to_local` delayed path), `OfferedNonRevocation`, `ReceivedNonRevocation` and their anchors forms (the HTLC paths other than revocation, with the one-block delay in the anchors form).

**Formalization Note.** Everything else is the published missions'. Unforgeability is a hypothesis on one oracle and one key; there is no key derivation, signing oracle, ECDSA or network model. Only `Std` is imported.""",
}

T = {}
T["to_local_penalty_sig"] = ("to_local: the revocation witness is accepted with no delay", r"""For a well-formed `K`, a true program and any accepted signature `sigR` (≤ 520 bytes) for `revPk`: `verifyScript tap c [] (p2wshOf (toLocalBytes K)) (toLocalPenaltyWitness K sigR) = true`, with no hypothesis on the transaction's version, `nSequence` or lock time, nor on the `CSV` flag.""")
T["to_local_penalty"] = ("to_local penalty: the holder of the revocation key spends the balance output", r"""Under `HoldsRevocation (oracleOf c (toLocalBytes K)) K` there is a `sigR` whose penalty witness `verifyScript` accepts.""")
T["offered_htlc_penalty"] = ("Offered HTLC penalty", r"""Under `HoldsRevocation` for the offered-HTLC script: some `[sigR, revPk, script]` is accepted.""")
T["received_htlc_penalty"] = ("Received HTLC penalty", r"""As `offered_htlc_penalty` for the received script.""")
T["offered_htlc_penalty_anchors"] = ("Offered HTLC penalty, anchors form", r"""As `offered_htlc_penalty` for the anchors-form script (the revocation path skips the one-block delay).""")
T["received_htlc_penalty_anchors"] = ("Received HTLC penalty, anchors form", r"""As `received_htlc_penalty` for the anchors-form script.""")
T["revoked_commitment_penalty"] = ("A revoked commitment transaction: every penalisable output is spendable at once by the holder of the revocation key", r"""For a well-formed `K` and HTLC `h`, true programs, and `HoldsRevocation (oracleOf c sc) K` for every script `sc`: the `to_local` output and the offered and received HTLC outputs, in both the legacy and the anchors form, each have a penalty witness that `verifyScript` accepts, in one context. The BOLT #5 penalty transaction, output by output, at the script level.""")
T["to_remote_honest_only"] = ("to_remote (anchors): only the remote key spends it, after one block", r"""Accepted witnesses for `toRemoteBytes K` are exactly `[sig]` with `sig` valid for `remoteKey` and `CsvPasses … 1`; the broadcaster has no path.""")
T["anchor_holder_or_delay"] = ("Anchors: the funding-key holder at any time, anyone after the delay", r"""For either anchor: accepted witnesses are `[sig]` with `sig` valid for the funding key, or a clean false together with `CsvPasses … 16`.""")
T["anchor_anyone_after_16"] = ("Anchors: the empty-signature sweep in transaction terms", r"""With the `CSV` flag and flag-free `nSequence`: `[[], anchorBytes fk]` verifies iff the program is true, the version is at least 2 and `nSequence ≥ 16`.""")
T["to_local_cheater_delayed"] = ("to_local safety: without the revocation key, every accepted spend takes the delayed path", r"""Under `NoRevocationSig`: every witness `verifyScript` accepts for `toLocalBytes K` is `[sig, b]` with `DelayedSpend`: `b` false, `CsvPasses … toSelfDelay`, `sig` valid for `localDelayedPk`.""")
T["cheater_delay_in_tx_terms"] = ("The cheater's to_local spend needs version 2 and nSequence ≥ to_self_delay", r"""Under `NoRevocationSig`, the `CSV` flag and flag-free `nSequence`: any accepted spend has `2 ≤ version` and `toSelfDelay ≤ nSequence`.""")
T["cheater_delay_any_sequence"] = ("The cheater's to_local spend, for any nSequence", r"""Without the `nSequence < 2^16` hypothesis: version at least 2, the disable bit clear, and `toSelfDelay ≤ nSequence`.""")
T["cheater_needs_delay"] = ("The cheater cannot spend to_local early", r"""Under `NoRevocationSig` and the `CSV` flag: no accepted spend has version below 2 or `nSequence` below `toSelfDelay`.""")
T["offered_cheater_no_revocation"] = ("Offered HTLC safety: the cheater never takes the revocation path", r"""Under `NoRevocationSig` and `NoRevHashPreimage`: every accepted spend of the offered HTLC is a preimage or timeout path (`OfferedNonRevocation`).""")
T["received_cheater_no_revocation"] = ("Received HTLC safety", r"""As above: every accepted spend is a success or timeout path (`ReceivedNonRevocation`).""")
T["offered_cheater_no_revocation_anchors"] = ("Offered HTLC safety, anchors form", r"""As above with the one-block delay in every path.""")
T["received_cheater_no_revocation_anchors"] = ("Received HTLC safety, anchors form", r"""As above with the one-block delay in every path.""")
T["htlc_cheater_one_block_anchors"] = ("The cheater's HTLC spend waits one block (anchors)", r"""Under the safety hypotheses and the `CSV` flag: version at least 2, disable bit clear, `nSequence ≥ 1`.""")
T["received_cheater_height"] = ("The cheater's received-HTLC timeout only above the expiry height", r"""With the lock-time mission's composition: a cheater's two-element spend of the received HTLC, final at `height`, has `expiry < height`.""")
T["penalty_any_block"] = ("The penalty is valid in any block", r"""The `to_local` penalty witness is accepted with no condition on the transaction, and with `nLockTime = 0` the penalty transaction is final at every height: the honest party wins the race whenever it gets a transaction confirmed within the delay.""")
THEOREMS = {f"BitcoinPenalty.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinPenalty.revoked_commitment_penalty"]["ms"] = ("Completeness", "All five penalty witnesses from the published `p2wsh_spend` theorems' backward directions.")
THEOREMS["BitcoinPenalty.to_local_cheater_delayed"]["ms"] = ("Safety", "The forward direction of `to_local`'s `p2wsh_spend` with the revocation disjunct excluded by `NoRevocationSig`.")
ORDER = ["BitcoinPenalty." + k for k in ["to_local_penalty_sig", "to_local_penalty", "offered_htlc_penalty", "received_htlc_penalty",
  "offered_htlc_penalty_anchors", "received_htlc_penalty_anchors", "revoked_commitment_penalty", "to_remote_honest_only",
  "anchor_holder_or_delay", "anchor_anyone_after_16", "to_local_cheater_delayed", "cheater_delay_in_tx_terms",
  "cheater_delay_any_sequence", "cheater_needs_delay", "offered_cheater_no_revocation", "received_cheater_no_revocation",
  "offered_cheater_no_revocation_anchors", "received_cheater_no_revocation_anchors", "htlc_cheater_one_block_anchors",
  "received_cheater_height", "penalty_any_block"]]
