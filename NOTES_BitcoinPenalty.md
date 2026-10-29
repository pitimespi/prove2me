# BitcoinPenalty: the Lightning penalty on a revoked commitment, at the script level

Files: `Definitions/Def_BitcoinPenalty.lean`, `Solutions/Sol_BitcoinPenalty_all.lean`,
`tests/PenaltyVectors.lean`. Builds on the five Lightning missions `BitcoinToLocal`, `BitcoinHtlc`,
`BitcoinAnchors`, `BitcoinFunding`, `BitcoinHtlcLocks` (imported public theorems only; no private
lemma of theirs is needed, every proof is a corollary of a published `*_p2wsh_spend` iff).

## The model

`CommitmentKeys K`: `revPk`, `revHash` (the `hash160` the HTLC scripts carry), `localDelayedPk`,
`remoteKey` (`to_remote`), `localHtlcKey`, `remoteHtlcKey`, `fundingKeyLocal`/`fundingKeyRemote`
(the anchors' keys), `toSelfDelay : Int`. `Htlc h`: `payHash`, `expiry`. `WellFormed K` /
`HtlcWellFormed h` collect the sibling missions' hypotheses (520-byte bounds, `0 ≤ toSelfDelay < 2^16`,
`expiry.natAbs < 2^32`).

The outputs of the revoked commitment, as `CScript` bytes, reuse the published constructors:
`toLocalBytes K = BitcoinToLocal.toLocalBytes revPk toSelfDelay localDelayedPk`, `offeredBytes K h`,
`receivedBytes K h` (`BitcoinHtlc`), `offeredBytesAnchors`, `receivedBytesAnchors`, `toRemoteBytes`,
`anchorLocalBytes`, `anchorRemoteBytes` (`BitcoinAnchors`). `p2wshOf sc = witnessBytes 0 (sha256 sc)`;
`oracleOf c sc = legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 sc` is the concrete
oracle the `*_p2wsh_spend` theorems instantiate.

Witnesses in `CScriptWitness` order (script last): `toLocalPenaltyWitness K sigR = [sigR, [1], toLocalBytes K]`
(`<revocation_sig> 1`), `htlcPenaltyWitness K sigR sc = [sigR, revPk, sc]` (`<revocation_sig> <revocationpubkey>`).

The two sides of the penalty, as hypotheses on an abstract `Oracle o`:

- `HoldsRevocation o K := (∃ sigR, sigR.length ≤ 520 ∧ o.checkSig sigR revPk = some true) ∧ o.hash160 revPk = revHash`
  (the honest party: an accepted, witness-sized signature for the revocation key).
- `NoRevocationSig o K := ∀ sig, o.checkSig sig revPk ≠ some true` (the cheater: no accepted signature
  for the revocation key — the unforgeability hypothesis).
- `NoRevHashPreimage o K := ∀ pk, o.hash160 pk = revHash → pk = revPk` (second-preimage resistance of
  `hash160` at `revPk`; the HTLC scripts check `OP_HASH160 <pushed key> == revHash`, so without it a
  cheater could in principle push a colliding key it can sign for).

The paths left to the cheater: `DelayedSpend f o K b sig` (`SpendCondition` minus the revocation
disjunct), `OfferedNonRevocation` / `ReceivedNonRevocation` (`BitcoinHtlc.*Spend` minus the revocation
disjunct), and the `…Anchors` variants (the same `∧ CsvPasses f o 1`).

## Public theorems (21, names `BitcoinPenalty.*`; all take `hf : c.flags.witness = true`, `WellFormed K`,
and `castToBool (sha256 script) = true` where a witness is produced)

(A) Completeness — the holder of the revocation key spends at once:

- `to_local_penalty_sig`: any `sigR` (≤ 520 bytes) with `(oracleOf c (toLocalBytes K)).checkSig sigR revPk = some true`
  gives `verifyScript tap c [] (p2wshOf (toLocalBytes K)) (toLocalPenaltyWitness K sigR) = true`. No
  hypothesis on `c.tx.version`, `nSequence`, `nLockTime` or `c.flags.csv`.
- `to_local_penalty`: under `HoldsRevocation (oracleOf c (toLocalBytes K)) K`, `∃ sigR, verifyScript … = true`.
- `offered_htlc_penalty`, `received_htlc_penalty`, `offered_htlc_penalty_anchors`, `received_htlc_penalty_anchors`:
  likewise with `htlcPenaltyWitness K sigR script` under `HoldsRevocation (oracleOf c script) K`.
- `revoked_commitment_penalty`: in one context `c`, from `∀ sc, HoldsRevocation (oracleOf c sc) K`, the
  five accepted penalty witnesses at once.
- `to_remote_honest_only`: `verifyScript … (ws ++ [toRemoteBytes K]) = true ↔ hash ok ∧ sizes ∧
  ∃ sig, ws = [sig] ∧ checkSig sig remoteKey = some true ∧ CsvPasses f o 1` — `to_remote` (anchors form)
  is the counterparty's own balance; no penalty is needed and the broadcaster has no path to it.
- `anchor_holder_or_delay`: for `fk ∈ {fundingKeyLocal, fundingKeyRemote}`, the accepted witnesses of
  `anchorBytes fk` are exactly `[sig]` with `checkSig sig fk = some true` or
  (`checkSig sig fk = some false ∧ CsvPasses f o 16`).
- `anchor_anyone_after_16`: with the CSV flag and a flag-free `nSequence`, `[[], anchorBytes fk]` verifies
  iff hash ok ∧ `2 ≤ version` ∧ `16 ≤ nSequence`.

(B) Safety — the cheater cannot escape:

- `to_local_cheater_delayed`: under `NoRevocationSig (oracleOf c (toLocalBytes K)) K`, every accepted
  `ws` is `[sig, b]` with `DelayedSpend f o K b sig` (`b` false, `CsvPasses f o toSelfDelay`, `sig` for
  the delayed key).
- `cheater_delay_in_tx_terms` (via `csv_concrete` + `lightning_delay`, needs `c.flags.csv = true` and
  `nSequence < 2^16`): `2 ≤ c.tx.version ∧ toSelfDelay.toNat ≤ inputSequence c.tx c.nIn`.
- `cheater_delay_any_sequence` (via `csv_concrete` + `checkSequence_iff` + `Nat.and_le_left`, no bound
  on `nSequence`): `2 ≤ version ∧ nSequence &&& DISABLE_FLAG = 0 ∧ toSelfDelay.toNat ≤ nSequence`.
- `offered_cheater_no_revocation`, `received_cheater_no_revocation`: under `NoRevocationSig` and
  `NoRevHashPreimage`, every accepted spend is `OfferedNonRevocation` / `ReceivedNonRevocation`
  (preimage/timeout, success/timeout) on `ws.reverse`.
- `offered_cheater_no_revocation_anchors`, `received_cheater_no_revocation_anchors`: the same with
  `∧ CsvPasses f o 1`; `htlc_cheater_one_block_anchors` turns that into `2 ≤ version ∧ disable bit clear ∧ 1 ≤ nSequence`.
- `received_cheater_height`: with `BitcoinHtlcLocks.received_spend_height`, a two-element spend
  `[sig, pk]` of a received HTLC by the cheater that is final in a block at `height` has `expiry < height`.

(C) The race:

- `penalty_any_block`: the penalty witness is accepted in every context (the theorem carries no
  hypothesis on version / `nSequence` / lock time), and with `nLockTime = 0` the penalty transaction is
  `isFinalTx` at every height and block time.
- `cheater_needs_delay`: `¬ (version < 2 ∨ nSequence < toSelfDelay.toNat)` for every accepted cheater
  spend of `to_local` under the CSV flag (so BIP 68 holds it for `to_self_delay` blocks).

## What the unforgeability hypothesis says, and does not say

`NoRevocationSig o K` is a statement about one oracle (one spending transaction, input, amount and
script code) and one key: *this* checker accepts no signature for `revPk`. It is the right abstraction
for the script-level question "which branch can this witness take", but:

- it is not derived from anything: there is no key-derivation model (BOLT #3's
  `revocationpubkey = revocation_basepoint * SHA256(…) + per_commitment_point * SHA256(…)`), no secret
  keys, no signing oracle, no ECDSA; `checkSig` under `legacyOracle` is `checkSigPreTapscript … = some true`;
- it is per oracle, so the cheater's hypothesis must be assumed for each spending context separately
  (the honest party's `HoldsRevocation` likewise — `revoked_commitment_penalty` assumes it for every
  script code in one context);
- `NoRevHashPreimage` is a separate collision assumption on `hash160` that the HTLC scripts need and
  `to_local` does not (it pushes `revPk` itself);
- nothing is said about the network: the theorems compare script-level acceptance and the BIP 68 /
  `IsFinalTx` conditions, not mempool policy, fee bumping, propagation or who reaches a miner first.
  "The honest party wins the race" is: its transaction is acceptable in the very next block while the
  cheater's is not acceptable for `to_self_delay` blocks (`cheater_needs_delay` gives the `nSequence`
  requirement; the BIP 68 consequence lives in `BitcoinBIP68` / `BitcoinBlockV2.sequenceLocksOk` and is
  not composed here);
- the legacy (non-anchor) `to_remote` output is a P2WPKH and has no published theorem; only the
  anchors-form `to_remote` is covered (`to_remote_honest_only`);
- `castToBool (sha256 script) = true` (the P2WSH program is not a "zero" byte string) is a hypothesis,
  as in the sibling missions.

## Checks

- `lake build Solutions.Sol_BitcoinPenalty_all`: succeeds; the only `sorry` warnings are the twelve
  imported stubs (`ToLocal.p2wsh_spend/csv_concrete/lightning_delay/checkSequence_iff`,
  `Htlc.offered/received_p2wsh_spend`, `Anchors.offered/received/to_remote/anchor_p2wsh_spend`,
  `Anchors.anchor_anyone_delay`, `HtlcLocks.received_spend_height`).
- `pipeline.py stubs BitcoinPenalty …`: 21 stubs, build errors 0. `pipeline.py split …`: 21 split
  files, all `errors=0` (`sorryAx` from the imported stubs only).
- `tests/PenaltyVectors.lean` (`decide +kernel`, stub oracle): `to_local` penalty accepted at once,
  the delayed path rejected until 144 blocks, the wrong-key attempts on either branch leave a clean
  false; HTLC penalties (both forms) accepted at once, the cheater's preimage/success/timeout paths,
  and their one-block wait in anchors form; `to_remote` / anchor facts; `parseScript` of every byte
  form; explicit witnesses of `HoldsRevocation`, `DelayedSpend`, `*NonRevocation*`, and a check that
  the stub hash is *not* second-preimage resistant (why `NoRevHashPreimage` is a hypothesis).
