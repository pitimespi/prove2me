import Definitions.Def_BitcoinPenalty
import Theorems.Thm_BitcoinToLocal_p2wsh_spend
import Theorems.Thm_BitcoinToLocal_csv_concrete
import Theorems.Thm_BitcoinToLocal_lightning_delay
import Theorems.Thm_BitcoinToLocal_checkSequence_iff
import Theorems.Thm_BitcoinHtlc_offered_p2wsh_spend
import Theorems.Thm_BitcoinHtlc_received_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_offered_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_received_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_to_remote_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_anchor_p2wsh_spend
import Theorems.Thm_BitcoinAnchors_anchor_anyone_delay
import Theorems.Thm_BitcoinHtlcLocks_received_spend_height

open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

/-! # The Lightning penalty at the script level

Every theorem below is a corollary of the published `*_p2wsh_spend` characterisations (imported as
public theorems of the `BitcoinToLocal`, `BitcoinHtlc` and `BitcoinAnchors` missions) together with
`csv_concrete`, `checkSequence_iff`, `lightning_delay`, `anchor_anyone_delay` and
`BitcoinHtlcLocks.received_spend_height`. The oracle is the concrete `legacyOracle` of the spending
context (`BitcoinPenalty.oracleOf`). -/

/-! ### Private helpers -/

private theorem delay_natAbs (K : CommitmentKeys) (hK : WellFormed K) : K.toSelfDelay.natAbs < 2 ^ 32 := by
  have := hK.delayNonneg; have := hK.delayLt; omega

private theorem reverse_two (a b : BitcoinSer.Bytes) : [a, b].reverse = [b, a] := by simp

private theorem mem_two_le (a b : BitcoinSer.Bytes) (ha : a.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hb : b.length ≤ MAX_SCRIPT_ELEMENT_SIZE) : ∀ e ∈ [a, b], e.length ≤ MAX_SCRIPT_ELEMENT_SIZE := by
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact ha
  · exact hb

/-- A passing `OP_CHECKSEQUENCEVERIFY` under the concrete oracle, in transaction terms: version at
least 2, the disable bit clear, and `nSequence` at least the operand. -/
private theorem csv_tx (c : Ctx) (sc : BitcoinSer.Bytes) (delay : Int) (hcsv : c.flags.csv = true)
    (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16)
    (h : CsvPasses (scriptFlagsOf c.flags) (oracleOf c sc) delay) :
    2 ≤ c.tx.version ∧ inputSequence c.tx c.nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      delay.toNat ≤ inputSequence c.tx c.nIn := by
  have hcs : checkSequence c.tx c.nIn delay = true :=
    (BitcoinToLocal.csv_concrete (scriptFlagsOf c.flags) (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 sc delay
      hcsv h0 h16).1 h
  have := (BitcoinToLocal.checkSequence_iff c.tx c.nIn delay h0 h16).1 hcs
  exact ⟨this.1, this.2.1, Nat.le_trans this.2.2.2 Nat.and_le_left⟩

/-! ### (A) Penalty completeness: the holder of the revocation key spends at once -/

/-- **`to_local` penalty, explicit signature.** Any signature the concrete oracle accepts for the
revocation key, pushed with the selector `1`, spends the `to_local` output: no delay check is run
on the `OP_IF` branch. No hypothesis on the spending transaction's version, `nSequence` or
`nLockTime`. -/
theorem BitcoinPenalty.to_local_penalty_sig (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toLocalBytes K)) = true)
    (sigR : BitcoinSer.Bytes) (hlen : sigR.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hsig : (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)).checkSig sigR K.revPk = some true) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true := by
  simp only [BitcoinPenalty.toLocalPenaltyWitness, BitcoinPenalty.p2wshOf, BitcoinPenalty.toLocalBytes,
    BitcoinPenalty.oracleOf] at hh hsig ⊢
  exact (BitcoinToLocal.p2wsh_spend tap c hf K.revPk K.localDelayedPk K.toSelfDelay [sigR, [1]]
    hK.revPk hK.localDelayedPk (delay_natAbs K hK)).2
    ⟨hh, [1], sigR, rfl, hlen, by decide, Or.inl ⟨by decide, hsig⟩⟩

/-- **`to_local` penalty.** Under `HoldsRevocation` there is a witness `<revocation_sig> 1 <script>`
that `verifyScript` accepts, in any spending context. -/
theorem BitcoinPenalty.to_local_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toLocalBytes K)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true := by
  obtain ⟨⟨sigR, hlen, hsig⟩, _⟩ := hR
  exact ⟨sigR, BitcoinPenalty.to_local_penalty_sig tap c hf K hK hh sigR hlen hsig⟩

/-- **Offered-HTLC penalty (non-anchor form).** Under `HoldsRevocation` the witness
`<revocation_sig> <revocationpubkey> <script>` spends an offered HTLC output at once. -/
theorem BitcoinPenalty.offered_htlc_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.offeredBytes K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytes K h)) = true := by
  obtain ⟨⟨sigR, hlen, hsig⟩, hrev⟩ := hR
  refine ⟨sigR, ?_⟩
  simp only [BitcoinPenalty.htlcPenaltyWitness, BitcoinPenalty.p2wshOf, BitcoinPenalty.offeredBytes,
    BitcoinPenalty.oracleOf] at hh hsig hrev ⊢
  exact (BitcoinHtlc.offered_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash [sigR, K.revPk]
    hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash).2
    ⟨hh, mem_two_le sigR K.revPk hlen hK.revPk, Or.inl ⟨K.revPk, sigR, reverse_two sigR K.revPk, hrev, hsig⟩⟩

/-- **Received-HTLC penalty (non-anchor form).** -/
theorem BitcoinPenalty.received_htlc_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.receivedBytes K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytes K h)) = true := by
  obtain ⟨⟨sigR, hlen, hsig⟩, hrev⟩ := hR
  refine ⟨sigR, ?_⟩
  simp only [BitcoinPenalty.htlcPenaltyWitness, BitcoinPenalty.p2wshOf, BitcoinPenalty.receivedBytes,
    BitcoinPenalty.oracleOf] at hh hsig hrev ⊢
  exact (BitcoinHtlc.received_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash h.expiry
    [sigR, K.revPk] hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash hw.expiry).2
    ⟨hh, mem_two_le sigR K.revPk hlen hK.revPk, Or.inl ⟨K.revPk, sigR, reverse_two sigR K.revPk, hrev, hsig⟩⟩

/-- **Offered-HTLC penalty with `option_anchors`.** The revocation path skips the
`1 OP_CHECKSEQUENCEVERIFY` suffix, so no delay applies. -/
theorem BitcoinPenalty.offered_htlc_penalty_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.offeredBytesAnchors K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytesAnchors K h)) = true := by
  obtain ⟨⟨sigR, hlen, hsig⟩, hrev⟩ := hR
  refine ⟨sigR, ?_⟩
  simp only [BitcoinPenalty.htlcPenaltyWitness, BitcoinPenalty.p2wshOf, BitcoinPenalty.offeredBytesAnchors,
    BitcoinPenalty.oracleOf] at hh hsig hrev ⊢
  exact (BitcoinAnchors.offered_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash [sigR, K.revPk]
    hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash).2
    ⟨hh, mem_two_le sigR K.revPk hlen hK.revPk, Or.inl ⟨K.revPk, sigR, reverse_two sigR K.revPk, hrev, hsig⟩⟩

/-- **Received-HTLC penalty with `option_anchors`.** -/
theorem BitcoinPenalty.received_htlc_penalty_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.receivedBytesAnchors K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytesAnchors K h)) = true := by
  obtain ⟨⟨sigR, hlen, hsig⟩, hrev⟩ := hR
  refine ⟨sigR, ?_⟩
  simp only [BitcoinPenalty.htlcPenaltyWitness, BitcoinPenalty.p2wshOf, BitcoinPenalty.receivedBytesAnchors,
    BitcoinPenalty.oracleOf] at hh hsig hrev ⊢
  exact (BitcoinAnchors.received_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash h.expiry
    [sigR, K.revPk] hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash hw.expiry).2
    ⟨hh, mem_two_le sigR K.revPk hlen hK.revPk, Or.inl ⟨K.revPk, sigR, reverse_two sigR K.revPk, hrev, hsig⟩⟩

/-- **A whole revoked commitment, one context.** If in the spending context `c` the honest party
has an accepted revocation signature for every witness script (`∀ sc, HoldsRevocation (oracleOf c sc) K`),
then `to_local`, the offered and received HTLC outputs (both forms) all have an accepted penalty
witness. -/
theorem BitcoinPenalty.revoked_commitment_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hR : ∀ sc, BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c sc) K)
    (hh : ∀ sc ∈ [BitcoinPenalty.toLocalBytes K, BitcoinPenalty.offeredBytes K h, BitcoinPenalty.receivedBytes K h,
        BitcoinPenalty.offeredBytesAnchors K h, BitcoinPenalty.receivedBytesAnchors K h],
      BitcoinScript.castToBool (BitcoinSer.sha256 sc) = true) :
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
        (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytesAnchors K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytesAnchors K h)) = true) := by
  refine ⟨BitcoinPenalty.to_local_penalty tap c hf K hK (hh _ (by simp)) (hR _),
    BitcoinPenalty.offered_htlc_penalty tap c hf K hK h hw (hh _ (by simp)) (hR _),
    BitcoinPenalty.received_htlc_penalty tap c hf K hK h hw (hh _ (by simp)) (hR _),
    BitcoinPenalty.offered_htlc_penalty_anchors tap c hf K hK h hw (hh _ (by simp)) (hR _),
    BitcoinPenalty.received_htlc_penalty_anchors tap c hf K hK h hw (hh _ (by simp)) (hR _)⟩

/-- **`to_remote` needs no penalty.** With `option_anchors` the `to_remote` output is spendable
exactly by a lone signature for the remote key after the one-block delay: it is the counterparty's
own balance, and the broadcaster has no path to it. -/
theorem BitcoinPenalty.to_remote_honest_only (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (ws : List BitcoinSer.Bytes) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toRemoteBytes K))
        (ws ++ [BitcoinPenalty.toRemoteBytes K]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toRemoteBytes K)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      ∃ sig, ws = [sig] ∧
        (BitcoinPenalty.oracleOf c (BitcoinPenalty.toRemoteBytes K)).checkSig sig K.remoteKey = some true ∧
        BitcoinToLocal.CsvPasses (BitcoinVerify.scriptFlagsOf c.flags)
          (BitcoinPenalty.oracleOf c (BitcoinPenalty.toRemoteBytes K)) 1 := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.toRemoteBytes, BitcoinPenalty.oracleOf]
  rw [BitcoinAnchors.to_remote_p2wsh_spend tap c hf K.remoteKey ws hK.remoteKey]
  unfold BitcoinAnchors.ToRemoteSpend
  constructor
  · rintro ⟨h1, h2, sig, hws, h3⟩
    refine ⟨h1, h2, sig, ?_, h3⟩
    have := congrArg List.reverse hws
    simpa using this
  · rintro ⟨h1, h2, sig, hws, h3⟩
    subst hws
    exact ⟨h1, h2, sig, rfl, h3⟩

/-- **Anchors: the key holder at once, anyone after 16 blocks.** Each anchor (keyed by one side's
funding key) is spendable exactly by a lone element that is either an accepted signature for that
key, or a cleanly rejected one (such as the empty signature) with the 16-block delay check passing. -/
theorem BitcoinPenalty.anchor_holder_or_delay (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (fk : BitcoinSer.Bytes) (hfk : fk = K.fundingKeyLocal ∨ fk = K.fundingKeyRemote) (ws : List BitcoinSer.Bytes) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinAnchors.anchorBytes fk))
        (ws ++ [BitcoinAnchors.anchorBytes fk]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fk)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      ∃ sig, ws = [sig] ∧
        ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some true ∨
          ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some false ∧
            BitcoinToLocal.CsvPasses (BitcoinVerify.scriptFlagsOf c.flags)
              (BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)) 16)) := by
  have hlen : fk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE := by
    rcases hfk with rfl | rfl
    · exact hK.fundingKeyLocal
    · exact hK.fundingKeyRemote
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.oracleOf]
  rw [BitcoinAnchors.anchor_p2wsh_spend tap c hf fk ws hlen]
  unfold BitcoinAnchors.AnchorSpend
  constructor
  · rintro ⟨h1, h2, sig, hws, h3⟩
    refine ⟨h1, h2, sig, ?_, h3⟩
    have := congrArg List.reverse hws
    simpa using this
  · rintro ⟨h1, h2, sig, hws, h3⟩
    subst hws
    exact ⟨h1, h2, sig, rfl, h3⟩

/-- **Anchors, the anyone-can-spend path in transaction terms.** The empty-signature witness
spends an anchor exactly when the spending transaction has version at least 2 and a (flag-free)
`nSequence` of at least 16. -/
theorem BitcoinPenalty.anchor_anyone_after_16 (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (fk : BitcoinSer.Bytes) (hfk : fk = K.fundingKeyLocal ∨ fk = K.fundingKeyRemote)
    (hseq : BitcoinToLocal.inputSequence c.tx c.nIn < 2 ^ 16) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinAnchors.anchorBytes fk))
        [[], BitcoinAnchors.anchorBytes fk] = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fk)) = true ∧
      2 ≤ c.tx.version ∧ 16 ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by
  have hlen : fk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE := by
    rcases hfk with rfl | rfl
    · exact hK.fundingKeyLocal
    · exact hK.fundingKeyRemote
  simp only [BitcoinPenalty.p2wshOf]
  exact BitcoinAnchors.anchor_anyone_delay tap c hf hcsv fk hlen hseq

/-! ### (B) Penalty safety: the cheater is held to the delayed and non-revocation paths -/

/-- **The cheater's `to_local` spend is delayed.** If the concrete oracle accepts no signature for the
revocation key, every witness `verifyScript` accepts for `to_local` is `<sig> <b>` with `b` false
(the `OP_ELSE` branch), the `to_self_delay` check passing, and `sig` valid for the delayed key. -/
theorem BitcoinPenalty.to_local_cheater_delayed (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true) :
    ∃ b sig, ws = [sig, b] ∧
      BitcoinPenalty.DelayedSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K b sig := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.toLocalBytes, BitcoinPenalty.oracleOf,
    BitcoinPenalty.NoRevocationSig, BitcoinPenalty.DelayedSpend] at hN hv ⊢
  obtain ⟨_, b, sig, hws, _, _, hsc⟩ := (BitcoinToLocal.p2wsh_spend tap c hf K.revPk K.localDelayedPk K.toSelfDelay ws
    hK.revPk hK.localDelayedPk (delay_natAbs K hK)).1 hv
  refine ⟨b, sig, hws, ?_⟩
  rcases hsc with ⟨_, hsig⟩ | ⟨hb, hcsv, hsig⟩
  · exact absurd hsig (hN sig)
  · exact ⟨hb, hcsv, hsig⟩

/-- **The cheater's delay in transaction terms** (via `lightning_delay`). Under the
`CHECKSEQUENCEVERIFY` flag and a flag-free `nSequence`, a `to_local` spend by a party without a
revocation signature can only be a version-2 (or later) transaction whose input `nSequence` is at
least `to_self_delay`: BIP 68 then holds it back by that many blocks. -/
theorem BitcoinPenalty.cheater_delay_in_tx_terms (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true)
    (hseq : BitcoinToLocal.inputSequence c.tx c.nIn < 2 ^ 16) :
    2 ≤ c.tx.version ∧ K.toSelfDelay.toNat ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by
  obtain ⟨b, sig, _, _, hcs, _⟩ := BitcoinPenalty.to_local_cheater_delayed tap c hf K hK hN ws hv
  have h1 : BitcoinSig.checkSequence c.tx c.nIn K.toSelfDelay = true :=
    (BitcoinToLocal.csv_concrete (BitcoinVerify.scriptFlagsOf c.flags) (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn
      c.amount .witnessV0 (BitcoinPenalty.toLocalBytes K) K.toSelfDelay hcsv hK.delayNonneg hK.delayLt).1 hcs
  exact (BitcoinToLocal.lightning_delay c.tx c.nIn K.toSelfDelay hK.delayNonneg hK.delayLt hseq).1 h1

/-- **The cheater's delay for any `nSequence`** (via `checkSequence_iff`): version at least 2, the
BIP 68 disable bit clear, and `nSequence ≥ to_self_delay`. -/
theorem BitcoinPenalty.cheater_delay_any_sequence (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true) :
    2 ≤ c.tx.version ∧
      BitcoinToLocal.inputSequence c.tx c.nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      K.toSelfDelay.toNat ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by
  obtain ⟨b, sig, _, _, hcs, _⟩ := BitcoinPenalty.to_local_cheater_delayed tap c hf K hK hN ws hv
  exact csv_tx c (BitcoinPenalty.toLocalBytes K) K.toSelfDelay hcsv hK.delayNonneg hK.delayLt hcs

/-- **Offered HTLC (non-anchor): the cheater never takes the revocation path.** Without a
revocation signature, and with `revPk` the only preimage of `revHash`, every accepted spend is a
preimage spend or a timeout spend. -/
theorem BitcoinPenalty.offered_cheater_no_revocation (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
      (ws ++ [BitcoinPenalty.offeredBytes K h]) = true) :
    BitcoinPenalty.OfferedNonRevocation (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K h ws.reverse := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.offeredBytes, BitcoinPenalty.oracleOf,
    BitcoinPenalty.NoRevocationSig, BitcoinPenalty.NoRevHashPreimage, BitcoinPenalty.OfferedNonRevocation] at hN hP hv ⊢
  obtain ⟨_, _, hsp⟩ := (BitcoinHtlc.offered_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash ws
    hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash).1 hv
  rcases hsp with ⟨pk, sig, _, hpk, hsig⟩ | hrest
  · have := hP pk hpk
    subst this
    exact absurd hsig (hN sig)
  · exact hrest

/-- **Received HTLC (non-anchor): the cheater never takes the revocation path.** -/
theorem BitcoinPenalty.received_cheater_no_revocation (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
      (ws ++ [BitcoinPenalty.receivedBytes K h]) = true) :
    BitcoinPenalty.ReceivedNonRevocation (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K h ws.reverse := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.receivedBytes, BitcoinPenalty.oracleOf,
    BitcoinPenalty.NoRevocationSig, BitcoinPenalty.NoRevHashPreimage, BitcoinPenalty.ReceivedNonRevocation] at hN hP hv ⊢
  obtain ⟨_, _, hsp⟩ := (BitcoinHtlc.received_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash
    h.expiry ws hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash hw.expiry).1 hv
  rcases hsp with ⟨pk, sig, _, hpk, hsig⟩ | hrest
  · have := hP pk hpk
    subst this
    exact absurd hsig (hN sig)
  · exact hrest

/-- **Offered HTLC with `option_anchors`: the cheater never takes the revocation path**, and the
one-block delay check applies to whatever path it takes. -/
theorem BitcoinPenalty.offered_cheater_no_revocation_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
      (ws ++ [BitcoinPenalty.offeredBytesAnchors K h]) = true) :
    BitcoinPenalty.OfferedNonRevocationAnchors (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K h ws.reverse := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.offeredBytesAnchors, BitcoinPenalty.oracleOf,
    BitcoinPenalty.NoRevocationSig, BitcoinPenalty.NoRevHashPreimage, BitcoinPenalty.OfferedNonRevocationAnchors,
    BitcoinPenalty.OfferedNonRevocation] at hN hP hv ⊢
  obtain ⟨_, _, hsp⟩ := (BitcoinAnchors.offered_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash ws
    hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash).1 hv
  rcases hsp with ⟨pk, sig, _, hpk, hsig⟩ | ⟨preimage, sig, hws, h1, h2, h3, h4, h5⟩ |
    ⟨x, localSig, remoteSig, dummy, hws, h1, h2, h3, h4, h5⟩
  · have := hP pk hpk
    subst this
    exact absurd hsig (hN sig)
  · exact ⟨Or.inl ⟨preimage, sig, hws, h1, h2, h3, h4⟩, h5⟩
  · exact ⟨Or.inr ⟨x, localSig, remoteSig, dummy, hws, h1, h2, h3, h4⟩, h5⟩

/-- **Received HTLC with `option_anchors`: the cheater never takes the revocation path**, and the
one-block delay check applies to whatever path it takes. -/
theorem BitcoinPenalty.received_cheater_no_revocation_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
      (ws ++ [BitcoinPenalty.receivedBytesAnchors K h]) = true) :
    BitcoinPenalty.ReceivedNonRevocationAnchors (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytesAnchors K h)) K h ws.reverse := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.receivedBytesAnchors, BitcoinPenalty.oracleOf,
    BitcoinPenalty.NoRevocationSig, BitcoinPenalty.NoRevHashPreimage, BitcoinPenalty.ReceivedNonRevocationAnchors,
    BitcoinPenalty.ReceivedNonRevocation] at hN hP hv ⊢
  obtain ⟨_, _, hsp⟩ := (BitcoinAnchors.received_p2wsh_spend tap c hf K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash
    h.expiry ws hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash hw.expiry).1 hv
  rcases hsp with ⟨pk, sig, _, hpk, hsig⟩ | ⟨preimage, localSig, remoteSig, dummy, hws, h1, h2, h3, h4, h5, h6⟩ |
    ⟨x, sig, hws, h1, h2, h3, h4, h5⟩
  · have := hP pk hpk
    subst this
    exact absurd hsig (hN sig)
  · exact ⟨Or.inl ⟨preimage, localSig, remoteSig, dummy, hws, h1, h2, h3, h4, h5⟩, h6⟩
  · exact ⟨Or.inr ⟨x, sig, hws, h1, h2, h3, h4⟩, h5⟩

/-- **The cheater's HTLC spends with `option_anchors` wait one block.** In transaction terms: the
spending transaction has version at least 2, the disable bit clear and `nSequence ≥ 1`. -/
theorem BitcoinPenalty.htlc_cheater_one_block_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
      (ws ++ [BitcoinPenalty.offeredBytesAnchors K h]) = true) :
    2 ≤ c.tx.version ∧
      BitcoinToLocal.inputSequence c.tx c.nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      1 ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by
  have := (BitcoinPenalty.offered_cheater_no_revocation_anchors tap c hf K hK h hw hN hP ws hv).2
  exact csv_tx c (BitcoinPenalty.offeredBytesAnchors K h) 1 hcsv (by decide) (by decide) this

/-- **A received HTLC the cheater spends with a two-element witness is past its expiry.** Combining
`BitcoinHtlcLocks.received_spend_height` with the unforgeability hypotheses: a transaction spending
a received HTLC output of the revoked commitment with `[sig, pk]`, final in a block at height
`height`, has `cltv_expiry < height` (the revocation alternative is excluded). -/
theorem BitcoinPenalty.received_cheater_height (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcltv : c.flags.cltv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hexp : 0 < h.expiry ∧ h.expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (hnIn : c.nIn < c.tx.vin.length)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K)
    (sig pk : BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
      ([sig, pk] ++ [BitcoinPenalty.receivedBytes K h]) = true)
    (height : Nat) (blockTime : Int) (hfinal : BitcoinBlockV2.isFinalTx c.tx height blockTime = true) :
    h.expiry < height := by
  simp only [BitcoinPenalty.p2wshOf, BitcoinPenalty.receivedBytes, BitcoinPenalty.oracleOf,
    BitcoinPenalty.NoRevocationSig, BitcoinPenalty.NoRevHashPreimage] at hN hP hv
  rcases BitcoinHtlcLocks.received_spend_height tap c hf hcltv K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash h.expiry
    sig pk hK.revHash hK.remoteHtlcKey hK.localHtlcKey hw.payHash hexp hnIn hv height blockTime hfinal with
    ⟨hpk, hsig⟩ | hlt
  · exfalso
    have := hP pk hpk
    subst this
    exact hN sig hsig
  · exact hlt

/-! ### (C) The race -/

/-- **The penalty is valid in any block.** The honest party's `to_local` penalty witness is accepted
in every spending context (no condition on `version` or `nSequence`: the theorem has none), and a
penalty transaction with `nLockTime = 0` is final at every height and block time. -/
theorem BitcoinPenalty.penalty_any_block (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toLocalBytes K)) = true)
    (sigR : BitcoinSer.Bytes) (hlen : sigR.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hsig : (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)).checkSig sigR K.revPk = some true)
    (hlock : c.tx.nLockTime = 0) (height : Nat) (blockTime : Int) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
        (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true ∧
      BitcoinBlockV2.isFinalTx c.tx height blockTime = true := by
  refine ⟨BitcoinPenalty.to_local_penalty_sig tap c hf K hK hh sigR hlen hsig, ?_⟩
  simp [BitcoinBlockV2.isFinalTx, hlock]

/-- **The cheater cannot win the race.** In the same transaction terms as `cheater_delay_in_tx_terms`,
stated for the race: whatever witness the cheater uses on `to_local`, its spending transaction is
version 2 or later with `nSequence ≥ to_self_delay`, so (BIP 68) it is not accepted before
`to_self_delay` blocks have been mined on top of the commitment, while the penalty needs no such
wait (`penalty_any_block`). -/
theorem BitcoinPenalty.cheater_needs_delay (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true) :
    ¬ (c.tx.version < 2 ∨ BitcoinToLocal.inputSequence c.tx c.nIn < K.toSelfDelay.toNat) := by
  have := BitcoinPenalty.cheater_delay_any_sequence tap c hf hcsv K hK hN ws hv
  omega
