import Definitions.Def_BitcoinMalleability
import Theorems.Thm_BitcoinVerify_native_witness_malleated
import Theorems.Thm_BitcoinSer_txid_strip

open BitcoinMalleability BitcoinSer BitcoinBlockV2

/-! ### Native witness programs force an empty scriptSig -/

/-- `CheckInputScripts` with the `WITNESS` flag: every input that spends a native witness program
has an empty `scriptSig`. -/
theorem BitcoinMalleability.native_scriptSig_empty (f : BitcoinActivation.ScriptFlags) (u : Ledger)
    (tx : BitcoinSer.Tx) (hf : f.witness = true) (h : BitcoinBlockV2.inputScriptsOk f u tx = true) :
    ∀ i ∈ tx.vin, BitcoinVerify.isWitnessProgram (BitcoinBlockV2.accessCoin u i.prevout).out.scriptPubKey ≠ none →
      i.scriptSig = [] := by
  intro i hi hw
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hi
  simp only [inputScriptsOk, List.all_eq_true, List.mem_range] at h
  have hn' := h n hn
  have hd : tx.vin.getD n ⟨⟨[], 0⟩, [], 0, []⟩ = i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some, hget]
  rw [hd] at hn'
  simp only [BitcoinTaproot.verifyScriptFull] at hn'
  by_cases hne : i.scriptSig = []
  · exact hne
  · have := BitcoinVerify.native_witness_malleated (BitcoinTaproot.taprootHandler (tx.vin.map fun j => (accessCoin u j.prevout).out))
      ⟨f, tx, n, (accessCoin u i.prevout).out.nValue⟩ i.scriptSig _ i.witness hf hw hne
    rw [this] at hn'
    cases hn'

/-! ### The txid is a function of the intent -/

private theorem stripWitness_eq_ofIntent (tx : BitcoinSer.Tx) (h : ∀ i ∈ tx.vin, i.scriptSig = []) :
    tx.stripWitness = ofIntent (intentOf tx) := by
  simp only [BitcoinSer.Tx.stripWitness, ofIntent, intentOf, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := h i hi
  cases i; simp_all

/-- For a transaction whose inputs all spend native witness programs and whose scripts verify, the
txid is the txid of the canonical transaction of its intent: no signature data enters it. -/
theorem BitcoinMalleability.txid_of_intent (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : BitcoinSer.Tx)
    (hf : f.witness = true) (h : BitcoinBlockV2.inputScriptsOk f u tx = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid (BitcoinMalleability.ofIntent (BitcoinMalleability.intentOf tx)) := by
  rw [BitcoinSer.txid_strip tx]
  rw [stripWitness_eq_ofIntent tx (fun i hi => BitcoinMalleability.native_scriptSig_empty f u tx hf h i hi (hw i hi))]

/-- **Non-malleability.** Two transactions with the same intent, both of whose scripts verify
against the same ledger, where the inputs spend native witness programs, have the same txid: no
choice of signatures or witnesses, by the signer or by a third party, changes it. -/
theorem BitcoinMalleability.txid_determined (f : BitcoinActivation.ScriptFlags) (u : Ledger)
    (tx tx' : BitcoinSer.Tx) (hf : f.witness = true)
    (hI : BitcoinMalleability.intentOf tx = BitcoinMalleability.intentOf tx')
    (h : BitcoinBlockV2.inputScriptsOk f u tx = true) (h' : BitcoinBlockV2.inputScriptsOk f u tx' = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid tx' := by
  have hw' : SpendsWitnessPrograms u tx' := by
    intro i' hi'
    have hmap : tx.vin.map (fun i => (i.prevout, i.nSequence)) = tx'.vin.map (fun i => (i.prevout, i.nSequence)) := by
      have := congrArg Intent.inputs hI; simpa [intentOf] using this
    have hm : (i'.prevout, i'.nSequence) ∈ tx.vin.map (fun i => (i.prevout, i.nSequence)) := by
      rw [hmap]; exact List.mem_map_of_mem hi'
    obtain ⟨i, hi, heq⟩ := List.mem_map.1 hm
    have hp : i.prevout = i'.prevout := (Prod.mk.inj heq).1
    rw [← hp]; exact hw i hi
  rw [BitcoinMalleability.txid_of_intent f u tx hf h hw, BitcoinMalleability.txid_of_intent f u tx' hf h' hw', hI]

/-! ### P2SH-wrapped witness programs -/

private theorem isWitnessProgram_p2sh (spk : BitcoinSer.Bytes) (h : BitcoinVerify.isPayToScriptHash spk = true) :
    BitcoinVerify.isWitnessProgram spk = none := by
  simp only [BitcoinVerify.isPayToScriptHash, Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 : (spk.getD 0 0).toNat = 169 := h.1.1.2
  simp only [BitcoinVerify.isWitnessProgram, h.1.1.1, h0]
  rw [if_neg (by omega), if_pos (by omega)]

/-- A P2SH output spent with witness data: `VerifyScript` succeeds only if the `scriptSig` is
exactly the push of the redeem script it evaluates to, and that redeem script is a witness program
(`SCRIPT_ERR_WITNESS_MALLEATED_P2SH`). -/
theorem BitcoinMalleability.p2sh_wrapped_scriptSig (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (sig spk : BitcoinSer.Bytes) (w : List BitcoinSer.Bytes) (hp : c.flags.p2sh = true) (hf : c.flags.witness = true)
    (hspk : BitcoinVerify.isPayToScriptHash spk = true) (hw : w ≠ [])
    (hv : BitcoinVerify.verifyScript tap c sig spk w = true) :
    ∃ redeem rest, BitcoinVerify.evalBytes c .base [] sig = some (redeem :: rest) ∧
      BitcoinVerify.isWitnessProgram redeem ≠ none ∧ sig = BitcoinSig.pushBytes redeem := by
  have hnw := isWitnessProgram_p2sh spk hspk
  unfold BitcoinVerify.verifyScript at hv
  cases hsig : BitcoinVerify.evalBytes c .base [] sig with
  | none => simp only [hsig] at hv; cases hv
  | some stackSig =>
    simp only [hsig] at hv
    cases hspk' : BitcoinVerify.evalBytes c .base stackSig spk with
    | none => simp only [hspk'] at hv; cases hv
    | some stack =>
      simp only [hspk'] at hv
      simp only [hf, hnw, hp, hspk, Bool.true_and, ite_true] at hv
      by_cases ht : BitcoinVerify.topTrue stack = true
      · simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false] at hv
        by_cases hpo : BitcoinVerify.isPushOnly sig = true
        · simp only [hpo, Bool.not_true, Bool.false_eq_true, ite_false] at hv
          cases stackSig with
          | nil => cases hv
          | cons redeem rest =>
            refine ⟨redeem, rest, rfl, ?_⟩
            dsimp only at hv
            cases hev : BitcoinVerify.evalBytes c .base rest redeem with
            | none => simp only [hev] at hv; cases hv
            | some st2 =>
              simp only [hev] at hv
              by_cases ht2 : BitcoinVerify.topTrue st2 = true
              · simp only [ht2, Bool.not_true, Bool.false_eq_true, ite_false] at hv
                cases hwr : BitcoinVerify.isWitnessProgram redeem with
                | none =>
                  simp only [hwr] at hv
                  have : w.isEmpty = true := by
                    cases hemp : w.isEmpty
                    · simp [hemp, hf] at hv
                    · rfl
                  exact absurd (List.isEmpty_iff.1 this) hw
                | some vp =>
                  simp only [hwr] at hv
                  refine ⟨by simp, ?_⟩
                  by_cases hne : sig = BitcoinSig.pushBytes redeem
                  · exact hne
                  · simp [hne] at hv
              · simp [ht2] at hv
        · simp [hpo] at hv
      · simp [ht] at hv
