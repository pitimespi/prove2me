import Definitions.Def_BitcoinMalleability
import Theorems.Thm_BitcoinVerify_native_witness_malleated
import Theorems.Thm_BitcoinSer_txid_strip

open BitcoinMalleability BitcoinSer BitcoinBlockV2

/-- `CheckInputScripts` with the `WITNESS` flag: every input that spends a native witness program
has an empty `scriptSig`. -/
theorem solution (f : BitcoinActivation.ScriptFlags) (u : Ledger)
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
