import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- The order in which the height-dependent flags switch on: DERSIG, then CLTV, then CSV, then
NULLDUMMY. -/
theorem solution (height : Nat) :
    let f := BitcoinActivation.blockScriptFlags height .none
    (f.cltv = true → f.dersig = true) ∧ (f.csv = true → f.cltv = true) ∧
    (f.nulldummy = true → f.csv = true) := by
  intro f
  unfold f blockScriptFlags exceptionBase baseFlags activeAt deploymentHeight
  simp only [Bool.false_or, decide_eq_true_eq]
  omega
