import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_order (height : Nat) :
    let f := BitcoinActivation.blockScriptFlags height .none
    (f.cltv = true → f.dersig = true) ∧ (f.csv = true → f.cltv = true) ∧
    (f.nulldummy = true → f.csv = true) := by sorry
