import Definitions.Def_BitcoinScript

theorem BitcoinScript.execOp_opCount (f : Flags) (o : Oracle) (e : Bool) (c : Byte) (s s' : State)
    (h : BitcoinScript.execOp f o e c s = some s') :
    s.opCount ≤ s'.opCount ∧ (s'.opCount = s.opCount ∨ s'.opCount ≤ BitcoinScript.MAX_OPS_PER_SCRIPT) := by sorry
