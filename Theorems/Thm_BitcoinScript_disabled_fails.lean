import Definitions.Def_BitcoinScript

theorem BitcoinScript.disabled_fails (f : Flags) (o : Oracle) (script : Script) (c : Byte)
    (hc : BitcoinScript.isDisabled c = true) (hmem : Instr.op c ∈ script) :
    ∀ s : State, BitcoinScript.run f o s script = none := by sorry
