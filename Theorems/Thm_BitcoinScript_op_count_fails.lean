import Definitions.Def_BitcoinScript

theorem BitcoinScript.op_count_fails (f : Flags) (o : Oracle) (stack : List Bytes) (script : Script)
    (h : BitcoinScript.MAX_OPS_PER_SCRIPT < BitcoinScript.opsIn script) :
    BitcoinScript.evalScript f o stack script = none := by sorry
