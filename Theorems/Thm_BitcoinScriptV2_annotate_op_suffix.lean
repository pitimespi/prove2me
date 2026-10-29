import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.annotate_op_suffix (s : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (h : BitcoinScriptV2.annotate s = some l) (c : BitcoinScript.Byte) (r : BitcoinScript.Bytes) (hm : (.op c, r) ∈ l) :
    ∃ p, s[p]? = some c ∧ r = s.drop (p + 1) := by sorry
