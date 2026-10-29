import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.annotate_suffix (s : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (h : BitcoinScriptV2.annotate s = some l) (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes) (hm : (i, r) ∈ l) :
    ∃ pre, s = pre ++ r := by sorry
