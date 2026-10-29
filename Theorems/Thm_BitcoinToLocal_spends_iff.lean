import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.spends_iff (f : Flags) (o : Oracle) (rev dpk : Bytes) (delay : Int) (st : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinToLocal.toLocalScript rev delay dpk) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      ∃ b sig, st = [b, sig] ∧ BitcoinToLocal.SpendCondition f o rev delay dpk b sig := by sorry
