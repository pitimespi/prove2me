import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.parseScript_toLocal (rev dpk : Bytes) (delay : Int)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    BitcoinSig.parseScript (BitcoinToLocal.toLocalBytes rev delay dpk) = some (BitcoinToLocal.toLocalScript rev delay dpk) := by sorry
