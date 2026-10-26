import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinSig BitcoinSer

theorem BitcoinSig.parseScript_p2pkh (h : Bytes) (hh : h.length = 20) :
    BitcoinSig.parseScript (BitcoinSig.p2pkhBytes h) = some (BitcoinScript.p2pkhScript h) := by sorry
