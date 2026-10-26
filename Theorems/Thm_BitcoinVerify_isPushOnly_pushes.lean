import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.isPushOnly_pushes (ps : List Bytes) (hp : ∀ p ∈ ps, p.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.isPushOnly (BitcoinVerify.pushesBytes ps) = true := by sorry
