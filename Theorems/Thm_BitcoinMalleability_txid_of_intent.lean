import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.txid_of_intent (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : BitcoinSer.Tx)
    (hf : f.witness = true) (h : BitcoinBlockV2.inputScriptsOk f u tx = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid (BitcoinMalleability.ofIntent (BitcoinMalleability.intentOf tx)) := by sorry
