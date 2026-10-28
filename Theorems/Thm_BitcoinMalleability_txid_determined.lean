import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.txid_determined (f : BitcoinActivation.ScriptFlags) (u : Ledger)
    (tx tx' : BitcoinSer.Tx) (hf : f.witness = true)
    (hI : BitcoinMalleability.intentOf tx = BitcoinMalleability.intentOf tx')
    (h : BitcoinBlockV2.inputScriptsOk f u tx = true) (h' : BitcoinBlockV2.inputScriptsOk f u tx' = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid tx' := by sorry
