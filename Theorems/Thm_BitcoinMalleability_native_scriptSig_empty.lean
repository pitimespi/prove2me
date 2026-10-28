import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinVerify
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.native_scriptSig_empty (f : BitcoinActivation.ScriptFlags) (u : Ledger)
    (tx : BitcoinSer.Tx) (hf : f.witness = true) (h : BitcoinBlockV2.inputScriptsOk f u tx = true) :
    ∀ i ∈ tx.vin, BitcoinVerify.isWitnessProgram (BitcoinBlockV2.accessCoin u i.prevout).out.scriptPubKey ≠ none →
      i.scriptSig = [] := by sorry
