import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2wsh_correct (tap : TaprootHandler) (c : Ctx) (ws : List Bytes) (script : Bytes)
    (hf : c.flags.witness = true) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 script)) (ws ++ [script]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 script) = true ∧
      BitcoinVerify.executeWitnessScriptV0 c ws.reverse script = true := by sorry
