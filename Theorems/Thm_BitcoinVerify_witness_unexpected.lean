import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.witness_unexpected (tap : TaprootHandler) (c : Ctx) (scriptSig spk : Bytes) (w : List Bytes)
    (hf : c.flags.witness = true) (hw : BitcoinVerify.isWitnessProgram spk = none)
    (hp : BitcoinVerify.isPayToScriptHash spk = false) (hne : w ≠ []) :
    BitcoinVerify.verifyScript tap c scriptSig spk w = false := by sorry
