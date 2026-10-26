import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.native_witness_malleated (tap : TaprootHandler) (c : Ctx) (scriptSig spk : Bytes)
    (w : List Bytes) (hf : c.flags.witness = true) (hw : BitcoinVerify.isWitnessProgram spk ≠ none)
    (hs : scriptSig ≠ []) : BitcoinVerify.verifyScript tap c scriptSig spk w = false := by sorry
