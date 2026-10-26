import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.unknown_witness_version (tap : TaprootHandler) (c : Ctx) (v : Nat) (prog : Bytes)
    (w : List Bytes) (hf : c.flags.witness = true) (hv : v ≤ 16)
    (hu : 2 ≤ v ∨ (v = 1 ∧ prog.length ≠ 32)) (h2 : 2 ≤ prog.length) (h40 : prog.length ≤ 40) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes v prog) w = BitcoinScript.castToBool prog := by sorry
