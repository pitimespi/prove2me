import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.isWitnessProgram_iff (s : Bytes) (v : Nat) (prog : Bytes) :
    BitcoinVerify.isWitnessProgram s = some (v, prog) ↔
      v ≤ 16 ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 ∧ s = BitcoinVerify.witnessBytes v prog := by sorry
