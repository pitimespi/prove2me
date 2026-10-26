import Definitions.Def_BitcoinPow

theorem BitcoinPow.checkProofOfWork_iff (hash : Nat) (nBits : BitVec 32) :
    BitcoinPow.checkProofOfWork hash nBits = true ↔
      BitcoinPow.compactNegative nBits = false ∧ BitcoinPow.compactOverflow nBits = false ∧
      0 < BitcoinPow.specTarget nBits ∧ BitcoinPow.specTarget nBits ≤ BitcoinPow.powLimit ∧
      hash ≤ BitcoinPow.specTarget nBits := by sorry
