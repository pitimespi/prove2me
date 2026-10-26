import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.derEncode_complete (sig : Bytes) (h : BitcoinSig.isValidSignatureEncoding sig = true) :
    ∃ (r s : Bytes) (ht : Byte), sig = BitcoinSig.derEncode r s ht ∧ BitcoinSig.minimalInt r ∧
      BitcoinSig.minimalInt s ∧ r.length + s.length ≤ 66 := by sorry
