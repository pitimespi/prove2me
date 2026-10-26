import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.derEncode_valid (r s : Bytes) (ht : Byte) (hr : BitcoinSig.minimalInt r)
    (hs : BitcoinSig.minimalInt s) (hlen : r.length + s.length ≤ 66) :
    BitcoinSig.isValidSignatureEncoding (BitcoinSig.derEncode r s ht) = true := by sorry
