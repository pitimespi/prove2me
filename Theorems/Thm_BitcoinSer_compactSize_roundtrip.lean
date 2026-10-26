import Definitions.Def_BitcoinSer

theorem BitcoinSer.compactSize_roundtrip (n : Nat) (rest : Bytes) (h : n < 2 ^ 64) :
    BitcoinSer.readCompactSize false (BitcoinSer.writeCompactSize n ++ rest) = some (n, rest) := by sorry
