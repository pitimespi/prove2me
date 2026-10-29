import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.csv_concrete (f : Flags) (sf : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : Bytes) (delay : Int) (hcsv : f.csv = true) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16) :
    BitcoinToLocal.CsvPasses f (BitcoinSig.legacyOracle sf tx nIn amount v sc) delay ↔
      BitcoinSig.checkSequence tx nIn delay = true := by sorry
