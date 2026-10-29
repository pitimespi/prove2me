import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.cltv_concrete (f : Flags) (sf : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : Bytes) (expiry : Int) (hcltv : f.cltv = true) (h0 : 0 ≤ expiry) :
    BitcoinHtlc.CltvPasses f (BitcoinSig.legacyOracle sf tx nIn amount v sc) expiry ↔
      BitcoinSig.checkLockTime tx nIn expiry = true := by sorry
