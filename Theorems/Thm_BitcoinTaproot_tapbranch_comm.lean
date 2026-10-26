import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.tapbranch_comm (a b : Bytes) : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash b a := by sorry
