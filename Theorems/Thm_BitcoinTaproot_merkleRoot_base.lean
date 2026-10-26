import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.merkleRoot_base (control leaf : Bytes) (h : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot control leaf = leaf := by sorry
