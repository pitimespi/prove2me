import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.merkleRoot_snoc (control node leaf : Bytes)
    (hc : BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE ≤ control.length)
    (hm : (control.length - BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) % BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE = 0)
    (hn : node.length = BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot (control ++ node) leaf =
      BitcoinTaproot.tapbranchHash (BitcoinTaproot.taprootMerkleRoot control leaf) node := by sorry
