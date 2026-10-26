import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.scriptpath_commitment (spent : List TxOut) (c : BitcoinVerify.Ctx) (stack : List Bytes)
    (script control q : Bytes) (hna : BitcoinTaproot.hasAnnex (stack ++ [script, control]) = false)
    (h : BitcoinTaproot.taprootHandler spent c (stack ++ [script, control]) q = true) :
    BitcoinTaproot.verifyTaprootCommitment control q
      (BitcoinTaproot.tapleafHash (BitVec.ofNat 8 ((control.getD 0 0).toNat &&& BitcoinTaproot.TAPROOT_LEAF_MASK)) script) = true := by sorry
