import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.keypath_annex (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig annex q : Bytes)
    (ha : (annex.getD 0 0).toNat = BitcoinTaproot.ANNEX_TAG) (hne : annex ≠ []) :
    BitcoinTaproot.taprootHandler spent c [sig, annex] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false
        ⟨true, BitcoinSer.sha256 (BitcoinSer.serBytes annex), [], 0xFFFFFFFF⟩ := by sorry
