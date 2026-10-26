import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.keypath_handler (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false ⟨false, [], [], 0xFFFFFFFF⟩ := by sorry
