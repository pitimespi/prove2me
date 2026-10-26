import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSig
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.keypath_correct (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr c.tx spent c.nIn ht false ⟨false, [], [], 0xFFFFFFFF⟩ = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by sorry
