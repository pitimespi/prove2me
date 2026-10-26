import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.checkSig_base_iff (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int)
    (scriptCode sig pk : Bytes) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount .base scriptCode sig pk = some true ↔
      BitcoinSig.checkSignatureEncoding f sig = true ∧ BitcoinSig.checkPubKeyEncoding f .base pk = true ∧
      BitcoinSig.pubkeyValid pk = true ∧
      ∃ (sig' : Bytes) (ht : Byte), sig = sig' ++ [ht] ∧
        BitcoinSig.pubkeyVerify pk
          (BitcoinSig.sigHashLegacy (BitcoinSig.findAndDelete scriptCode (BitcoinSig.pushBytes sig)).1 tx nIn ht.toNat)
          sig' = true := by sorry
