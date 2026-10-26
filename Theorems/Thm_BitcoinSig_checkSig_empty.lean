import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.checkSig_empty (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode pk : Bytes) (hpk : BitcoinSig.checkPubKeyEncoding f v pk = true) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode [] pk = some false := by sorry
