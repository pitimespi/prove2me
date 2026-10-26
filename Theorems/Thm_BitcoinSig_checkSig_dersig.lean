import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.checkSig_dersig (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode sig pk : Bytes) (hf : f.dersig = true) (hne : sig ≠ [])
    (hder : BitcoinSig.isValidSignatureEncoding sig = false) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode sig pk = none := by sorry
