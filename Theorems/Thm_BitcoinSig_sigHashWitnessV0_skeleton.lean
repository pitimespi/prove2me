import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.sigHashWitnessV0_skeleton (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat) (amount : Int)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashWitnessV0 scriptCode tx' nIn hashType amount =
      BitcoinSig.sigHashWitnessV0 scriptCode tx nIn hashType amount := by sorry
