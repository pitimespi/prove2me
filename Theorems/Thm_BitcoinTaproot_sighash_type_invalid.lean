import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.sighash_type_invalid (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (h : ¬ (hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83))) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by sorry
