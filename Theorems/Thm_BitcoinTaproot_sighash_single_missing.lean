import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.sighash_single_missing (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (hv : hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83)) (h3 : hashType &&& 3 = 3) (hout : tx.vout.length ≤ inPos) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by sorry
