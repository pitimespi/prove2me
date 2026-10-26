import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.opsuccess_accepts (c : TapCtx) (ed : ExecData) (stack : List Bytes) (script : Bytes) (weight : Int)
    (h : BitcoinTaproot.opSuccessScan script.length script = some true) :
    BitcoinTaproot.executeTapscript c ed stack script weight = true := by sorry
