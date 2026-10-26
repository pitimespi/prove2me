import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.checkmultisig_rejected (c : TapCtx) (ed : ExecData) (fExec : Bool) (ts : TapState) :
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIG ts = none ∧
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIGVERIFY ts = none := by sorry
