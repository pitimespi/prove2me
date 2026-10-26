import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.sigops_budget (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey sig : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: sig :: rest) (hsig : sig ≠ []) (hw : ts.weightLeft < BitcoinTaproot.VALIDATION_WEIGHT_PER_SIGOP_PASSED) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts = none := by sorry
