import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.minimalif_rejects (c : TapCtx) (ed : ExecData) (ts : TapState) (top : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = top :: rest) (h : 1 < top.length ∨ (top.length = 1 ∧ (top.getD 0 0).toNat ≠ 1)) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_IF ts = none := by sorry
