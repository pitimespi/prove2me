import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.checksig_empty (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: [] :: rest) (hpk : pubkey.length = 32) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts =
      some { ts with st := { ts.st with stack := BitcoinScript.boolBytes false :: rest } } := by sorry
