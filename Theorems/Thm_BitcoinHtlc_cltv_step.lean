import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.cltv_step (f : Flags) (o : Oracle) (s : State) (expiry : Int) (rest : List Bytes)
    (hs : s.stack = BitcoinScript.serialize expiry :: rest) (hd : expiry.natAbs < 2 ^ 32) :
    BitcoinScript.execOp f o true BitcoinScript.OP_CHECKLOCKTIMEVERIFY s =
      if BitcoinHtlc.CltvPasses f o expiry then some s else none := by sorry
