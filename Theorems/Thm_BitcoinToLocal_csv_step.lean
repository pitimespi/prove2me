import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.csv_step (f : Flags) (o : Oracle) (s : State) (delay : Int) (rest : List Bytes)
    (hs : s.stack = BitcoinScript.serialize delay :: rest) (hd : delay.natAbs < 2 ^ 32) :
    BitcoinScript.execOp f o true BitcoinScript.OP_CHECKSEQUENCEVERIFY s =
      if BitcoinToLocal.CsvPasses f o delay then some s else none := by sorry
