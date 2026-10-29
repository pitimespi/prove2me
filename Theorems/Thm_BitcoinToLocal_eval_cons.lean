import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.eval_cons (f : Flags) (o : Oracle) (rev dpk b : Bytes) (delay : Int) (tl : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) (htl : tl.length + 1 ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (b :: tl) (BitcoinToLocal.toLocalScript rev delay dpk) =
      match tl with
      | [] => none
      | sig :: rest =>
        if BitcoinScript.castToBool b then (o.checkSig sig rev).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else if BitcoinToLocal.CsvPasses f o delay then (o.checkSig sig dpk).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else none := by sorry
