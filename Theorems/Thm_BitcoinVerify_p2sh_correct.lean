import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2sh_correct (tap : TaprootHandler) (c : Ctx) (args : List Bytes) (redeem h : Bytes)
    (hp : c.flags.p2sh = true) (hh : h.length = 20)
    (hargs : ∀ a ∈ args, a.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hred : redeem.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hn : args.length + 2 ≤ BitcoinScript.MAX_STACK_SIZE)
    (hsz : (BitcoinVerify.pushesBytes (args ++ [redeem])).length ≤ BitcoinVerify.MAX_SCRIPT_SIZE)
    (hnw : BitcoinVerify.isWitnessProgram redeem = none) :
    BitcoinVerify.verifyScript tap c (BitcoinVerify.pushesBytes (args ++ [redeem])) (BitcoinVerify.p2shBytes h) [] = true ↔
      BitcoinSer.hash160 redeem = h ∧
      ∃ st, BitcoinVerify.evalBytes c .base args.reverse redeem = some st ∧ BitcoinVerify.topTrue st = true := by sorry
