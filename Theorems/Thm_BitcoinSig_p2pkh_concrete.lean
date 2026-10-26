import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinSig BitcoinSer

theorem BitcoinSig.p2pkh_concrete (f : SigFlags) (fl : BitcoinScript.Flags) (tx : Tx) (nIn : Nat) (amount : Int)
    (v : SigVersion) (sig pk h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain fl (BitcoinSig.legacyOracle f tx nIn amount v (BitcoinSig.p2pkhBytes h))
        [.push sig, .push pk] (BitcoinScript.p2pkhScript h) = true ↔
      BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript f tx nIn amount v (BitcoinSig.p2pkhBytes h) sig pk = some true := by sorry
