import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.legacyOracle_eq (f : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : BitcoinScript.Bytes) :
    BitcoinSig.legacyOracle f tx nIn amount v sc =
      BitcoinScriptV2.withCodeSig (BitcoinScriptV2.legacyOracleV2 f tx nIn amount v) v sc := by sorry
