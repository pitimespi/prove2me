import Definitions.Def_BitcoinScriptV2

open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

set_option linter.unusedSimpArgs false

theorem solution (f : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : BitcoinScript.Bytes) :
    BitcoinSig.legacyOracle f tx nIn amount v sc =
      BitcoinScriptV2.withCodeSig (BitcoinScriptV2.legacyOracleV2 f tx nIn amount v) v sc := by
  rfl
