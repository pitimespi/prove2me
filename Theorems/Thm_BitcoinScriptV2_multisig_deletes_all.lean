import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.multisig_deletes_all (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (c : BitcoinScript.Byte)
    (hc : c = BitcoinScript.OP_CHECKMULTISIG ∨ c = BitcoinScript.OP_CHECKMULTISIGVERIFY) (sig pk : BitcoinScript.Bytes) :
    (BitcoinScriptV2.oracleAt v o s (.op c)).checkSig sig pk =
      o.checkSig (BitcoinScriptV2.fadAll v s.scriptCode (BitcoinScriptV2.multisigSigs s.st.stack)) sig pk := by sorry
