import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.multisigSigs_eq (nk ns : BitcoinScript.Bytes) (keys sigs rest : List BitcoinScript.Bytes)
    (nKeys nSigs : Int) (hk : BitcoinScript.toNum false BitcoinScript.nDefaultMaxNumSize nk = some nKeys)
    (hkl : keys.length = nKeys.toNat) (hn : BitcoinScript.toNum false BitcoinScript.nDefaultMaxNumSize ns = some nSigs)
    (hsl : sigs.length = nSigs.toNat) :
    BitcoinScriptV2.multisigSigs (nk :: (keys ++ ns :: (sigs ++ rest))) = sigs := by sorry
