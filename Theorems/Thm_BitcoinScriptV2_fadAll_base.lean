import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.fadAll_base (sc : BitcoinScript.Bytes) (sigs : List BitcoinScript.Bytes) :
    BitcoinScriptV2.fadAll .base sc sigs =
      sigs.foldl (fun sc sig => (BitcoinSig.findAndDelete sc (BitcoinSig.pushBytes sig)).1) sc := by sorry
