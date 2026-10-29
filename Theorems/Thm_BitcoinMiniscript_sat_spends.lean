import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sat_spends (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .B) (w : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.Sat f o m w)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    ∃ res, BitcoinScript.evalScript f o w (BitcoinMiniscript.compile m) = some res ∧ res.length = 1 ∧
      (match res with | top :: _ => BitcoinScript.castToBool top | [] => false) = true := by sorry
