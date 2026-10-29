import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sem_sound (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ty : BitcoinMiniscript.Ty) (ht : BitcoinMiniscript.HasType m ty) (hne : ty ≠ .W)
    (w out rest : List BitcoinScript.Bytes) (hs : BitcoinMiniscript.Sem f o m w out)
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (w ++ rest) (BitcoinMiniscript.compile m) = some (out ++ rest) := by sorry
