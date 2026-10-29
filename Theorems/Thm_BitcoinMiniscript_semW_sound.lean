import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.semW_sound (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .W) (w rest : List BitcoinScript.Bytes) (x v : BitcoinScript.Bytes)
    (hs : BitcoinMiniscript.Sem f o m w [v])
    (hops : BitcoinMiniscript.opsMax m ≤ BitcoinScript.MAX_OPS_PER_SCRIPT)
    (hsz : w.length + 1 + rest.length + BitcoinMiniscript.size m ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (x :: (w ++ rest)) (BitcoinMiniscript.compile m) = some (v :: x :: rest) ∨
    BitcoinScript.evalScript f o (x :: (w ++ rest)) (BitcoinMiniscript.compile m) = some (x :: v :: rest) := by sorry
