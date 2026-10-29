import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.opsIn_compile_le (m : BitcoinMiniscript.Ms) :
    BitcoinScript.opsIn (BitcoinMiniscript.compile m) ≤ BitcoinMiniscript.opsMax m := by sorry
