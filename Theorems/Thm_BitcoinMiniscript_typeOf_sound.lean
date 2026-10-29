import Definitions.Def_BitcoinMiniscript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.typeOf_sound (m : BitcoinMiniscript.Ms) (ty : BitcoinMiniscript.Ty)
    (h : BitcoinMiniscript.typeOf m = some ty) : BitcoinMiniscript.HasType m ty := by sorry
