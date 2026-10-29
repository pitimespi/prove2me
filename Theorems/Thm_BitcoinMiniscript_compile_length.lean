import Definitions.Def_BitcoinMiniscript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.compile_length (m : BitcoinMiniscript.Ms) :
    (BitcoinMiniscript.compile m).length = BitcoinMiniscript.size m := by sorry
