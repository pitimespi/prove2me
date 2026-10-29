import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.goodVal_of_semW (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (ht : BitcoinMiniscript.HasType m .W) (w : List BitcoinScript.Bytes) (v : BitcoinScript.Bytes)
    (h : BitcoinMiniscript.Sem f o m w [v]) : BitcoinMiniscript.GoodVal v := by sorry
