import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.sem_consumes (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle) (m : BitcoinMiniscript.Ms)
    (w out : List BitcoinScript.Bytes) (h : BitcoinMiniscript.Sem f o m w out) :
    ((BitcoinMiniscript.props m).z = true → w = []) ∧ ((BitcoinMiniscript.props m).o = true → w.length = 1) := by sorry
