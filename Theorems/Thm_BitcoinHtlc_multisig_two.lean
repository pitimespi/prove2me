import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.multisig_two (o : Oracle) (s1 s2 k1 k2 : Bytes) :
    BitcoinScript.multisigLoop o [s1, s2] [k1, k2] = some true ↔
      o.checkSig s1 k1 = some true ∧ o.checkSig s2 k2 = some true := by sorry
