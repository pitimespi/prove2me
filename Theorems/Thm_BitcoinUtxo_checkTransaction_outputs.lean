import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.checkTransaction_outputs {T : Type} [DecidableEq T] (tx : Tx T) (h : checkTransaction tx = true) :
    tx.vin.Nodup ∧ ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ MAX_MONEY := by sorry
