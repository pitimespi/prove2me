import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.totalValue_spendInputs {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)), keysNodup u → ops.Nodup → (∀ op ∈ ops, haveCoin u op = true) →
      totalValue (spendInputs u ops) = totalValue u - valueIn u ops := by sorry
