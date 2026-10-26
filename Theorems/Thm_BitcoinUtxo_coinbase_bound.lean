import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.coinbase_bound {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat)
    (hcb : tx.isCoinbase = true)
    (hfresh : ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none)
    (hpos : ∀ o ∈ tx.vout, 0 ≤ o.value) :
    totalValue (updateCoins u tx h) ≤ totalValue u + valueOut tx := by sorry
