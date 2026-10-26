import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.tx_conservation {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hn : keysNodup u) (hnd : tx.vin.Nodup) (hcb : tx.isCoinbase = false)
    (hfee : checkTxInputs u tx h = some fee)
    (hfresh : ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none)
    (hpos : ∀ o ∈ tx.vout, 0 ≤ o.value) :
    totalValue (updateCoins u tx h) ≤ totalValue u - fee := by sorry
