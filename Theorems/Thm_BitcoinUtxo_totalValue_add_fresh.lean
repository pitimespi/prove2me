import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.totalValue_add_fresh {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (h : getCoin u op = none) :
    totalValue (addCoin u op c) = totalValue u + (if c.out.unspendable then 0 else c.out.value) := by sorry
