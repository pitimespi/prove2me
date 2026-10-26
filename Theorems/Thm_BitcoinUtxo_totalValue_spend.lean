import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.totalValue_spend {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (hn : keysNodup u) (h : getCoin u op = some c) :
    totalValue (spendCoin u op) = totalValue u - c.out.value := by sorry
