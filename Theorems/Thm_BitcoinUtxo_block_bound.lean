import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.block_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) (u : UtxoSet T) (h : Nat) (block : List (Tx T))
    (u' : UtxoSet T) (fees : Int) (hn : keysNodup u) (hnd : (block.map Tx.txid).Nodup)
    (hc : connectBlock subsidy u h block = some (u', fees)) :
    totalValue u' ≤ totalValue u + subsidy h ∧ keysNodup u' := by sorry
