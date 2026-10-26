import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.ledger_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) (blocks : List (List (Tx T))) (h : Nat)
    (u' : UtxoSet T) (hnd : ∀ b ∈ blocks, (b.map Tx.txid).Nodup)
    (hc : connectChain subsidy [] h blocks = some u') :
    totalValue u' ≤ subsidySum subsidy h blocks.length := by sorry
