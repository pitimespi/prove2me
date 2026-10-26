import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.chain_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) :
    ∀ (blocks : List (List (Tx T))) (u : UtxoSet T) (h : Nat) (u' : UtxoSet T),
      keysNodup u → (∀ b ∈ blocks, (b.map Tx.txid).Nodup) →
      connectChain subsidy u h blocks = some u' →
      totalValue u' ≤ totalValue u + subsidySum subsidy h blocks.length := by sorry
