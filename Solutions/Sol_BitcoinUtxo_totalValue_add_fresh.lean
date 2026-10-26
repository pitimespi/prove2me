import Definitions.Def_BitcoinUtxo

open BitcoinUtxo

private theorem totalValue_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) :
    totalValue ((k, c) :: rest) = c.out.value + totalValue rest := rfl

private theorem spendCoin_of_none {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (h : getCoin u op = none) :
    spendCoin u op = u := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold getCoin at h
    by_cases hk : k = op
    · rw [if_pos hk] at h; simp at h
    · rw [if_neg hk] at h
      unfold spendCoin
      rw [if_neg hk, ih h]

theorem solution {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (h : getCoin u op = none) :
    totalValue (addCoin u op c) = totalValue u + (if c.out.unspendable then 0 else c.out.value) := by
  unfold addCoin
  split
  · omega
  · rw [spendCoin_of_none u op h, totalValue_cons]; omega
