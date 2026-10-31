import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.all_contested_prob_le (n K δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Int)
    (bound : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Nat)
    (hbound : ∀ k X i, Mmin ≤ bound k X i ∧ bound k X i ≤ 2 ^ 63)
    (hcausal : ∀ k X X', (∀ m : Fin K, m < k → X m = X' m) → offset k X = offset k X' ∧ bound k X = bound k X') :
    ((Finset.univ.filter (fun X : Fin K → Fin n → Fin (2 ^ 64) =>
        ∀ k, ¬ Uncontested (offset k X) (bound k X) δ (X k))).card : ℚ) / (2 ^ 64) ^ (n * K) ≤
      contestedBound n δ Mmin ^ K := by sorry
