import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.contested_prob_le (n δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      contestedBound n δ Mmin := by sorry
