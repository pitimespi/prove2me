import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.close_pair_prob (a b : Int) (Ma Mb Mmin δ : Nat) (hM : 1 ≤ Mmin)
    (hMb : Mmin ≤ Mb ∧ Mb ≤ 2 ^ 63) (hδ : 1 ≤ δ) :
    ((Finset.univ.filter (fun p : Fin (2 ^ 64) × Fin (2 ^ 64) =>
        |(a + randomDelay Ma p.1) - (b + randomDelay Mb p.2)| < δ)).card : ℚ) / (2 ^ 64) ^ 2 ≤
      (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63 := by sorry
