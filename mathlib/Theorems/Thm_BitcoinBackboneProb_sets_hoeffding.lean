import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.sets_hoeffding (n t : ℕ) (p : unitInterval) (S T : Finset ℕ)
    (hTS : T ⊆ S) (j : ℕ)
    (hε : 0 ≤ (j : ℝ) + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p)) :
    (P n t p).real {ω | ∑ i ∈ T, Y ω i + j ≤ ∑ i ∈ S, Z ω i} ≤
      Real.exp (-2 * ((j : ℝ) + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p)) ^ 2
        / (S.card * ((t : ℝ) + 1) ^ 2)) := by sorry
