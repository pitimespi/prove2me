import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.nonNegative_two_to_one (v : Nat) (hv : v < 2 ^ 63) (n : Int)
    (hn : -2 ^ 63 ≤ n ∧ n < 2 ^ 63) :
    nonNegative n = v ↔ n = v ∨ n = (if v = 0 then -2 ^ 63 else -(v : Int)) := by sorry
