import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_eligible_of_won {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W) (n : NodeId)
    (h : (W.node n).electionWon = true) : P.eligible n = true := by sorry
