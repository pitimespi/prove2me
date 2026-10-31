import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_won_of_electionWon {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (h : (W.node n).electionWon = true) : Won P W n (W.node n).currentTerm := by sorry
