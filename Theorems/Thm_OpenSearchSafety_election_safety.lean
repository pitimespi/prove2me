import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.election_safety {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (ha : (W.node a).electionWon = true) (hb : (W.node b).electionWon = true)
    (ht : (W.node a).currentTerm = (W.node b).currentTerm) : a = b := by sorry
