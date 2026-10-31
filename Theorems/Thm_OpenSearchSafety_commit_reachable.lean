import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.commit_reachable : ∃ (P : Params) (W : Cluster Unit), P.InitCompatible ∧
    P.strategy = ElectionStrategy.DEFAULT_INSTANCE ∧ Reachable P W ∧ Committed W 1 1 := by sorry
