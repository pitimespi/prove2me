import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_commit {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (c : ApplyCommitRequest) (cs' : CoordinationState V) (hsent : W.sent (.applyCommit c))
    (h : (W.node n).handleCommit c = .ok cs') : Inv P (W.set n cs') := by sorry
