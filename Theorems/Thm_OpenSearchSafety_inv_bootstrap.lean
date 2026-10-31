import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_bootstrap {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (X : VotingConfiguration) (s : ClusterState V) (cs' : CoordinationState V) (hX : P.initConfs X)
    (hcontract : (W.node n).initialStateContract s)
    (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
    (h : (W.node n).setInitialState s = .ok cs') : Inv P (W.set n cs') := by sorry
