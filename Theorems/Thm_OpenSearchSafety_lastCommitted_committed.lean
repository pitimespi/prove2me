import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.lastCommitted_committed {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (n : NodeId) (hn : P.eligible n = true) :
    (W.node n).lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∨
    P.initConfs (W.node n).lastCommittedConfiguration ∨
    ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ Committed W s.term s.version ∧
      s.lastAcceptedConfiguration = (W.node n).lastCommittedConfiguration := by sorry
