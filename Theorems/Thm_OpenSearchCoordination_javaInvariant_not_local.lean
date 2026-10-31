import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.javaInvariant_not_local :
    ∃ (cs : CoordinationState Unit) (p : PublishRequest Unit) (cs' : CoordinationState Unit) (r : PublishResponse),
      cs.javaInvariant ElectionStrategy.DEFAULT_INSTANCE ∧ cs.handlePublishRequest p = .ok (cs', r) ∧
      ¬ cs'.javaInvariant ElectionStrategy.DEFAULT_INSTANCE := by sorry
