import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.init_javaInvariant {V : Type} (es : ElectionStrategy) (n : DiscoveryNode) (t : Nat) (s : ClusterState V)
    (h : s.term ≤ t) : (CoordinationState.init n t s).javaInvariant es := by sorry
