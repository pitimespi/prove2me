import Definitions.Def_OpenSearchProgress
open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

theorem OpenSearchProgress.publication_acks_accepted {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (W' : Cluster V) (hE : PublicationExec P c t Q W W') :
    (∀ q ∈ Q, (W'.node q).currentTerm = t →
      W'.sent (.publishResponse q c ⟨t, s.version⟩) ∨
      ∃ cs' r, (W'.node q).handlePublishRequest ⟨s⟩ = .ok (cs', r)) ∧
    (∀ q ∈ Q, W'.sent (.publishResponse q c ⟨t, s.version⟩) →
      ∃ cs' o, (W'.node c).handlePublishResponse (P.dn q) ⟨t, s.version⟩ = .ok (cs', o) ∧
        q ∈ cs'.publishVotes.nodes) := by sorry
