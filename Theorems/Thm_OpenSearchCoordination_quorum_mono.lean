import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.quorum_mono (c : VotingConfiguration) (a b : List NodeId) (hab : ∀ x, x ∈ a → x ∈ b)
    (ha : c.hasQuorum a = true) : c.hasQuorum b = true := by sorry
