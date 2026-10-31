import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_commit_quorum_after {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD : NodeId) (sD : ClusterState V) (ptD : Nat) (pvD : Int) (hD : W.sent (.publishRequest srcD sD ptD pvD))
    (ct : Nat) (cv : Int) (hc : Committed W ct cv) (h : Descends W sD.term sD.version ct cv)
    (hne : ¬ (sD.term = ct ∧ sD.version = cv))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv ct cv →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = ct ∧ fv = cv)) :
    ∃ A, RespVoters P W ct cv A ∧ sD.lastAcceptedConfiguration.hasQuorum A = true := by sorry
