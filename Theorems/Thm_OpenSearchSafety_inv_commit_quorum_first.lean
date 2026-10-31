import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_commit_quorum_first {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (ct : Nat) (cv : Int) (hc : Committed W ct cv)
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv ct cv → ft = ct ∧ fv = cv) :
    ∃ X A, P.initConfs X ∧ RespVoters P W ct cv A ∧ X.hasQuorum A = true := by sorry
