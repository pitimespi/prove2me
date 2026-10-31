import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_pivot {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (bt : Nat) (bv : Int) (x y : VotingConfiguration) (hr : Realizes P W bt bv x y) :
    (∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ Committed W s.term s.version ∧
      Descends W s.term s.version bt bv ∧
      (∀ et ev, Committed W et ev → Descends W et ev bt bv → Descends W et ev s.term s.version) ∧
      (x = s.lastAcceptedConfiguration ∨ y = s.lastAcceptedConfiguration)) ∨
    ((∀ et ev, Committed W et ev → ¬ Descends W et ev bt bv) ∧ P.initConfs x) := by sorry
