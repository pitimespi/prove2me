import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleJoin_stays_won {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (hinv : cs.electionWon = cs.isElectionQuorum es cs.joinVotes)
    (h : cs.handleJoin es j = .ok (cs', b)) (hw : cs.electionWon = true) : cs'.electionWon = true := by sorry
