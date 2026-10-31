import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.handlePreVoteRequest_spec (healthy : Bool) (st : CollectorState) (req : PreVoteRequest)
    (resp : PreVoteResponse) :
    handlePreVoteRequest healthy st req = .ok resp ↔
      healthy = true ∧ (st.leader = none ∨ st.leader = some req.sourceNode) ∧ resp = st.response := by sorry
