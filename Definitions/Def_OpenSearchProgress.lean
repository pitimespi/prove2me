import Definitions.Def_OpenSearchSafety

/-!
# OpenSearch cluster coordination: progress under stability

Safety holds in every execution. Progress cannot: in an asynchronous network a message may never be delivered, and
competing candidates can keep raising terms (this is what pre-voting and the randomized election scheduler mitigate).
The theorems of this mission state progress for the executions of a *stable period*: a window in which one node runs
for election (or publishes) and none of the steps that the relations below exclude occurs, while every other step of
the cluster remains possible — deliveries in any order, duplicates, other nodes' joins, acceptances and commits,
restarts of other nodes. Under their hypotheses, they show that in every such execution the candidate, once in the
election term, accepts and counts every voter's join for that term, and every acknowledging node in the
cluster-manager's term has acknowledged its publication or accepts it, while the cluster-manager accepts and counts
every acknowledgement of it sent by an acknowledging node; that once all of a quorum's votes (acknowledgements) are
counted, the election is won (the publication committed); and that such executions exist. No theorem states that the
start-joins an election or a publication needs stay enabled.
-/

namespace OpenSearchProgress

open OpenSearchCoordination OpenSearchSafety

variable {V : Type}

/-- A step of a stable election period for candidate `c` in term `t` with voters `Q`, `(kt, kv)` being the term and
version of `c`'s accepted state when the period starts: any step of the cluster except a start-join in a term at least
`t` other than `c`'s own request for `t`, any new publication, a bootstrap of `c` or of a voter, a restart of `c` or of
a voter that is cluster-manager-eligible (`restartAny`, the restart of a node that is not eligible, is not restricted),
and the acceptance by `c` or a voter of a publication fresher than `(kt, kv)` (a stale publication of a former
cluster-manager arriving during the election). -/
inductive ElectionStep (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) (kt : Nat) (kv : Int) :
    Cluster V → Cluster V → Prop where
  | bootstrap (W : Cluster V) (n : NodeId) (X : VotingConfiguration) (s : ClusterState V)
      (cs' : CoordinationState V) (hX : P.initConfs X) (hnq : n ≠ c ∧ n ∉ Q)
      (hcontract : (W.node n).initialStateContract s)
      (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
      (h : (W.node n).setInitialState s = .ok cs') :
      ElectionStep P c t Q kt kv W (W.set n cs')
  | startJoin (W : Cluster V) (n src : NodeId) (t' : Nat) (cs' : CoordinationState V) (j : Join)
      (hsrc : P.eligible src = true) (hstable : t' < t ∨ (src = c ∧ t' = t))
      (h : (W.node n).handleStartJoin ⟨P.dn src, t'⟩ = .ok (cs', j)) :
      ElectionStep P c t Q kt kv W ((W.set n cs').send (.join j))
  | join (W : Cluster V) (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool)
      (hsent : W.sent (.join j)) (hdest : j.targetNode.id = n)
      (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
      ElectionStep P c t Q kt kv W (W.set n cs')
  | publish (W : Cluster V) (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
      (cs' : CoordinationState V) (r : PublishResponse) (hsent : W.sent (.publishRequest src s pt pv))
      (hfresh : n = c ∨ n ∈ Q → s.term < kt ∨ (s.term = kt ∧ s.version ≤ kv))
      (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
      ElectionStep P c t Q kt kv W ((W.set n cs').send (.publishResponse n src r))
  | respond (W : Cluster V) (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V)
      (o : Option ApplyCommitRequest) (hsent : W.sent (.publishResponse src n r))
      (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
      ElectionStep P c t Q kt kv W (match o with
        | none => W.set n cs'
        | some a => (W.set n cs').send (.applyCommit a))
  | commit (W : Cluster V) (n : NodeId) (a : ApplyCommitRequest) (cs' : CoordinationState V)
      (hsent : W.sent (.applyCommit a)) (h : (W.node n).handleCommit a = .ok cs') :
      ElectionStep P c t Q kt kv W (W.set n cs')
  | restart (W : Cluster V) (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true)
      (hnq : n ≠ c ∧ n ∉ Q) (hs : RestartState (W.node n).lastAcceptedState s') :
      ElectionStep P c t Q kt kv W (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'))
  | restartAny (W : Cluster V) (n : NodeId) (t' : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
      ElectionStep P c t Q kt kv W (W.set n (CoordinationState.init (W.node n).localNode t' s'))

end OpenSearchProgress

namespace OpenSearchProgress

open OpenSearchCoordination OpenSearchSafety

variable {V : Type}

/-- The executions of a stable election period: finite sequences of `ElectionStep`s. -/
inductive ElectionExec (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) (kt : Nat) (kv : Int) :
    Cluster V → Cluster V → Prop where
  | refl (W : Cluster V) : ElectionExec P c t Q kt kv W W
  | step (W W' W'' : Cluster V) : ElectionExec P c t Q kt kv W W' → ElectionStep P c t Q kt kv W' W'' →
      ElectionExec P c t Q kt kv W W''

/-- A step of a stable publication period for the cluster-manager `c` of term `t` with acknowledging nodes `Q`: any step
of the cluster except a start-join in a term above `t` at `c` or at a node of `Q`, a further publication by `c`, and a
restart of `c` if it is cluster-manager-eligible (`restartAny`, the restart of a node that is not eligible, is not
restricted). -/
inductive PublicationStep (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) : Cluster V → Cluster V → Prop where
  | bootstrap (W : Cluster V) (n : NodeId) (X : VotingConfiguration) (s : ClusterState V)
      (cs' : CoordinationState V) (hX : P.initConfs X)
      (hcontract : (W.node n).initialStateContract s)
      (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
      (h : (W.node n).setInitialState s = .ok cs') :
      PublicationStep P c t Q W (W.set n cs')
  | startJoin (W : Cluster V) (n src : NodeId) (t' : Nat) (cs' : CoordinationState V) (j : Join)
      (hsrc : P.eligible src = true) (hstable : (n = c ∨ n ∈ Q) → t' ≤ t)
      (h : (W.node n).handleStartJoin ⟨P.dn src, t'⟩ = .ok (cs', j)) :
      PublicationStep P c t Q W ((W.set n cs').send (.join j))
  | join (W : Cluster V) (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool)
      (hsent : W.sent (.join j)) (hdest : j.targetNode.id = n)
      (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
      PublicationStep P c t Q W (W.set n cs')
  | clientValue (W : Cluster V) (n : NodeId) (s : ClusterState V) (cs' : CoordinationState V)
      (p : PublishRequest V) (hn : n ≠ c) (hcontract : (W.node n).clientValueContract s)
      (h : (W.node n).handleClientValue s = .ok (cs', p)) :
      PublicationStep P c t Q W ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm
        (W.node n).lastAcceptedVersion))
  | publish (W : Cluster V) (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
      (cs' : CoordinationState V) (r : PublishResponse) (hsent : W.sent (.publishRequest src s pt pv))
      (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
      PublicationStep P c t Q W ((W.set n cs').send (.publishResponse n src r))
  | respond (W : Cluster V) (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V)
      (o : Option ApplyCommitRequest) (hsent : W.sent (.publishResponse src n r))
      (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
      PublicationStep P c t Q W (match o with
        | none => W.set n cs'
        | some a => (W.set n cs').send (.applyCommit a))
  | commit (W : Cluster V) (n : NodeId) (a : ApplyCommitRequest) (cs' : CoordinationState V)
      (hsent : W.sent (.applyCommit a)) (h : (W.node n).handleCommit a = .ok cs') :
      PublicationStep P c t Q W (W.set n cs')
  | restart (W : Cluster V) (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true) (hnc : n ≠ c)
      (hs : RestartState (W.node n).lastAcceptedState s') :
      PublicationStep P c t Q W (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'))
  | restartAny (W : Cluster V) (n : NodeId) (t' : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
      PublicationStep P c t Q W (W.set n (CoordinationState.init (W.node n).localNode t' s'))

/-- The executions of a stable publication period. -/
inductive PublicationExec (P : Params) (c : NodeId) (t : Nat) (Q : List NodeId) : Cluster V → Cluster V → Prop where
  | refl (W : Cluster V) : PublicationExec P c t Q W W
  | step (W W' W'' : Cluster V) : PublicationExec P c t Q W W' → PublicationStep P c t Q W' W'' →
      PublicationExec P c t Q W W''

end OpenSearchProgress
