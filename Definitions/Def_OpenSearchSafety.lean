import Definitions.Def_OpenSearchCoordination

/-!
# OpenSearch cluster coordination: the cluster

Every node runs the `CoordinationState` of `Def_OpenSearchCoordination` (OpenSearch
`b2a54ba5c0defba3d1d20423e911d4bf920bab19`). Nodes exchange messages through a network that may lose, duplicate, delay
and reorder them: a message, once sent, stays available forever and may be handled any number of times, by any node it
is addressed to, or never. Nodes may crash and restart at any time.

Each step is a successful call of one `CoordinationState` method, its output, if any, being sent. The steps cover every
call the `Coordinator` makes (`Coordinator.java`, cited `CO:<line>`; the `Coordinator`'s own guards only reject more):
* `bootstrap`: `setInitialState` with a bootstrap configuration (`ClusterBootstrapService`, CO:1101-1161), under the
  method's asserted preconditions; nodes may bootstrap with different configurations (see `BootstrapConfig`);
* `startJoin`: `handleStartJoin` for a request from any cluster-manager-eligible node in any term (elections, abdication,
  and `ensureTermAtLeast` on receiving a message of a higher term, which joins that message's sender); the `Join` is
  sent to the requester;
* `join`: `handleJoin` of a sent `Join` addressed to the node;
* `clientValue`: `handleClientValue` of any cluster state satisfying the asserted precondition; the `PublishRequest` is
  sent to every node;
* `publish`: `handlePublishRequest` of a sent `PublishRequest`; the `PublishResponse` goes back to the publisher;
* `respond`: `handlePublishResponse` of a sent `PublishResponse` addressed to the node; a resulting `ApplyCommitRequest`
  is sent to every node;
* `commit`: `handleCommit` of a sent `ApplyCommitRequest`;
* `restart`: a new `CoordinationState` over the persisted state. A cluster-manager-eligible node persists its current
  term and accepted state synchronously (`GatewayMetaState.LucenePersistedState`) and rebuilds on startup the parts of
  the accepted state that are not persisted (the node list, routing table, transient settings — the payload and the
  cluster-manager node here; GatewayMetaState.java:164-197); a node that never joined a cluster may instead restore a
  term-0 state with empty configurations from the remote store (GatewayMetaState.java:166-185). A node that is not
  cluster-manager-eligible persists asynchronously or not at all, and may come back with any persisted state.

A `PublishRequest` records, as ghost data that the real message does not carry, the term and version of the state its
publisher had accepted when it published (its parent); this defines descent between published states.

OpenSearch's randomized safety test `CoordinationStateTestCluster` (`test/framework/.../coordination/`) checks the
first two safety properties on random executions of a similar model: messages are never removed, start-join requests
carry arbitrary terms, any elected node publishes arbitrary values and configurations, and nodes reboot.

Assumptions (outside the model): the cluster-manager role of a node never changes (changing it and back can reset the
persisted term, GatewayMetaState.java:232-255); no disk rollback; no offline tools (`opensearch-node` unsafe-bootstrap,
detach-cluster, remove-settings, remove-customs); bootstrap requirements name the same node at every node; one election
strategy for all nodes; a publication delivered through the remote store reconstructs exactly the published state.
-/

namespace OpenSearchSafety

open OpenSearchCoordination

/-- Messages. -/
inductive Message (V : Type) where
  | join (j : Join)
  /-- A `PublishRequest` from `source`, with the ghost parent (term, version). -/
  | publishRequest (source : NodeId) (state : ClusterState V) (parentTerm : Nat) (parentVersion : Int)
  /-- A `PublishResponse` from `source` to `dest`. -/
  | publishResponse (source dest : NodeId) (resp : PublishResponse)
  | applyCommit (c : ApplyCommitRequest)

/-- The fixed parameters of a cluster. -/
structure Params where
  /-- `DiscoveryNode.isClusterManagerNode()` of each node. -/
  eligible : NodeId → Bool
  /-- The configurations a node may bootstrap with. -/
  initConfs : VotingConfiguration → Prop
  /-- The election strategy of every node. -/
  strategy : ElectionStrategy

/-- The `DiscoveryNode` of node `n`. -/
def Params.dn (P : Params) (n : NodeId) : DiscoveryNode := ⟨n, P.eligible n⟩

/-- The bootstrap configurations are compatible: votes of cluster-manager-eligible nodes that form a quorum of one
bootstrap configuration share a voter with votes that form a quorum of another. -/
def Params.InitCompatible (P : Params) : Prop :=
  ∀ X Y, P.initConfs X → P.initConfs Y → ∀ q₁ q₂ : List NodeId,
    (∀ x ∈ q₁, P.eligible x = true) → (∀ x ∈ q₂, P.eligible x = true) →
    X.hasQuorum q₁ = true → Y.hasQuorum q₂ = true → ∃ x, x ∈ q₁ ∧ x ∈ q₂

/-- The configuration `ClusterBootstrapService` bootstraps with (CBS:176-215, CBS:259-273, CBS:306-335): the bootstrap
requirements (`cluster.initial_cluster_manager_nodes`, without duplicates) are numbered `0 … k-1`; requirement `i`, when
the node has discovered the node it names, contributes that node's id `resolve i`, and otherwise a placeholder id
`placeholder i` (`"{bootstrap-placeholder}-" + requirement`); more than half of the requirements must be matched. -/
def BootstrapConfig (k : Nat) (resolve placeholder : Nat → NodeId) (matched : Nat → Bool)
    (X : VotingConfiguration) : Prop :=
  (∀ x, x ∈ X.nodeIds ↔ ∃ i, i < k ∧ x = if matched i then resolve i else placeholder i) ∧
  ((List.range k).filter matched).length * 2 > k

/-- A cluster: the coordination state of every node and the set of messages sent so far. -/
structure Cluster (V : Type) where
  node : NodeId → CoordinationState V
  sent : Message V → Prop

namespace Cluster

variable {V : Type}

/-- Replace node `n`'s state. -/
def set (W : Cluster V) (n : NodeId) (cs : CoordinationState V) : Cluster V :=
  { W with node := fun m => if m = n then cs else W.node m }

/-- Send a message. -/
def send (W : Cluster V) (m : Message V) : Cluster V := { W with sent := fun x => W.sent x ∨ x = m }

end Cluster

variable {V : Type}

/-- A fresh cluster: every node is in term 0 with an accepted term-0 state with empty configurations (its version,
metadata version and payload are arbitrary — a fresh node has version 0, a node restored from the remote store or
upgraded from an older version may have others), and no message has been sent. -/
def Initial (P : Params) (W : Cluster V) : Prop :=
  (∀ n, ∃ s : ClusterState V, s.term = 0 ∧ s.lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
      s.lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
      W.node n = CoordinationState.init (P.dn n) 0 s) ∧
  (∀ m, ¬ W.sent m)

/-- The accepted state a restarting cluster-manager-eligible node comes back with, given the one it had: the persisted
term, version, configurations and cluster-UUID flags, with the rest rebuilt; or, if it never joined a cluster (term 0,
empty configurations, unknown cluster UUID), a term-0 state with empty configurations restored from the remote store. -/
def RestartState (s s' : ClusterState V) : Prop :=
  (s'.term = s.term ∧ s'.version = s.version ∧
    s'.lastCommittedConfiguration = s.lastCommittedConfiguration ∧
    s'.lastAcceptedConfiguration = s.lastAcceptedConfiguration ∧
    s'.clusterUUIDKnown = s.clusterUUIDKnown ∧ s'.clusterUUIDCommitted = s.clusterUUIDCommitted) ∨
  (s.term = 0 ∧ s.lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
    s.lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧ s.clusterUUIDKnown = false ∧
    s'.term = 0 ∧ s'.lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
    s'.lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG)

/-- One step of the cluster. -/
inductive Step (P : Params) : Cluster V → Cluster V → Prop where
  | bootstrap (W : Cluster V) (n : NodeId) (X : VotingConfiguration) (s : ClusterState V)
      (cs' : CoordinationState V) (hX : P.initConfs X)
      (hcontract : (W.node n).initialStateContract s)
      (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
      (h : (W.node n).setInitialState s = .ok cs') :
      Step P W (W.set n cs')
  | startJoin (W : Cluster V) (n src : NodeId) (t : Nat) (cs' : CoordinationState V) (j : Join)
      (hsrc : P.eligible src = true)
      (h : (W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)) :
      Step P W ((W.set n cs').send (.join j))
  | join (W : Cluster V) (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool)
      (hsent : W.sent (.join j)) (hdest : j.targetNode.id = n)
      (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
      Step P W (W.set n cs')
  | clientValue (W : Cluster V) (n : NodeId) (s : ClusterState V) (cs' : CoordinationState V)
      (p : PublishRequest V) (hcontract : (W.node n).clientValueContract s)
      (h : (W.node n).handleClientValue s = .ok (cs', p)) :
      Step P W ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm
        (W.node n).lastAcceptedVersion))
  | publish (W : Cluster V) (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
      (cs' : CoordinationState V) (r : PublishResponse) (hsent : W.sent (.publishRequest src s pt pv))
      (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
      Step P W ((W.set n cs').send (.publishResponse n src r))
  | respond (W : Cluster V) (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V)
      (o : Option ApplyCommitRequest) (hsent : W.sent (.publishResponse src n r))
      (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
      Step P W (match o with
        | none => W.set n cs'
        | some c => (W.set n cs').send (.applyCommit c))
  | commit (W : Cluster V) (n : NodeId) (c : ApplyCommitRequest) (cs' : CoordinationState V)
      (hsent : W.sent (.applyCommit c)) (h : (W.node n).handleCommit c = .ok cs') :
      Step P W (W.set n cs')
  | restart (W : Cluster V) (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true)
      (hs : RestartState (W.node n).lastAcceptedState s') :
      Step P W (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'))
  | restartAny (W : Cluster V) (n : NodeId) (t : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
      Step P W (W.set n (CoordinationState.init (W.node n).localNode t s'))

/-- The clusters reachable from a fresh cluster. -/
inductive Reachable (P : Params) : Cluster V → Prop where
  | init (W : Cluster V) : Initial P W → Reachable P W
  | step (W W' : Cluster V) : Reachable P W → Step P W W' → Reachable P W'

/-- A published state (term, version) is committed when an `ApplyCommitRequest` for it has been sent. -/
def Committed (W : Cluster V) (t : Nat) (v : Int) : Prop := ∃ src, W.sent (.applyCommit ⟨src, t, v⟩)

/-- `(t, v)` is the parent of `(t', v')`: a publication of `(t', v')` was made on top of an accepted `(t, v)`. -/
def Parent (W : Cluster V) (t : Nat) (v : Int) (t' : Nat) (v' : Int) : Prop :=
  ∃ src s, W.sent (.publishRequest src s t v) ∧ s.term = t' ∧ s.version = v'

/-- Descent between published (term, version) pairs: the reflexive-transitive closure of `Parent`. -/
inductive Descends (W : Cluster V) : Nat → Int → Nat → Int → Prop where
  | refl (t : Nat) (v : Int) : Descends W t v t v
  | step (t : Nat) (v : Int) (t' : Nat) (v' : Int) (t'' : Nat) (v'' : Int) :
      Descends W t v t' v' → Parent W t' v' t'' v'' → Descends W t v t'' v''

end OpenSearchSafety
