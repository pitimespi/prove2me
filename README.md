# prove2me — Bitcoin consensus rules in Lean 4

Formal verification of Bitcoin Core's mainnet consensus rules, pinned at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, developed as missions on [Prove2me](https://prove2.me).
The repository also verifies OpenSearch's cluster-coordination consensus protocol (Zen2); see
[OpenSearch cluster coordination](#opensearch-cluster-coordination-zen2) below.

Lean toolchain: `leanprover/lean4:v4.33.1` (Prove2me environment `0df444a3…`). No Mathlib: every
definition imports only `Std`.

## Layout

- `Definitions/Def_*.lean` — source-linked transcriptions of the consensus functions (one file per mission).
- `Theorems/Thm_*.lean` — theorem statements as published on the platform (`:= by sorry` stubs mirroring the server's modules).
- `Solutions/Sol_<theorem>.lean` — accepted proofs, one per theorem, each a top-level `theorem solution`.
  `Sol_*_all.lean` are the development files from which the per-theorem files are split.
- `missions/` — mission descriptions, prose statements (`items/*.py`), proof explanations as submitted, and the blind
  read-backs attached to the Script proposal (`readbacks/script/`), written by an independent agent from the Lean code alone.
- `tools/pipeline.py` — stubs / split / audit staging / proposal / submission helper used for each mission.
- `tests/Block170Test.lean` — real mainnet data: headers 0–170 and block 170 validated end to end, rejected when tampered, disconnected back.
- `tests/TaprootVectors.lean` — BIP341 wallet test vectors (script trees, tweaks, control blocks, key-path sighashes).
- `tests/SigVectors.lean`, `tests/VerifyVectors.lean` — signature-layer and VerifyScript vectors (BIP340, BIP143, generated ECDSA).
- `tests/SerVectors.lean` — hash test vectors and genesis checks.
- `tests/ScriptVectors.lean` — `#eval` sanity vectors for the Script interpreter (run with `lake env lean tests/ScriptVectors.lean`).
- `tests/*Vectors.lean` (22 files, 1,528 `#eval` lines, every line `true`) with `tests/reference/*.py` — independent Python references written from the Bitcoin Core source, generating edge-case vectors for every reviewed function.
- `REVIEW.md` — the source review guide: method, known limits L1–L10, findings (F1 fixed; R1, R2, D1, D2 verdict-irrelevant), the 23 risk-ranked spots, all reviewed; one report per spot in `REVIEW_SPOT*.md`.
- `STATUS.md` — mission inventory, proposal IDs, and what remains open.
- `missions/submissions/*.json` — the accepted proof submissions of missions 9–13; `missions/umbrella_current.json` — the umbrella proposal with its 161 references and main theorem.

## Build

```
lake build Definitions.Def_BitcoinPow Solutions.Sol_BitcoinPow_nextWork_permitted
```

The `Theorems/` stubs carry `sorry` by design: on the server each resolves to the published,
proved theorem; locally they let the reduction proofs type-check.

## Missions

| Mission | Goal theorem | Theorems |
|---|---|---|
| BIP68 relative lock-time | `BitcoinBIP68.core_correct` | 5 |
| Block subsidy and the 21M bound | `BitcoinSubsidy.issuance_bound` | 8 |
| Proof of work: compact targets and retargeting | `BitcoinPow.nextWork_permitted` | 10 |
| Merkle root and CVE-2012-2459 | `BitcoinMerkle.dup_block` | 9 |
| UTXO accounting and the ledger supply bound | `BitcoinUtxo.ledger_bound` | 10 |
| Headers: median time past and contextual rules | `BitcoinHeader.mtp_mono_chain` | 9 |
| Soft-fork activation: script flags by height | `BitcoinActivation.flags_mono` | 10 |
| Script: CScriptNum, the legacy interpreter, and P2PKH | `BitcoinScript.p2pkh_correct` | 10 |
| Serialization, SHA-256d, weights, genesis block | `BitcoinSer.block_roundtrip` | 17 |
| Signatures: DER, sighash, ECDSA/Schnorr, concrete P2PKH | `BitcoinSig.derEncode_complete` | 14 |
| VerifyScript: P2SH, SegWit v0, witness dispatch | `BitcoinVerify.p2wpkh_correct` | 11 |
| Taproot: key path, script path, Tapscript | `BitcoinTaproot.keypath_correct` | 15 |
| Block validation composed, ApplySpec, DisconnectBlock, the umbrella goal (revision 2) | `BitcoinBlockV2.acceptance` | 19 |

All 71 theorems are proved on the platform. See `STATUS.md` for the open areas.

## OpenSearch cluster coordination (Zen2)

Formal verification of the consensus protocol with which OpenSearch (and Elasticsearch since 7.0) elects its
cluster-manager and commits cluster-state updates, pinned at OpenSearch revision
`b2a54ba5c0defba3d1d20423e911d4bf920bab19` (`server/src/main/java/org/opensearch/cluster/coordination/`). The
per-node state machine `CoordinationState.java` and the pre-voting and election-scheduling code are transcribed
check by check; the cluster is a message soup (loss, duplication, reordering) with crash-recovery, covering every
handler call the `Coordinator` makes. Elastic's TLA+ model `ZenWithTerms` of this algorithm was only model-checked;
here safety is proved for every execution of the cluster model with the Java semantics, for compatible bootstrap
configurations and the default election strategy (the Java semantics differ from the TLA+ model: one of its invariants
fails for them — see `NOTES_OpenSearchSafety.md`), and liveness under stability; for the randomized election timers,
the probability of contested rounds is bounded.

| Mission | Files | Goal theorem | Theorems |
|---|---|---|---|
| The per-node state machine (`CoordinationState`) | `Def_OpenSearchCoordination`, `NOTES_OpenSearchCoordination.md` | `OpenSearchCoordination.javaInvariant_preserved` | 18 |
| Pre-voting and election scheduling | `Def_OpenSearchPreVote` | `OpenSearchPreVote.preVote_then_election` | 10 |
| Cluster safety (compatible bootstrap configurations, default election strategy): one cluster-manager per term, one state per (term, version), committed states never fork, election safety, `invariant()` never fails at cluster-manager-eligible nodes | `Def_OpenSearchSafety`, `NOTES_OpenSearchSafety.md` | `OpenSearchSafety.committed_linear` | 44 |
| Liveness under a stable period: elections are won and publications committed in any delivery order | `Def_OpenSearchProgress`, `NOTES_OpenSearchProgress.md` | `OpenSearchProgress.election_possible` | 6 |
| Randomized election timers: bounds on the probability that rounds of competing timers are contested (about `C(n,2)(2δ−1)/Mmin` per round, its `K`-th power over `K` adaptively scheduled rounds) (Mathlib) | `mathlib/Definitions/Def_OpenSearchElectionTimer`, `mathlib/NOTES_OpenSearchElectionTimer.md` | `OpenSearchElectionTimer.all_contested_prob_le` | 7 |

All 85 theorems are proved on the platform and locally (axioms `propext`, `Classical.choice`, `Quot.sound` only; the safety and progress
missions were also checked end to end in a single module without theorem stubs). The transcriptions replay
OpenSearch's own unit tests: `tests/OpenSearchCoordinationVectors.lean` (41 tests of `CoordinationStateTests` and
`CoordinationMetadataTests`, 179 checks) and `tests/OpenSearchPreVoteVectors.lean` (all 17 tests of
`PreVoteCollectorTests` and `ElectionSchedulerFactoryTests`, 39 checks). The safety invariant was designed twice
independently and validated with explicit-state model checkers before the proof (no counterexample to induction).

```
lake build Definitions.Def_OpenSearchSafety Solutions.Sol_OpenSearchSafety_committed_linear
lake env lean tests/OpenSearchCoordinationVectors.lean
cd mathlib && cp ../Definitions/Def_OpenSearchCoordination.lean ../Definitions/Def_OpenSearchPreVote.lean Definitions/ \
  && lake env lean Solutions/Sol_OpenSearchElectionTimer_all.lean
```

