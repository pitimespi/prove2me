# Bitcoin consensus formalization — status report

Lean 4 (v4.33.1, platform env `0df444a3…`), Bitcoin Core pinned at `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, mainnet parameters. Every definition is transcribed from the pinned source files; every theorem below compiles locally with a complete proof (axioms: `propext`, `Classical.choice`, `Quot.sound` only — no `sorry`, no `native_decide`, no `bv_decide`).

## Missions on Prove2me

| # | Mission | Proposal | Status | Goal theorem | Theorems | Proofs ready |
|---|---|---|---|---|---|---|
| 1 | BIP68 relative lock-time | `a476b1aa-dd01-4f70-91ca-2c3edaff612c` | In review (moderator); **all 5 theorems Proved** | `BitcoinBIP68.core_correct` | 5 | done |
| 2 | Block subsidy & 21M bound | `5e03e959-8b28-4706-95f4-e811c66b8e38` | In review; **all 8 Proved** | `BitcoinSubsidy.issuance_bound` | 8 | 8 |
| 3 | Proof of work: compact targets & retargeting | `7e8995f8-594f-4915-bd3a-49fb265e8056` | In review; **all 10 Proved** | `BitcoinPow.nextWork_permitted` | 10 | 10 |
| 4 | Merkle root & CVE-2012-2459 check | `9dd5c171-f875-416d-9f64-bacf33388a37` | In review; **all 9 Proved** | `BitcoinMerkle.dup_block` | 9 | 9 |
| 5 | UTXO accounting & ledger supply bound | `3560d0b7-ca90-488f-9eaa-ff085f0e2df6` | In review; **all 10 Proved** | `BitcoinUtxo.ledger_bound` | 10 | 10 |
| 6 | Headers: median time past & contextual rules | `e5a5d9c9-b4d4-4650-a737-49b5c02b02e2` | In review; **all 9 Proved** | `BitcoinHeader.mtp_mono_chain` | 9 | 9 |
| 7 | Soft-fork activation: script flags by height | `fd6291a7-3b83-4220-b1db-68759db667a9` | In review; **all 10 Proved** | `BitcoinActivation.flags_mono` | 10 | 10 |
| 8 | Script: CScriptNum, legacy `EvalScript`/`VerifyScript`, P2PKH | `fe54cb6b-06b5-45d0-9378-94ad594447f9` | In review; **all 10 Proved** | `BitcoinScript.p2pkh_correct` | 10 | 10 |
| 9 | Serialization, CompactSize, SHA-256d/Hash160, weights, genesis block | `de803721-663b-4dc5-9b2c-57573424cb33` | Published; **all 17 Proved** (submitted and accepted) | `BitcoinSer.block_roundtrip` | 17 | 17 |
| 10 | Signatures: strict DER, sighash (legacy/BIP143), secp256k1 ECDSA/Schnorr, concrete P2PKH | `64726a79-22e3-4530-9da0-f77dd4f58fc9` | Published; **all 14 Proved** (submitted and accepted) | `BitcoinSig.derEncode_complete` | 14 | 14 |
| 11 | VerifyScript dispatch: P2SH, native/wrapped SegWit v0, unknown versions | `b7297a23-212b-4d31-95ce-c235e82f9037` | Published; **all 11 Proved** (submitted and accepted) | `BitcoinVerify.p2wpkh_correct` | 11 | 11 |
| 12 | Taproot: key path, script-path commitment, BIP341 sighash, Tapscript rules | `a2e08bc2-73c6-4c97-9d55-9ee2df86fec5` | Published; **all 15 Proved** (submitted and accepted) | `BitcoinTaproot.keypath_correct` | 15 | 15 |
| 13 | Block validation composed: header path, CheckBlock, ContextualCheckBlock, ConnectBlock, DisconnectBlock, the umbrella goal | `e0d2bee0-9471-4c84-91de-f76e81852e33` | Published; **all 19 Proved** (submitted and accepted) | `BitcoinBlock.acceptance` | 19 | 19 |
| 13r | Block validation composed, **revision 2** (corrects the P2SH sigop term, finding F1 of the source review) | `74c0941a-c7b7-413d-ba32-656b815d24b0` | Draft (awaiting Submit); same 19 theorems, proofs re-checked | `BitcoinBlock.acceptance` | 19 | 19 |
| — | Umbrella: *Bitcoin Mainnet: Correctness of the Consensus Rules* | `c416e514-a450-41cc-8dd7-bef33d605a8e` | Draft; references all 147 theorems + 14 definitions of the thirteen missions; **main theorem set to `BitcoinBlock.acceptance`** | `BitcoinBlock.acceptance` (Proved) | — | — |

Each Draft proposal has: a definition item (verbatim transcription with source lines), the theorem items with formal statements, prose statements, sources and tags, a blind independent read-back on every item, a goal (`main_item_id`) and milestones.

## What the theorems say (per mission)

**Subsidy.** `coreSubsidy = ⌊5e9 / 2^⌊h/210000⌋⌋`; ≤ MAX_MONEY; non-increasing; halving recurrence; zero iff h ≥ 6,930,000; exact total 2,099,999,997,690,000 sat; cumulative issuance < MAX_MONEY for every chain length.

**PoW.** Overflow flag ⇔ specTarget ≥ 2^256 (exact); SetCompact = exact value without overflow; CheckProofOfWork acceptance characterized; SetCompact∘GetCompact rounds down, yields valid words, and is monotone; timespan clamp in [T/4, 4T]; next target ≤ powLimit; off-boundary unchanged; **CalculateNextWorkRequired always passes PermittedDifficultyTransition** (given prev target ≤ powLimit).

**Merkle.** Base cases (empty/single/pair); root independent of the flag; flag sticky; level distributes over even splits; **duplicating an aligned block of 2^k trailing leaves after a non-empty aligned prefix preserves the root and sets the mutation flag** (general CVE-2012-2459).

**UTXO.** CheckTransaction ⇒ distinct inputs & in-range outputs; CheckTxInputs returns exactly valueIn − valueOut in range with inputs present; spend/add accounting; **ordinary tx lowers ledger by ≥ fee (no value creation)**; coinbase adds ≤ valueOut; **block raises ledger by ≤ subsidy(h)**; chain bound; **from empty ledger, total ≤ Σ subsidy** (subsidy a parameter; compose with mission 2 for the absolute cap).

**Headers.** MTP ∈ window, bounded, depends on 11 times only; **MTP non-decreasing under time-too-old** (one step and along a chain); ContextualCheckBlockHeader characterized; BIP34/66/65 version floors.

**Script.** (Blind audit of the first draft caught two transcription gaps, both fixed: `nOpCount` counts only opcodes above `OP_16`, and the stack-size check also runs after a skipped opcode, as in `interpreter.cpp` lines 462 and 1232.) `CScriptNum` serialize/set_vch round-trip; serializer output always minimal; strict 4-byte constructor accepts serialized values; `CastToBool` ⇔ nonzero script number (both zero encodings false); push-only scripts leave exactly their pushes; any disabled opcode (CVE-2010-5137) fails from every state, executed or not; `execOp` never lowers `nOpCount` (CHECKMULTISIG's increase stays ≤ 201); >201 operations always fail; **P2PK and P2PKH templates correct in both directions for every oracle**.

**Serialization.** Fixed-width and CompactSize round-trips; CompactSize canonical (only the shortest encoding is accepted) and bounded; 80-byte headers round-trip; transactions round-trip in basic and BIP144 formats (witness-aware reader needs an input, a genuine source quirk); txid ignores witnesses; legacy weight = 4 × size; SHA-256/Hash160 sizes; **genesis coinbase hashes to the recorded merkle root and genesis header to hashGenesisBlock, by kernel evaluation of the transcribed SHA-256**; block serialization is a left inverse and injective.

**Signatures.** Strict DER (BIP66) characterized in both directions as the canonical `30 L 02 r 02 s ht` layout with minimal integers; SIGHASH_SINGLE bug; legacy and BIP143 sighashes ignore scriptSigs/witnesses; ANYONECANPAY locality; CPubKey::IsValid; S normalization; lax-parse overflow rejected; empty signature is a clean false; DERSIG makes malformed signatures script errors; the legacy checker characterized as ECDSA on the sighash; P2PKH bytes parse; **P2PKH correct against Core's concrete hashes and checker**. secp256k1 ECDSA/Schnorr are executable transcriptions validated against BIP340 vectors, the BIP143 example and independently generated signatures.

**VerifyScript.** IsPayToScriptHash/IsWitnessProgram characterized; canonical pushes parse and are push-only; witness malleation and unexpected-witness rules; unknown witness versions accept iff the program is a true script value; **native P2WPKH correct** (goal), native P2WSH characterized, **P2SH correct**, **P2SH-P2WPKH correct** — all two-directional against the concrete BIP143 checker. Taproot branch left as a handler parameter.

**Activation.** Activation monotone; flags before BIP66 / after SegWit; activation order DERSIG→CLTV→CSV→NULLDUMMY; BIP16 exception = no flags; Taproot exception = all but TAPROOT; exceptions only remove; CSV lock-time flag; **GetBlockScriptFlags monotone in height**.

**Taproot.** `ComputeTapbranchHash` symmetric; merkle root of a control block is a left fold along the path; `OP_SUCCESSx` accepts outright, `OP_CHECKMULTISIG` rejected, `MINIMALIF` consensus, 50-weight budget per passed signature, empty signature is a clean false; BIP341 sighash guards (undefined types, `SINGLE` without output); key path with and without annex is the Schnorr check of the output key; `CheckSchnorrSignature` characterized (64/65 bytes); **key-path spending correct** (goal); a verifying script-path spend has a valid commitment. `verifyScriptFull` is the complete `VerifyScript` with no parameter left.

**Block composition.** Genesis passes `CheckBlock` (kernel evaluation); the header path is the Header mission's check; `BLOCK_TIME_FUTURE` characterized, transient, and the only clock dependence; `CheckTransaction`, `CheckBlock`, `ContextualCheckBlock`, `CheckTxInputs`, `SequenceLocks` (= `satisfiesBIP68` via the published `fold_acceptance`), the transaction loop and `ConnectBlock` each characterized by a predicate; when the BIP30 scan is skipped; the resulting ledger is `ApplySpec`; reachable states are well formed; chain work strictly increases; **`DisconnectBlock` undoes `ConnectBlock`** cleanly; and the umbrella goal **`acceptance`: R(S) ⟹ (C(S,B,t) accepts ⟺ V(S,B,t))**. Exercised on real mainnet data: block 170 (the first user-to-user spend) validates end to end against block 9's coinbase and disconnects back (`tests/Block170Test.lean`).

## Done

All 61 theorems across the first seven missions are **Proved** on the platform (56 submitted in this round, all ACCEPTED on first submission). The Script mission (8) was published and all 10 of its theorems are **Proved** (10 of 10 ACCEPTED on first submission), bringing the total to 71 proved theorems across eight missions; the umbrella references all of them. The umbrella proposal now carries reference items for every published definition and theorem. The seven proposals await moderator review (`In review`); that step is the platform's, not yours.

## Not done (honest boundary)

- **Serialization / SHA-256d / CompactSize** (area 1), **script byte-level parsing, P2SH and witness-program dispatch in `VerifyScript`, multi-block reorganization as a single statement (the disconnect theorem applied in sequence), assumed-valid shortcuts (not modeled: scripts are always checked), and the cryptographic assumptions (proof-of-work hardness, unforgeability), which are outside functional correctness. Every other area now has a concrete, source-linked transcription with its theorems proved; missions 9–13 are published with every proof accepted; the umbrella references all of them and has `BitcoinBlock.acceptance` as its main theorem, awaiting the user's Submit. The source review (`REVIEW.md`, spots 1–11 done) found one defect, F1, in mission 13's sigop accounting; the corrected definition is proposed as revision 2 and, once published, replaces mission 13's references on the umbrella.
- Umbrella goal theorem cannot be stated until areas 1, 8 (signature layer), 10 exist.

## Technical notes for future solvers

- The platform rejects `bv_decide` (`Lean.ofReduceBool`); use `BitVec.toNat` + `Nat` bitwise lemmas (`Nat.and_div_two_pow`, `Nat.and_mod_two_pow`, `Nat.and_two_pow_sub_one_eq_mod`, `Nat.and_one_is_mod`).
- Huge `if`-chains (`execOp`, 37 branches): `split at h` on the whole term times out; walk the chain with `by_cases`/`rw [if_pos/if_neg] at h`, `dsimp only at h` to zeta-reduce `let`s and unreduced `match`es, then `split`/`cases h` per branch. `cases h` on `some x = some s'` may eliminate either side, so take facts about `x` before it.
- `BitcoinBIP68.core_correct` and `fold_acceptance` hold without the admissibility/overflow hypotheses (unbounded `Int`); only `calculated_bounds` needs them.
- Local toolchain: Lean release tarball v4.33.1 (no elan/Mathlib needed for these bundles). Workspace layout per `prove2me_workspace`.

## Files (scratchpad)
- `lean_backup/{Definitions,Theorems,Solutions}` — all Lean sources (9 definition files, 71 statement stubs, 82 solution files).
- `expl/` — proof explanations per theorem.
- `*_description.md`, `*_items.py` — mission descriptions and prose statements.
- `core-src/` — the pinned Bitcoin Core sources consulted.
