# NOTES: BitcoinScriptV2 — closing limits L1 and L10 of the script interpreter

Mission files: `Definitions/Def_BitcoinScriptV2.lean` (namespace `BitcoinScriptV2`, imports
`Def_BitcoinVerify`), `Solutions/Sol_BitcoinScriptV2_all.lean` (20 public theorems, sorry-free),
`Theorems/Thm_BitcoinScriptV2_*.lean` and `Solutions/Sol_BitcoinScriptV2_*.lean` (pipeline stubs and
splits, all building), `tests/CoreV2Tests.lean`, `tests/CoreV2TxTests.lean`,
`tests/CoreV2ScriptTests1..5.lean`. Nothing under the published `Def_BitcoinScript.lean`,
`Def_BitcoinSig.lean`, `Def_BitcoinVerify.lean` was touched.

## 1. The two limits (REVIEW.md §2, L1 and L10)

Core, `src/script/interpreter.cpp` at `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`:

| Core | lines | semantics |
|---|---|---|
| `EvalScript` | 432 | `CScript::const_iterator pbegincodehash = script.begin();` |
| `case OP_CODESEPARATOR` | 1058–1066 | when executed (the opcode is outside `OP_IF…OP_ENDIF`, so it runs iff `fExec`): `pbegincodehash = pc;` — `pc` has already been advanced past the opcode byte by `GetOp`, so the script code becomes the bytes *after* the separator |
| `case OP_CHECKSIG/VERIFY` | 1069–1092 | `EvalChecksig(vchSig, vchPubKey, pbegincodehash, pend, …)` (1080) |
| `EvalChecksigPreTapscript` | 331–352 | `CScript scriptCode(pbegincodehash, pend)` (336); in `SigVersion::BASE` only, `FindAndDelete(scriptCode, CScript() << vchSig)` (339–343); `CheckSignatureEncoding`/`CheckPubKeyEncoding` (345); `checker.CheckECDSASignature(vchSig, vchPubKey, scriptCode, sigversion)` (349) |
| `case OP_CHECKMULTISIG/VERIFY` | 1115–1200 | after the count/stack-depth checks, `CScript scriptCode(pbegincodehash, pend)` (1149); `for k in 0 … nSigsCount-1: vchSig = stacktop(-isig-k); if BASE: FindAndDelete(scriptCode, CScript() << vchSig)` (1152–1159) — every signature, top of the stack first, before any check; the `while` loop (1161–1187) then runs the encoding checks (1170) and `CheckECDSASignature(vchSig, vchPubKey, scriptCode, sigversion)` (1177) on that one script code |
| `FindAndDelete` | 239 | as transcribed by `BitcoinSig.findAndDelete` |
| `SignatureHash` BASE | 1610, 1673 | `CTransactionSignatureSerializer` with the given `scriptCode`; `SerializeScriptCode` (1281–1300) drops `OP_CODESEPARATOR`s from it (`BitcoinSig.serScriptCode`) |

The published model (`BitcoinVerify.evalBytes` → `BitcoinSig.legacyOracle … script`) hands the oracle the
*whole* executed script and lets `checkSigPreTapscript` delete the one signature being checked:

* **L1**: no `pbegincodehash`; an executed `OP_CODESEPARATOR` is a no-op for the signature hash.
* **L10**: in `OP_CHECKMULTISIG` only the checked signature is deleted, and separately for each check.

## 2. Design of the V2 interpreter

* `annotate : Bytes → Option (List (Instr × Bytes))` — the `GetOp` parse pairing every instruction with the
  bytes after it (Core's `pc` once the instruction is read, i.e. `CScript(pc, pend)`).
  `annotate_parse`: `(annotate s).map (map Prod.fst) = parseScript s`.
* `StateV2 = { st : State, scriptCode : Bytes }` — the published state plus `CScript(pbegincodehash, pend)`;
  the run starts with `scriptCode := script`.
* `OracleV2.checkSig : (scriptCode : Bytes) → (sig pk : Bytes) → Option Bool` — the encoding checks and
  `CheckECDSASignature` on a script code that the *interpreter* has already `FindAndDelete`d (lines 345–349
  and 1170–1177). `legacyOracleV2 f tx nIn amount v` is the concrete one.
* `fadSig v sc sig` = `FindAndDelete(sc, CScript() << sig)` in `.base`, `sc` in `.witnessV0`;
  `fadAll v sc sigs = sigs.foldl (fadSig v) sc` (Core's `k` loop, top of the stack first).
* `multisigSigs stack` — the `nSigsCount` signatures an `OP_CHECKMULTISIG` on this stack examines.
* `oracleAt v o s i : BitcoinScript.Oracle` — the published oracle the instruction `i` is executed with:
  for `OP_CHECKMULTISIG(VERIFY)` `withCode o (fadAll v s.scriptCode (multisigSigs s.st.stack))` (one script
  code for the whole loop); otherwise `withCodeSig o v s.scriptCode`, whose `checkSig sig pk =
  o.checkSig (fadSig v sc sig) sig pk` is exactly `EvalChecksigPreTapscript` (and is never consulted by a
  non-signature opcode).
* `stepV2 f v o s (i, r) = (BitcoinScript.step f (oracleAt v o s i) s.st i).map (⟨·, if i = OP_CODESEPARATOR ∧
  fExec then r else s.scriptCode⟩)` — **every opcode runs through the published `execOp`/`step`**; only the
  `pbegincodehash` bookkeeping is new. `runV2`, `evalScriptV2 f v o stack script`, `evalBytesV2 c v stack
  script` (with the `MAX_SCRIPT_SIZE` test), `executeWitnessScriptV0V2`, `verifyWitnessProgramV2`,
  `verifyScriptV2 tap c scriptSig scriptPubKey witness` mirror the published `BitcoinVerify` functions line by
  line with the V2 evaluator on the legacy and witness-v0 paths; the Taproot handler is untouched.

Consequences checked against Core: an unexecuted separator changes nothing; the script code after an executed
one is the suffix after the separator byte (`codesep_tracks`); a `CHECKSIG` deletes its own signature from that
suffix (`checksig_deletes_one`); a `CHECKMULTISIG` deletes every signature push, in stack order, once
(`multisig_deletes_all`); in witness v0 nothing is deleted (`fadAll_witness`) but the separator still restarts
the code.

## 3. Side conditions and the agreement theorems

The published oracle is the V2 oracle on the whole script: `legacyOracle_eq : legacyOracle f tx nIn amount v sc =
withCodeSig (legacyOracleV2 f tx nIn amount v) v sc` (by `rfl`).

* `StepOk v s i` — if `i` is executed: it is not `OP_CODESEPARATOR`, and if it is an `OP_CHECKMULTISIG(VERIFY)`
  then `fadSig v s.scriptCode sig = s.scriptCode` for every `sig ∈ multisigSigs s.st.stack` (no signature push
  occurs in the script code; vacuous in witness v0).
* `RunOk f v o s l` — every step of the V2 run satisfies `StepOk` (as far as the run gets, so failing runs are
  covered). `EvalOk c v stack script` — `RunOk` for the concrete context from the initial state.
* Static sufficient conditions: `NoCodeSep s` (no `OP_CODESEPARATOR` instruction), `NoMultisig s`;
  `runOk_of_static`, `runOk_witness` (in witness v0 `NoCodeSep` alone suffices), `evalOk_of_static`,
  `evalOk_witness`.

| theorem | statement |
|---|---|
| `legacyOracle_eq` | `legacyOracle f tx nIn amount v sc = withCodeSig (legacyOracleV2 f tx nIn amount v) v sc` |
| `annotate_parse` | `(annotate s).map (List.map Prod.fst) = parseScript s` |
| `annotate_suffix` | `annotate s = some l → (i, r) ∈ l → ∃ pre, s = pre ++ r` |
| `annotate_op_suffix` | `annotate s = some l → (.op c, r) ∈ l → ∃ p, s[p]? = some c ∧ r = s.drop (p+1)` |
| `stepV2_codesep` | executed `OP_CODESEPARATOR` with suffix `r`: `stepV2 … = some s' → s'.scriptCode = r` |
| `stepV2_keeps` | any other step (or an unexecuted separator) keeps `scriptCode` |
| `codesep_tracks` | the `k`-th instruction an executed `OP_CODESEPARATOR` with suffix `r`: `s'.scriptCode = r ∧ ∃ p, script[p]? = some OP_CODESEPARATOR ∧ r = script.drop (p+1)` |
| `multisig_deletes_all` | `(oracleAt v o s (.op c)).checkSig sig pk = o.checkSig (fadAll v s.scriptCode (multisigSigs s.st.stack)) sig pk` for `c ∈ {CHECKMULTISIG, CHECKMULTISIGVERIFY}` |
| `fadAll_base` | `fadAll .base sc sigs = sigs.foldl (fun sc sig => (findAndDelete sc (pushBytes sig)).1) sc` |
| `fadAll_witness` | `fadAll .witnessV0 sc sigs = sc` |
| `multisigSigs_eq` | `multisigSigs (nk :: (keys ++ ns :: (sigs ++ rest))) = sigs` for well-formed counts |
| `checksig_deletes_one` | `(oracleAt v o s (.op c)).checkSig sig pk = o.checkSig (fadSig v s.scriptCode sig) sig pk` for `c ∈ {CHECKSIG, CHECKSIGVERIFY}` |
| `stepV2_agree` | `s.scriptCode = sc → StepOk v s i → stepV2 f v o s (i, r) = (step f (withCodeSig o v sc) s.st i).map (⟨·, sc⟩)` |
| `eval_agree` | `annotate script = some l → RunOk f v o ⟨State.initial stack, script⟩ l → evalScriptV2 f v o stack script = evalScript f (withCodeSig o v script) stack (l.map Prod.fst)` |
| `evalBytes_agree` | `EvalOk c v stack script → evalBytesV2 c v stack script = evalBytes c v stack script` |
| `runOk_of_static` | `NoCodeSep (l.map Prod.fst) → NoMultisig (l.map Prod.fst) → RunOk f v o s l` |
| `runOk_witness` | `NoCodeSep (l.map Prod.fst) → RunOk f .witnessV0 o s l` |
| `evalOk_of_static` | `(∀ s, parseScript script = some s → NoCodeSep s ∧ NoMultisig s) → EvalOk c v stack script` |
| `evalOk_witness` | `(∀ s, parseScript script = some s → NoCodeSep s) → EvalOk c .witnessV0 stack script` |
| `verify_agree` | `EvalOk` for the scriptSig (from `[]`), the scriptPubKey (from the scriptSig's stack), the redeem script (from the rest of that stack) and the witness script (from the witness stack) → `verifyScriptV2 tap c scriptSig scriptPubKey witness = verifyScript tap c scriptSig scriptPubKey witness` |

Proof structure. `stepV2_agree` is reflexive for every non-multisig step (the oracle `withCodeSig o v sc` *is*
the published oracle, `legacyOracle_eq`); for an executed multisig the side condition makes `fadAll` the
identity and the private lemma `execOp_multisig_congr` (the multisig branch of `execOp` consults `checkSig`
only on `multisigSigs s.stack`; proved by pruning the opcode chain with `simp (decide := true)` and case
analysis of the branch) plus `multisigLoop_congr` close the gap. `runV2_agree` is an induction over the
annotated list; `evalBytes_agree` adds `annotate_parse` and `legacyOracle_eq`; `verify_agree` follows the
shared control flow of the two verifiers, with the P2WPKH script shown separator-free by a private
`parseScript_p2pkh` (no imported stub is used, so the build is sorry-free).

## 4. Vectors (Core `script_tests.json`, `tx_valid.json`, `tx_invalid.json` through `verifyScriptV2`)

| file | cases | agree |
|---|---|---|
| `tests/CoreV2ScriptTests1..5.lean` | 793 | **793** (unchanged) |
| `tests/CoreV2TxTests.lean` | 201 (122 valid + 79 invalid) | **201** (was 185) |
| `tests/CoreV2Tests.lean` | the 9 former mismatches + 8 per-input checks | **17/17** |

The nine flipped vectors: `valid#79, #81, #85, #222, #224, #226, invalid#62` (L1) and `valid#96, #244`
(L10) — exactly the set of `REVIEW_DIFFTEST.md`; no agreeing case regressed (994/994).

## 5. Limits that remain

* `SCRIPT_VERIFY_CONST_SCRIPTCODE` (policy, interpreter.cpp 340–342, 1157–1158, and the pre-switch check on
  `OP_CODESEPARATOR`) is still modeled as off, as are all other policy flags.
* The V2 evaluator takes a byte script (`annotate`), so `evalScriptV2` has no parsed-`Script` entry point; the
  agreement theorems bridge via `annotate_parse`.
* `verify_agree`'s side conditions are stated per executed script (semantic `EvalOk`); the static conditions
  `NoCodeSep`/`NoMultisig` give them for the standard templates (P2PK, P2PKH, P2WPKH, P2SH/P2WSH without
  separators or multisig), but a script with `OP_CHECKMULTISIG` needs the run-dependent form, since whether a
  signature push occurs in the script code depends on the stack.
* Tapscript (`BitcoinTaproot`) already tracked `codeseparator_pos` and has no `FindAndDelete`; it is reused
  as is.
