# Script interpreter V2: limits L1 and L10 closed (draft section)

Revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, mainnet parameters. New files:
`Definitions/Def_BitcoinScriptV2.lean`, `Solutions/Sol_BitcoinScriptV2_all.lean` (20 kernel-checked
theorems, no `sorry`), `tests/CoreV2Tests.lean`, `tests/CoreV2TxTests.lean`,
`tests/CoreV2ScriptTests1..5.lean`; design notes in `NOTES_BitcoinScriptV2.md`. The published
`Def_BitcoinScript.lean`, `Def_BitcoinSig.lean`, `Def_BitcoinVerify.lean` are unchanged.

## What changed

`BitcoinScriptV2` is a second legacy/witness-v0 evaluator that reuses the published `BitcoinScript.execOp`
and `step` for every opcode and adds only the two pieces of bookkeeping the published model lacks:

* **L1 — `pbegincodehash`.** The run is over the `GetOp` parse paired with byte offsets (`annotate`); the state
  carries `scriptCode = CScript(pbegincodehash, pend)`, initially the whole script, and an *executed*
  `OP_CODESEPARATOR` sets it to the bytes after the separator (interpreter.cpp:1058–1066). Both
  `OP_CHECKSIG(VERIFY)` and `OP_CHECKMULTISIG(VERIFY)` hash that script code, in `SigVersion::BASE` and
  `WITNESS_V0` alike (`EvalChecksigPreTapscript`, :336; `OP_CHECKMULTISIG`, :1149).
* **L10 — multisig `FindAndDelete`.** The interpreter, not the oracle, performs Core's `FindAndDelete`s: one
  signature for `OP_CHECKSIG` (:339–343), and for `OP_CHECKMULTISIG` the pushes of *all* `nSigsCount`
  signatures, top of the stack first, before the first check (:1152–1159), in `BASE` only. The oracle
  (`OracleV2.checkSig scriptCode sig pk`) is the encoding checks plus
  `checker.CheckECDSASignature(sig, pk, scriptCode, sigversion)` on the script code it is handed (:345–349,
  :1170–1177).

`verifyScriptV2` mirrors `BitcoinVerify.verifyScript` with the V2 evaluator on the legacy and witness-v0
paths; the Taproot handler (which already tracked `codeseparator_pos`) is reused as is.

## Which vectors flipped

All 994 included Core cases were re-run through `verifyScriptV2`:

| file | cases | published model | V2 |
|---|---|---|---|
| `script_tests.json` (`CoreV2ScriptTests1..5`) | 793 | 793 | **793** |
| `tx_valid.json` + `tx_invalid.json` (`CoreV2TxTests`) | 201 | 185 | **201** |

The nine cases that disagreed (`REVIEW_DIFFTEST.md`, mismatch table) now agree, and nothing regressed:
`valid#79` (hash starts at the separator), `valid#81` (only once execution reached it), `valid#85` (separator
inside an executed `IF`), `valid#222` (BIP143 P2WSH with `OP_CODESEPARATOR`), `valid#224`/`#226` (BIP143
executed/unexecuted separator pairs), `invalid#62` (the inverted `IF` case, now correctly rejected) for L1;
`valid#96` (2-of-3 P2SH whose redeem script embeds one of the signatures) and `valid#244`
(`2 CHECKMULTISIGVERIFY <sig1> <sig2> DROP`) for L10. `tests/CoreV2Tests.lean` holds these nine with Core's
expected verdicts plus a per-input check of each multi-input vector (17/17 `true`).

## The equivalence theorem

The published interpreter is exact outside the two limits, and this is now a theorem rather than a review
remark. With `withCodeSig o v sc` the published oracle derived from a V2 oracle on a fixed script code
(`legacyOracle f tx nIn amount v sc = withCodeSig (legacyOracleV2 f tx nIn amount v) v sc`, by `rfl`):

* `StepOk v s i`: the executed instruction is not an `OP_CODESEPARATOR`, and if it is an
  `OP_CHECKMULTISIG(VERIFY)` then no signature push occurs in the script code (every `FindAndDelete` is the
  identity; vacuous in witness v0). `RunOk` lifts this to every step of the V2 run, failing runs included.
* `eval_agree`: `annotate script = some l → RunOk f v o ⟨State.initial stack, script⟩ l →
  evalScriptV2 f v o stack script = evalScript f (withCodeSig o v script) stack (l.map Prod.fst)`.
* `evalBytes_agree`: `EvalOk c v stack script → evalBytesV2 c v stack script = evalBytes c v stack script`.
* `verify_agree`: under `EvalOk` for the four scripts a verification executes (scriptSig, scriptPubKey, redeem
  script, witness script), `verifyScriptV2 tap c scriptSig scriptPubKey witness = verifyScript tap c scriptSig
  scriptPubKey witness`.
* Static sufficient conditions: `NoCodeSep` and `NoMultisig` on the parsed script (`runOk_of_static`,
  `evalOk_of_static`); in witness v0, `NoCodeSep` alone (`runOk_witness`, `evalOk_witness`). So every theorem
  proved about the published verifier on separator-free, multisig-free scripts (P2PK, P2PKH, P2WPKH, the
  HTLC/anchor/to-local scripts) transfers to V2 unchanged.

Characterizations of the new bookkeeping: `codesep_tracks` (after an executed separator at byte position `p`
the script code is `script.drop (p+1)`), `checksig_deletes_one`, `multisig_deletes_all`
(`fadAll v scriptCode (multisigSigs stack)` = Core's `k` loop), `fadAll_base`, `fadAll_witness`,
`multisigSigs_eq`.

Not covered: `SCRIPT_VERIFY_CONST_SCRIPTCODE` and the other policy flags remain off, as in the published
model; the side condition for scripts containing `OP_CHECKMULTISIG` is run-dependent by nature (whether a
signature push occurs in the script code depends on the stack), so `verify_agree` is stated with the semantic
`EvalOk` rather than a syntactic test.
