SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, "
       "OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), "
       "SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); "
       "Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision")
TAGS = ["bitcoin", "consensus", "script", "interpreter", "codeseparator", "checkmultisig", "findanddelete", "sighash", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinScriptV2",
    "definition_title": "The legacy script interpreter with the signature script code tracked exactly (closing limits L1 and L10)",
    "natural_language_statement": r"""A second interpreter over the script mission's `BitcoinScript`, whose only difference is that the signature checks see the *script code* exactly as Core computes it.

**`OracleV2`** — like the script mission's `Oracle`, but `checkSig : (scriptCode : Bytes) → (sig pk : Bytes) → Option Bool` receives the script code. **`fadSig v sc sig`** — in `SigVersion::BASE`, `FindAndDelete` of the push of `sig` from `sc`; the identity in witness v0. **`fadAll v sc sigs`** — the fold of `fadSig` over a list of signatures. **`withCode o sc`**, **`withCodeSig o v sc`** — the published `Oracle` obtained by fixing the script code (and, for `withCodeSig`, deleting the checked signature as the published model does). **`multisigSigs stack`** — the signatures an `OP_CHECKMULTISIG` will consume, read off the stack layout.

**`StateV2`** — the published `State` plus `scriptCode : Bytes`, Core's `CScript(pbegincodehash, pend)`. **`oracleAt v o s i`** — the oracle for instruction $i$: `OP_CHECKSIG(VERIFY)` see `fadSig` of the one signature, `OP_CHECKMULTISIG(VERIFY)` see `fadAll` of all their signatures (deleted before any check, as Core does), every other instruction sees the code unchanged. **`stepV2`** — the published `step` with `oracleAt`, and an executed `OP_CODESEPARATOR` resets `scriptCode` to the bytes after the opcode. **`annotate s`** — the `GetOp` parse of a byte script paired with the byte suffix after each instruction; **`runV2`**, **`evalScriptV2`**, **`legacyOracleV2`**, **`evalBytesV2`**, **`executeWitnessScriptV0V2`**, **`verifyWitnessProgramV2`**, **`verifyScriptV2`** — the verification mission's pipeline over the new evaluator (the Taproot handler unchanged).

**Side conditions.** `NoCodeSep s`, `NoMultisig s` (no such instruction in the parsed script); `StepOk v s i` (the instruction is not an executed code separator, and a multisig's signatures do not occur as pushes in the current script code), `RunOk`, `EvalOk c v stack script` (along the actual run).

**Formalization Note.** The published interpreter (`BitcoinScript`, `BitcoinSig.legacyOracle`, `BitcoinVerify.verifyScript`) is exact except for two documented limits: L1 (the script code does not restart after an executed `OP_CODESEPARATOR`) and L10 (`OP_CHECKMULTISIG` deletes only the checked signature). This file is the interpreter without those limits; the theorems state that it agrees with the published one wherever the limits do not bite, and its tests agree with every one of Core's 994 script and transaction vectors at the pinned revision. Only `Std` is imported.""",
}

T = {}
T["legacyOracle_eq"] = ("The published oracle is the V2 oracle with the code fixed", r"""`legacyOracle f tx nIn amount v sc = withCodeSig (legacyOracleV2 f tx nIn amount v) v sc`, by definition.""")
T["annotate_parse"] = ("The annotated parse projects to the published parse", r"""`(annotate s).map (List.map Prod.fst) = parseScript s`.""")
T["annotate_suffix"] = ("Every annotation is a suffix of the script", r"""If `annotate s = some l` and `(i, r) ∈ l` then `s = pre ++ r` for some `pre`.""")
T["annotate_op_suffix"] = ("An opcode's annotation is the bytes after its position", r"""If `annotate s = some l` and `(.op c, r) ∈ l` then there is a position $p$ with `s[p]? = some c` and `r = s.drop (p+1)`.""")
T["stepV2_codesep"] = ("An executed OP_CODESEPARATOR resets the script code to its suffix", r"""If `stepV2` executes `(.op OP_CODESEPARATOR, r)` from an executing state and succeeds, the new `scriptCode` is `r`.""")
T["stepV2_keeps"] = ("Every other step keeps the script code", r"""If the instruction is not an executed code separator, `stepV2` leaves `scriptCode` unchanged.""")
T["codesep_tracks"] = ("The script code after an executed OP_CODESEPARATOR at byte p is the script from p+1 (L1 closed)", r"""For an annotated script and its $k$-th instruction `(.op OP_CODESEPARATOR, r)`, an executing successful step gives `scriptCode = r` with `r = script.drop (p+1)` for the opcode's byte position $p$: Core's `pbegincodehash = pc`.""")
T["checksig_deletes_one"] = ("OP_CHECKSIG checks against the code with its own signature deleted", r"""The oracle at an `OP_CHECKSIG(VERIFY)` checks `sig` against `fadSig v scriptCode sig`.""")
T["fadAll_base"] = ("In SigVersion::BASE, deleting all signatures is a fold of FindAndDelete", r"""`fadAll .base sc sigs = sigs.foldl (fun sc sig => (findAndDelete sc (pushBytes sig)).1) sc`.""")
T["fadAll_witness"] = ("In witness v0 nothing is deleted", r"""`fadAll .witnessV0 sc sigs = sc`.""")
T["multisigSigs_eq"] = ("The multisig signatures are read off the stack layout", r"""For a stack `nk :: keys ++ ns :: sigs ++ rest` with `nk`, `ns` decoding to the lengths of `keys` and `sigs`: `multisigSigs … = sigs`.""")
T["multisig_deletes_all"] = ("OP_CHECKMULTISIG checks every signature against the code with all its signatures deleted (L10 closed)", r"""The oracle at an `OP_CHECKMULTISIG(VERIFY)` checks each `sig` against `fadAll v scriptCode (multisigSigs stack)`: Core deletes all `nSigsCount` signature pushes before any check.""")
T["stepV2_agree"] = ("Outside the two limits a V2 step is the published step", r"""Under `StepOk v s i` and `scriptCode = sc`: `stepV2 f v o s (i, r) = (step f (withCodeSig o v sc) s.st i).map (⟨·, sc⟩)`.""")
T["eval_agree"] = ("Outside the two limits the V2 evaluator is the published evaluator", r"""Under `RunOk` along the run: `evalScriptV2 f v o stack script = evalScript f (withCodeSig o v script) stack (l.map Prod.fst)` for the annotated parse `l`.""")
T["evalBytes_agree"] = ("Outside the two limits the V2 byte-level evaluator is the published one", r"""Under `EvalOk c v stack script`: `evalBytesV2 c v stack script = evalBytes c v stack script`.""")
T["runOk_of_static"] = ("Scripts without OP_CODESEPARATOR and OP_CHECKMULTISIG are always outside the limits", r"""`NoCodeSep` and `NoMultisig` of the parsed script imply `RunOk` from any state.""")
T["runOk_witness"] = ("In witness v0 only OP_CODESEPARATOR matters", r"""`NoCodeSep` alone implies `RunOk` for `SigVersion::WITNESS_V0` (no `FindAndDelete` there).""")
T["evalOk_of_static"] = ("Static sufficient condition for EvalOk", r"""If every parse of the script satisfies `NoCodeSep ∧ NoMultisig`, then `EvalOk c v stack script`.""")
T["evalOk_witness"] = ("Static sufficient condition for EvalOk in witness v0", r"""If every parse satisfies `NoCodeSep`, then `EvalOk c .witnessV0 stack script`.""")
T["verify_agree"] = ("Outside the two limits VerifyScript is unchanged: the published verifier is exact there", r"""If the scriptSig, the scriptPubKey on the resulting stack, the P2SH redeem script and the witness script are each `EvalOk` in their context: `verifyScriptV2 tap c scriptSig scriptPubKey witness = verifyScript tap c scriptSig scriptPubKey witness`. Hence the published `verifyScript` (and every theorem proved about it) is exact for every script execution that does not execute an `OP_CODESEPARATOR` in a signature-checked legacy script and does not push a multisig's own signature into its script code; `verifyScriptV2` is the exact rule everywhere, as 994 of 994 Core vectors confirm.""")
THEOREMS = {f"BitcoinScriptV2.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinScriptV2.codesep_tracks"]["ms"] = ("L1 closed", "The byte position of an executed separator is recovered from the annotation.")
THEOREMS["BitcoinScriptV2.multisig_deletes_all"]["ms"] = ("L10 closed", "All signatures deleted before any check, top-first as Core pops them.")
THEOREMS["BitcoinScriptV2.eval_agree"]["ms"] = ("Equivalence outside the limits", "Per-step agreement with the published `step` under `StepOk`, folded along the run.")
ORDER = ["BitcoinScriptV2." + k for k in ["legacyOracle_eq", "annotate_parse", "annotate_suffix", "annotate_op_suffix", "stepV2_codesep", "stepV2_keeps",
  "codesep_tracks", "checksig_deletes_one", "fadAll_base", "fadAll_witness", "multisigSigs_eq", "multisig_deletes_all", "stepV2_agree",
  "eval_agree", "evalBytes_agree", "runOk_of_static", "runOk_witness", "evalOk_of_static", "evalOk_witness", "verify_agree"]]
