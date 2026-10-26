SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, "
       "EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, "
       "src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; "
       "XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; "
       "IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7")
TAGS = ["bitcoin", "consensus", "taproot", "tapscript", "schnorr", "bip341", "bip342", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinTaproot",
    "definition_title": "Taproot and Tapscript: the version-1 witness branch, BIP341 signature hash, commitment check, and the Tapscript interpreter rules",
    "natural_language_statement": r"""**Constants.** `TAPROOT_LEAF_MASK` = 0xfe, `TAPROOT_LEAF_TAPSCRIPT` = 0xc0, control-block sizes 33 + 32·k for $k \le 128$, `ANNEX_TAG` = 0x50, `VALIDATION_WEIGHT_OFFSET` = 50, `VALIDATION_WEIGHT_PER_SIGOP_PASSED` = 50, `SIGHASH_DEFAULT` = 0, `OP_CHECKSIGADD` = 0xba.

**Hashes and the tweak.** `tagged t m` is the BIP340 tagged hash $\mathrm{SHA256}(\mathrm{SHA256}(t)\,\|\,\mathrm{SHA256}(t)\,\|\,m)$. `tapleafHash v s` = `TapLeaf`(v ‖ compactSize(|s|) ‖ s); `tapbranchHash a b` = `TapBranch` of the two children in lexicographic order (`lexLt` is `std::lexicographical_compare`); `controlNodes` cuts the 32-byte path nodes after the 33-byte base; `taprootMerkleRoot control leaf` folds `tapbranchHash` over them from the leaf; `tapTweakHash p r` = `TapTweak`(p ‖ r). `xonlyTweakAddCheck q parity P t` is `secp256k1_xonly_pubkey_tweak_add_check`: $t < n$, $Q = P + tG \ne \mathcal{O}$, $x(Q)$ is the 32-byte key `q` and the parity of $y(Q)$ is `parity`; `checkTapTweak` lifts the internal key with the signature mission's `liftX` first; `verifyTaprootCommitment control program leafHash` is `VerifyTaprootCommitment` (parity from bit 0 of the control byte, internal key bytes 1–32, root from the path).

**BIP341 signature hash.** `sigHashSchnorr tx spent inPos hashType tapscript ed` is `SignatureHashSchnorr` with `ExecData` (annex presence and hash, tapleaf hash, code-separator position): `none` for a hash type outside $\{0,1,2,3,0x81,0x82,0x83\}$ and for `SIGHASH_SINGLE` without a matching output; otherwise the `TapSighash` tagged hash of the epoch byte, hash type, version, locktime, the four precomputed hashes unless `ANYONECANPAY`, the outputs hash for `ALL`, the spend-type byte, the input (index, or outpoint ‖ spent output ‖ sequence), the annex hash, the single-output hash and the Tapscript extension. `spent` lists the spent outputs, one per input.

**Schnorr check.** `checkSchnorrSignature tx spent nIn sig q tapscript ed` is `CheckSchnorrSignature`: 64 bytes (`SIGHASH_DEFAULT`) or 65 bytes whose last byte is a non-zero hash type, then BIP340 `schnorrVerify` of the signature mission over the BIP341 hash.

**Tapscript (BIP342).** `isOpSuccess` is `IsOpSuccess`; `opSuccessScan` is the pre-scan of `ExecuteWitnessScript` (a malformed push before any success opcode fails). `TapCtx` carries the interpreter flags, transaction, spent outputs and input index; `tapOracle` supplies the hash and locktime oracles of the Script mission (its `checkSig` is never consulted). `TapState` is the interpreter state plus the remaining validation weight, the code-separator position and the opcode position. `evalChecksigTapscript` is `EvalChecksigTapscript`: a non-empty signature costs 50 weight and fails on a negative budget, an empty key fails, a 32-byte key runs the Schnorr check, other key lengths succeed (upgradable). `tapExecOp` is one executed opcode under `TAPSCRIPT`: `MINIMALIF` on `OP_IF`/`OP_NOTIF`, `OP_CHECKSIG(VERIFY)` and `OP_CHECKSIGADD` via `evalChecksigTapscript`, `OP_CHECKMULTISIG(VERIFY)` fail, `OP_CODESEPARATOR` records the opcode position, everything else is the Script mission's `execOp`. `tapStep`/`tapRun` are the loop (no operation count, push-size and stack-size limits, conditional skipping, opcode position); `executeTapscript c ed stack script weight` is `ExecuteWitnessScript` under `TAPSCRIPT` (scan, initial limits, run, exactly one true element).

**The version-1 branch.** `hasAnnex` (two or more elements and a last element starting with 0x50), `witnessSerializedSize`; `taprootHandler spent : BitcoinVerify.TaprootHandler` is the version-1 branch of `VerifyWitnessProgram`: an empty witness fails; one element after the annex is the key path (Schnorr check of the output key, no tapleaf, code separator 0xFFFFFFFF); otherwise the control block and script are popped, the control size is checked, the leaf version is masked, the commitment verified, and leaf version 0xc0 runs Tapscript on the remaining elements with the weight budget $|\mathrm{ser}(\text{witness})| + 50$, other leaf versions succeed. `verifyScriptFull spent` is the complete `VerifyScript` with this handler; `p2trBytes q` = `OP_1 <q>`.

**Formalization Note.** Policy flags (`DISCOURAGE_UPGRADABLE_TAPROOT_VERSION`, `DISCOURAGE_UPGRADABLE_PUBKEYTYPE`, `DISCOURAGE_OP_SUCCESS`) are off, as in block validation. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinTaproot.tapbranch_comm": dict(title="ComputeTapbranchHash is symmetric",
    nl=r"""For all byte strings $a, b$: `tapbranchHash a b = tapbranchHash b a`. The branch hash sorts its two children lexicographically, so the merkle path does not encode left/right.""",
    ms=("lexicographical_compare — asymmetry and totality", "If `lexLt a b` then not `lexLt b a`; if neither, `a = b`.")),
"BitcoinTaproot.merkleRoot_base": dict(title="An empty path commits to the leaf",
    nl=r"""For a 33-byte control block (no path nodes), `taprootMerkleRoot control leaf = leaf`: the merkle root of a single-leaf tree is the leaf hash itself.""",
    ms=("ComputeTaprootMerkleRoot — the base case", "The node count is $(33-33)/32 = 0$.")),
"BitcoinTaproot.merkleRoot_snoc": dict(title="Appending a path node hashes the root with it",
    nl=r"""For a well-formed control block (length $33 + 32k$) and a 32-byte node: `taprootMerkleRoot (control ++ node) leaf = tapbranchHash (taprootMerkleRoot control leaf) node`. The merkle root is a left fold of the branch hash along the path.""",
    ms=("ComputeTaprootMerkleRoot — the step", "The chunking of `control ++ node` is the chunking of `control` followed by `node`.")),
"BitcoinTaproot.opsuccess_accepts": dict(title="OP_SUCCESSx makes the script succeed",
    nl=r"""If the `OP_SUCCESSx` pre-scan of a script returns `true`, `executeTapscript` returns `true` for every context, execution data, stack and weight: the script's body is never executed (BIP342).""",
    ms=("ExecuteWitnessScript — the success scan", "The scan result short-circuits the match.")),
"BitcoinTaproot.checkmultisig_rejected": dict(title="OP_CHECKMULTISIG is disabled in Tapscript",
    nl=r"""For every context, execution data, execution flag and state, `tapExecOp` on `OP_CHECKMULTISIG` and on `OP_CHECKMULTISIGVERIFY` is `none` (`SCRIPT_ERR_TAPSCRIPT_CHECKMULTISIG`).""",
    ms=("EvalScript TAPSCRIPT — CHECKMULTISIG", "By computation of the dispatch.")),
"BitcoinTaproot.minimalif_rejects": dict(title="MINIMALIF is consensus in Tapscript",
    nl=r"""An executed `OP_IF` whose top stack element is longer than one byte, or is one byte other than `0x01`, is a script error (`SCRIPT_ERR_TAPSCRIPT_MINIMALIF`).""",
    ms=("EvalScript TAPSCRIPT — MINIMALIF", "The minimal-if test precedes the generic `execOp`.")),
"BitcoinTaproot.sigops_budget": dict(title="The validation-weight budget",
    nl=r"""An executed `OP_CHECKSIG` with a non-empty signature when fewer than 50 weight units remain is a script error (`SCRIPT_ERR_TAPSCRIPT_VALIDATION_WEIGHT`), before any key or signature is examined.""",
    ms=("EvalChecksigTapscript — the budget", "The weight is decremented and tested first.")),
"BitcoinTaproot.checksig_empty": dict(title="An empty signature is a clean false",
    nl=r"""An executed `OP_CHECKSIG` with an empty signature and a 32-byte key pushes `false` (the empty vector), consumes no weight, and performs no signature check — the construction that makes `OP_CHECKSIGADD` thresholds work.""",
    ms=("EvalChecksigTapscript — empty signature", "`success = false`; the key-length branch is skipped.")),
"BitcoinTaproot.sighash_type_invalid": dict(title="Undefined hash types are rejected",
    nl=r"""For a hash type outside $\{0,1,2,3\} \cup \{0x81,0x82,0x83\}$, `sigHashSchnorr` is `none` (the signature check fails).""",
    ms=("SignatureHashSchnorr — hash type guard", "The first test of the function.")),
"BitcoinTaproot.sighash_single_missing": dict(title="SIGHASH_SINGLE without an output fails",
    nl=r"""For a valid hash type whose output type is `SIGHASH_SINGLE` and an input index with no corresponding output, `sigHashSchnorr` is `none`: unlike the legacy sighash there is no `uint256::ONE` quirk in BIP341.""",
    ms=("SignatureHashSchnorr — SINGLE", "The output-type computation and the length test.")),
"BitcoinTaproot.keypath_handler": dict(title="The key path is a Schnorr check of the output key",
    nl=r"""For a single-element witness `[sig]`, the Taproot handler equals `checkSchnorrSignature` of `sig` against the 32-byte program under the key-path execution data (no annex, no tapleaf, code separator 0xFFFFFFFF).""",
    ms=("VerifyWitnessProgram v1 — key path", "A one-element witness has no annex and `stack.length = 1`.")),
"BitcoinTaproot.keypath_annex": dict(title="The key path commits to the annex",
    nl=r"""For a witness `[sig, annex]` with a non-empty annex starting with `0x50`, the Taproot handler equals the Schnorr check with execution data recording the annex and its hash $\mathrm{SHA256}(\mathrm{compactSize}(|annex|)\,\|\,annex)$.""",
    ms=("VerifyWitnessProgram v1 — annex", "`hasAnnex` holds; the annex is popped and hashed.")),
"BitcoinTaproot.checkSchnorr_iff": dict(title="CheckSchnorrSignature characterized",
    nl=r"""`checkSchnorrSignature tx spent nIn sig q tapscript ed = true` iff there are a 64-byte body, a hash type $ht$ and a message $h$ with: `sig` is the body and $ht = 0$, or `sig` is the body followed by one byte equal to $ht \ne 0$; `sigHashSchnorr … ht … = some h`; and `schnorrVerify q h body = true`.""",
    ms=("CheckSchnorrSignature — both directions", "Case split on the signature length 64 / 65 / other.")),
"BitcoinTaproot.keypath_correct": dict(title="Taproot key-path spending is correct",
    nl=r"""For every list of spent outputs, context $c$ (flags, transaction, input index, amount), signature and 32-byte output key $q$:
$$\mathrm{taprootHandler}(spent, c, [sig], q) = \mathtt{true} \iff \exists\, body\ ht\ h.\ |body| = 64 \wedge \big((sig = body \wedge ht = 0) \vee (\exists b.\ sig = body \,\|\, [b] \wedge b = ht \ne 0)\big) \wedge \mathrm{sigHashSchnorr}(c.tx, spent, c.nIn, ht, \mathrm{tapscript}{=}\mathtt{false}, \langle \mathtt{false}, [], [], \mathtt{0xFFFFFFFF}\rangle) = \mathrm{some}\ h \wedge \mathrm{schnorrVerify}(q, h, body) = \mathtt{true}.$$
A key-path spend verifies exactly when the witness is a BIP340 signature by the output key of the BIP341 signature hash: 64 bytes under `SIGHASH_DEFAULT`, or 65 bytes under the non-zero hash type of the last byte.

**Formalization Note.** `taprootHandler` is the version-1 branch of `VerifyWitnessProgram` as plugged into the published `VerifyScript`; the equivalence holds for every flag set, transaction and amount. The script path is covered by `scriptpath_commitment`.""",
    ms=None),
"BitcoinTaproot.scriptpath_commitment": dict(title="A verifying script-path spend has a valid commitment",
    nl=r"""If a witness `stack ++ [script, control]` without an annex verifies under the Taproot handler, then `verifyTaprootCommitment control q leafHash = true`, where `leafHash` is the tapleaf hash of the revealed script under the control byte's masked leaf version: the merkle path from the leaf, tweaked into the internal key, yields the output key with the control byte's parity.""",
    ms=("VerifyWitnessProgram v1 — script path", "The commitment check guards both the Tapscript and the unknown-leaf branches.")),
}
ORDER = ["BitcoinTaproot.tapbranch_comm","BitcoinTaproot.merkleRoot_base","BitcoinTaproot.merkleRoot_snoc",
         "BitcoinTaproot.opsuccess_accepts","BitcoinTaproot.checkmultisig_rejected","BitcoinTaproot.minimalif_rejects",
         "BitcoinTaproot.sigops_budget","BitcoinTaproot.checksig_empty",
         "BitcoinTaproot.sighash_type_invalid","BitcoinTaproot.sighash_single_missing",
         "BitcoinTaproot.keypath_handler","BitcoinTaproot.keypath_annex","BitcoinTaproot.checkSchnorr_iff",
         "BitcoinTaproot.scriptpath_commitment","BitcoinTaproot.keypath_correct"]
