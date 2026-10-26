SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, VerifyWitnessProgram, ExecuteWitnessScript, src/script/interpreter.cpp: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; "
       "CScript::IsPayToScriptHash, IsWitnessProgram, IsPushOnly, IsPayToAnchor, DecodeOP_N, src/script/script.cpp and script.h; "
       "MAX_SCRIPT_SIZE, WITNESS_V0_SCRIPTHASH_SIZE, WITNESS_V0_KEYHASH_SIZE, WITNESS_V1_TAPROOT_SIZE; BIP16, BIP141, BIP143 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7")
TAGS = ["bitcoin", "consensus", "segwit", "p2sh", "verifyscript", "bip141", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinVerify",
    "definition_title": "VerifyScript: P2SH, native and wrapped SegWit v0, unknown witness versions, and the taproot hand-off",
    "natural_language_statement": r"""**Context and flags.** A `Ctx` is the spending transaction, the input index, the amount spent and the consensus flag set (`BitcoinActivation.ScriptFlags`, the output of `GetBlockScriptFlags`); `scriptFlagsOf` and `sigFlagsOf` project the interpreter and signature-layer flags (`DERSIG` is the only signature flag on mainnet). $\mathrm{MAX\_SCRIPT\_SIZE} = 10{,}000$.

**Byte-level evaluation.** `evalBytes ctx v stack script` is `EvalScript` on a byte string: the size test, the `GetOp` parse (`none` on a malformed push), and the Script mission's interpreter with the concrete oracle of the signature mission for signature version `v` and this script code.

**Predicates.** `isPayToScriptHash` is `CScript::IsPayToScriptHash` (23 bytes `a9 14 … 87`); `isWitnessProgram` is `IsWitnessProgram` (`OP_0`/`OP_1..16` then one push of 2–40 bytes, nothing else; returns the version and program); `isPushOnly` is `IsPushOnly` (every instruction parses and has opcode at most `OP_16`); `isPayToAnchor` is the version-1 two-byte `4e73` program; `topTrue` is `CastToBool` of the top, false on an empty stack.

**Witness execution.** `executeWitnessScriptV0` is `ExecuteWitnessScript` for version 0: every element within 520 bytes, the script run under `WITNESS_V0`, exactly one element left and it true. `verifyWitnessProgram` is `VerifyWitnessProgram`: version 0 with a 32-byte program is P2WSH (last witness element is the script, its SHA-256 must equal the program, the rest is the initial stack), with a 20-byte program is P2WPKH (exactly two elements, the implied `DUP HASH160 <program> EQUALVERIFY CHECKSIG`), other lengths fail; version 1 with a 32-byte program outside P2SH is Taproot, delegated to the `TaprootHandler` parameter when the `TAPROOT` flag is set and accepted otherwise; pay-to-anchor and every other version/size combination succeed. Witness stacks are in `CScriptWitness` order (last element on top), reversed into the interpreter's top-first stacks.

**`verifyScript`** is `VerifyScript` with the consensus flags: the scriptSig and then the output script on the same stack, a true top; with `WITNESS`, a witness-program output requires an empty scriptSig and runs the program; with `P2SH`, a P2SH output requires a push-only scriptSig, restores the scriptSig's stack, pops the serialized redeem script and runs it, requires a true top, and, with `WITNESS`, a witness-program redeem script requires the scriptSig to be exactly its single push and runs the program as P2SH-wrapped; finally, with `WITNESS`, a non-empty witness that nothing consumed fails. `SIGPUSHONLY` and `CLEANSTACK` are policy and off.

**Templates.** `p2shBytes h`, `witnessBytes v program`, `pushesBytes` (a push-only scriptSig), `p2wpkhExec`.

**Formalization Note.** Policy flags are off; the Taproot branch is a parameter supplied by the Taproot development; the oracle's script code is the executed script, exact for scripts without `OP_CODESEPARATOR`. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinVerify.isPayToScriptHash_iff": dict(title="IsPayToScriptHash characterized",
    nl=r"""A byte string satisfies `IsPayToScriptHash` iff it is `OP_HASH160 <h> OP_EQUAL` for some 20-byte $h$.""",
    ms=("IsPayToScriptHash — characterization", "Both directions from the three byte tests and the length.")),
"BitcoinVerify.isWitnessProgram_iff": dict(title="IsWitnessProgram characterized",
    nl=r"""`isWitnessProgram s = some (v, program)` iff $v \le 16$, $2 \le |program| \le 40$ and $s$ is `OP_v <program>` (a single direct push), i.e. `witnessBytes v program`.""",
    ms=("IsWitnessProgram — characterization", "Decode the version byte and the single push in both directions.")),
"BitcoinVerify.parseScript_pushes": dict(title="A push-only scriptSig parses to its pushes",
    nl=r"""For elements each within 520 bytes, `parseScript (pushesBytes ps) = some (ps.map push)`: the canonical pushes (direct, `PUSHDATA1`, `PUSHDATA2`) parse back to the pushed elements.""",
    ms=("GetScriptOp — canonical pushes", "Case split on the three push encodings.")),
"BitcoinVerify.isPushOnly_pushes": dict(title="A push-only scriptSig satisfies IsPushOnly",
    nl=r"""For elements each within 520 bytes, `isPushOnly (pushesBytes ps) = true`.""",
    ms=("IsPushOnly — canonical pushes", "Induction over the elements.")),
"BitcoinVerify.native_witness_malleated": dict(title="A witness-program output needs an empty scriptSig",
    nl=r"""With the `WITNESS` flag, if the output script is a witness program and the scriptSig is non-empty, `verifyScript` is `false` whatever the witness (`SCRIPT_ERR_WITNESS_MALLEATED`).""",
    ms=("VerifyScript — witness malleation", "The scriptSig test precedes the program verification.")),
"BitcoinVerify.witness_unexpected": dict(title="An unconsumed witness fails",
    nl=r"""With the `WITNESS` flag, if the output is neither a witness program nor P2SH and the witness is non-empty, `verifyScript` is `false` (`SCRIPT_ERR_WITNESS_UNEXPECTED`).""",
    ms=("VerifyScript — unexpected witness", "The final hadWitness test.")),
"BitcoinVerify.unknown_witness_version": dict(title="Unknown witness versions are accepted",
    nl=r"""With the `WITNESS` flag, an output `OP_v <program>` with $2 \le v \le 16$, or $v = 1$ with a program that is not 32 bytes (including pay-to-anchor), spent with an empty scriptSig and any witness, verifies exactly when the program is true as a script value. This is the future-soft-fork compatibility rule: such outputs are anyone-can-spend, except that an all-zero program fails the base evaluation.""",
    ms=("VerifyWitnessProgram — unknown versions", "Evaluate OP_v <program> on the empty stack and the fall-through branches.")),
"BitcoinVerify.p2wsh_correct": dict(title="Native P2WSH characterized",
    nl=r"""With the `WITNESS` flag, the output `OP_0 <SHA256(script)>` spent with an empty scriptSig and witness `ws ++ [script]` verifies iff the program is true as a script value and the witness script, run under witness v0 on the stack of the remaining elements (last on top), leaves exactly one true element.""",
    ms=("VerifyWitnessProgram — P2WSH", "The last element is the script; its hash is the program by construction.")),
"BitcoinVerify.p2sh_correct": dict(title="P2SH is correct",
    nl=r"""With the `P2SH` flag, the output `OP_HASH160 <h> OP_EQUAL` spent with the push-only scriptSig $\langle a_1\rangle \cdots \langle a_k\rangle \langle redeem\rangle$ and no witness, where $redeem$ is not a witness program, verifies iff $\mathrm{Hash160}(redeem) = h$ and $redeem$, run on the stack $[a_k, \dots, a_1]$, leaves a true top. The side conditions are the push and stack limits (elements within 520 bytes, at most 1000 elements, scriptSig within 10,000 bytes).""",
    ms=("VerifyScript — P2SH", "Push-only evaluation, the hash test, the restored stack and the redeem evaluation.")),
"BitcoinVerify.p2sh_p2wpkh_correct": dict(title="P2SH-wrapped P2WPKH is correct",
    nl=r"""With both flags, the output `OP_HASH160 <Hash160(OP_0 <h>)> OP_EQUAL` spent with scriptSig `<OP_0 <h>>` and witness `[sig, pk]` verifies iff $h$ is true as a script value, $\mathrm{Hash160}(pk) = h$ and the BIP143 signature check on the implied P2PKH script accepts.""",
    ms=("VerifyScript — P2SH-P2WPKH", "The P2SH path, the single-push test, then the wrapped program.")),
"BitcoinVerify.p2wpkh_correct": dict(title="Native P2WPKH is correct",
    nl=r"""With the `WITNESS` flag, for a 20-byte $h$ and signature and key within 520 bytes:
$$\mathrm{verifyScript}\big([\,],\ \mathtt{OP\_0}\ \langle h\rangle,\ [sig, pk]\big) = \mathtt{true} \iff \mathrm{castToBool}(h) \wedge \mathrm{Hash160}(pk) = h \wedge \mathrm{checkSigPreTapscript}_{\mathrm{WITNESS\_V0}}(\text{p2pkhBytes}(h), sig, pk) = \mathrm{some}\ \mathtt{true},$$
where the signature check is the signature mission's checker under witness v0 (BIP143 sighash, `DERSIG` from the flags) on the implied script `DUP HASH160 <h> EQUALVERIFY CHECKSIG`. The first conjunct records that an all-zero key hash is unspendable: the base evaluation of `OP_0 <h>` leaves $h$ on top and requires it true.

**Formalization Note.** `verifyScript` is the full `VerifyScript` control flow with the consensus flags; the equivalence holds for every flag set with `WITNESS` on, every transaction and amount, and every Taproot handler.""",
    ms=None),
}
ORDER = ["BitcoinVerify.isPayToScriptHash_iff","BitcoinVerify.isWitnessProgram_iff","BitcoinVerify.parseScript_pushes","BitcoinVerify.isPushOnly_pushes",
         "BitcoinVerify.native_witness_malleated","BitcoinVerify.witness_unexpected","BitcoinVerify.unknown_witness_version","BitcoinVerify.p2wsh_correct",
         "BitcoinVerify.p2sh_correct","BitcoinVerify.p2sh_p2wpkh_correct","BitcoinVerify.p2wpkh_correct"]
