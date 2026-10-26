SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; "
       "CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; "
       "GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h")
TAGS = ["bitcoin", "consensus", "script", "interpreter", "cscriptnum", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinScript",
    "definition_title": "CScriptNum, CastToBool, and the legacy Script interpreter (EvalScript, VerifyScript)",
    "natural_language_statement": r"""A byte is an 8-bit word; a stack element is a list of bytes. Limits: element size $520$, $201$ operations, $20$ keys per multisig, $1000$ stack elements, $4$-byte numbers.

**Numbers.** $\mathrm{leNat}$ is the little-endian value of a byte list; $\mathrm{topBit}$ is bit 7 of the last byte; $\mathrm{clearTop}$ clears it; $\mathrm{setVch}(v)$ is `CScriptNum::set_vch`: $-\mathrm{leNat}(\mathrm{clearTop}\,v)$ when the top bit is set, else $\mathrm{leNat}(v)$, and $0$ for the empty list. $\mathrm{natBytes}(n)$ is the little-endian byte loop without trailing zeros; $\mathrm{setTop}$ sets bit 7 of the last byte; $\mathrm{serialize}(n)$ is `CScriptNum::serialize`: empty for $0$, else the magnitude bytes with a sign byte `0x80`/`0x00` appended when their top bit is already set, or the top bit set for a negative value otherwise. $\mathrm{nonMinimal}(v)$ is the constructor's rejection test (last byte has no value bits and the previous byte does not need it); $\mathrm{toNum}(\text{requireMinimal}, \text{maxSize}, v)$ is the constructor, `none` where it throws. $\mathrm{castToBool}$ is `CastToBool`; `vchTrue` $= [1]$, `vchFalse` $= [\,]$.

**Scripts.** An instruction is a data push or a non-push opcode byte; a script is a list of instructions, the output of `GetOp`. Opcode constants follow `script.h`; `isDisabled` lists the fifteen CVE-2010-5137 opcodes.

**Flags and oracle.** `Flags` holds `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY`, `NULLDUMMY`. An `Oracle` supplies `ripemd160`, `sha1`, `sha256`, `hash160`, `hash256`, `checkSig` (returning `none` where an encoding check fails the script, `some b` for the signature verdict), `checkLockTime` and `checkSequence`.

**Execution.** A `State` is the main stack, alt stack, condition stack and `nOpCount`, stacks top-first. `execOp`(flags, oracle, fExec, opcode, state) is the `switch` of `EvalScript` for one opcode: small-integer pushes, `NOP`s, `CHECKLOCKTIMEVERIFY`/`CHECKSEQUENCEVERIFY` (5-byte numbers, negative rejected, disable flag), `IF`/`NOTIF`/`ELSE`/`ENDIF`, `VERIFY`, `RETURN`, the stack family (`TOALTSTACK` … `TUCK`, `SIZE`), `EQUAL`/`EQUALVERIFY`, the unary and binary numeric family on 4-byte operands, `WITHIN`, the five hash opcodes, `CODESEPARATOR`, `CHECKSIG`/`CHECKSIGVERIFY`, `CHECKMULTISIG`/`CHECKMULTISIGVERIFY` with key-count accounting, the `NULLDUMMY` test and the extra popped element; anything else is a bad opcode. `step` is one loop iteration: element-size check and conditional push for a push; op count, disabled test, execute-or-skip and stack-size check for an opcode. `run` is the loop plus the final unbalanced-conditional check; `evalScript` returns the main stack; `verifyScriptPlain` is `VerifyScript` for a `scriptPubKey` that is neither P2SH nor a witness program. `p2pkhScript` and `p2pkScript` are the two templates; `opsIn` counts non-push instructions.

**Formalization Note.** `SigVersion::BASE` only; `fRequireMinimal` false; policy flags off; byte-level parsing, `MAX_SCRIPT_SIZE`, P2SH, witness programs and Tapscript are out of scope. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinScript.serialize_roundtrip": dict(title="CScriptNum serialization round-trips",
    nl=r"""For every integer $n$, $\mathrm{setVch}(\mathrm{serialize}(n)) = n$: reading back the bytes `CScriptNum::serialize` produces gives the original value, including $0$ (the empty encoding), negative values (sign bit or sign byte), and magnitudes whose top byte already has bit 7 set (sign byte appended).""",
    ms=("CScriptNum — round-trip", "Prove set_vch ∘ serialize = id over all integers, with the sign-byte and sign-bit cases.")),
"BitcoinScript.serialize_minimal": dict(title="The serializer always produces a minimal encoding",
    nl=r"""For every integer $n$, $\mathrm{nonMinimal}(\mathrm{serialize}(n)) = \mathtt{false}$: the output of `CScriptNum::serialize` never has a final byte without value bits that the previous byte could absorb. Consequently the interpreter's own numeric results always pass the `MINIMALDATA` test.""",
    ms=("CScriptNum — minimality of serialize", "Show serialize never emits a redundant final byte, using that the magnitude's top byte is nonzero.")),
"BitcoinScript.toNum_serialize": dict(title="A serialized number of at most four bytes is accepted strictly and reads back",
    nl=r"""For every integer $n$ whose serialization has at most four bytes, $\mathrm{toNum}(\mathtt{true}, 4, \mathrm{serialize}(n)) = \mathrm{some}\ n$: the strict (`fRequireMinimal`) four-byte constructor accepts the serializer's output and returns the original value.""",
    ms=("CScriptNum — strict constructor on serialized values", "Combine round-trip and minimality under the four-byte bound.")),
"BitcoinScript.castToBool_iff": dict(title="CastToBool is 'nonzero as a script number'",
    nl=r"""For every byte list $v$, $\mathrm{castToBool}(v) = \mathtt{true} \iff \mathrm{setVch}(v) \ne 0$. In particular both encodings of zero — all-zero bytes, and zero bytes followed by `0x80` (negative zero) — are false, and every other byte list is true, whatever its length.""",
    ms=("CastToBool — characterization", "Prove truth equals nonzero magnitude by induction on the byte list.")),
"BitcoinScript.eval_pushes": dict(title="A push-only script leaves exactly its pushes",
    nl=r"""For every flag setting and oracle and every list of elements $p_1, \dots, p_n$ each of at most $520$ bytes with $n \le 1000$, evaluating the script $\langle p_1\rangle \cdots \langle p_n\rangle$ from the empty stack succeeds with stack $[p_n, \dots, p_1]$ (top first). This is the evaluation of a standard `scriptSig`.""",
    ms=("EvalScript — push-only scripts", "Induction over the pushes with the element-size and stack-size checks discharged.")),
"BitcoinScript.disabled_fails": dict(title="A disabled opcode fails the script wherever it appears",
    nl=r"""For every flag setting, oracle, script, and state, if the script contains any of the fifteen disabled opcodes (`CAT`, `SUBSTR`, `LEFT`, `RIGHT`, `INVERT`, `AND`, `OR`, `XOR`, `2MUL`, `2DIV`, `MUL`, `DIV`, `MOD`, `LSHIFT`, `RSHIFT`), running it fails — even when the opcode sits in a branch that would not execute. This is the CVE-2010-5137 rule.""",
    ms=("EvalScript — disabled opcodes", "Show the disabled test fires before the execution test, from any state.")),
"BitcoinScript.execOp_opCount": dict(title="No opcode lowers the operation count",
    nl=r"""For every flag setting, oracle, execution flag, opcode $c$ and states $s, s'$ with $\mathrm{execOp}(c, s) = \mathrm{some}\ s'$: $s.\mathrm{opCount} \le s'.\mathrm{opCount}$, and either the count is unchanged or (for `CHECKMULTISIG`, which adds its key count) it is at most $201$. A case analysis over the whole opcode table.""",
    ms=("execOp — nOpCount monotone", "Case split along the opcode chain; the only increase is CHECKMULTISIG's, bounded by its own check.")),
"BitcoinScript.op_count_fails": dict(title="More than 201 operations never succeed",
    nl=r"""For every flag setting, oracle, starting stack and script with more than $201$ non-push instructions, $\mathrm{evalScript}$ returns `none`. Each executed or skipped non-push instruction raises `nOpCount` by at least one and the limit is checked before every one of them.""",
    ms=("EvalScript — MAX_OPS_PER_SCRIPT", "Thread the count invariant through the loop; the 202nd operation is rejected.")),
"BitcoinScript.p2pk_correct": dict(title="Pay-to-public-key is correct",
    nl=r"""For every flag setting and oracle, signature $sig$ and key $pk$ of at most $520$ bytes,
$$\mathrm{verifyScriptPlain}\big([\langle sig\rangle],\ \langle pk\rangle\ \mathtt{CHECKSIG}\big) = \mathtt{true} \iff \mathrm{checkSig}(sig, pk) = \mathrm{some}\ \mathtt{true}.$$""",
    ms=("VerifyScript — P2PK template", "Compute the two evaluations and read off the oracle's verdict.")),
"BitcoinScript.p2pkh_correct": dict(title="Pay-to-public-key-hash is correct",
    nl=r"""For every flag setting and oracle, signature $sig$, public key $pk$ and hash $h$ each of at most $520$ bytes,
$$\mathrm{verifyScriptPlain}\big([\langle sig\rangle, \langle pk\rangle],\ \mathtt{DUP\ HASH160}\ \langle h\rangle\ \mathtt{EQUALVERIFY\ CHECKSIG}\big) = \mathtt{true} \iff \mathrm{hash160}(pk) = h \;\wedge\; \mathrm{checkSig}(sig, pk) = \mathrm{some}\ \mathtt{true}.$$
Here `verifyScriptPlain` evaluates the `scriptSig` and then the `scriptPubKey` on the same stack with the transcribed `EvalScript` — element-size, operation-count and stack-size checks included — and requires a true top; `hash160` and `checkSig` are the oracle's. The template that carries most of Bitcoin's history therefore enforces exactly "the key hashes to $h$ and the signature verifies", in both directions, for every oracle.

**Formalization Note.** The 520-byte bounds are the `MAX_SCRIPT_ELEMENT_SIZE` push checks; no assumption is made on the oracle, on the flags, or on the length of $h$ beyond the push limit.""",
    ms=None),
}
ORDER = ["BitcoinScript.serialize_roundtrip","BitcoinScript.serialize_minimal","BitcoinScript.toNum_serialize",
         "BitcoinScript.castToBool_iff","BitcoinScript.eval_pushes","BitcoinScript.disabled_fails",
         "BitcoinScript.execOp_opCount","BitcoinScript.op_count_fails","BitcoinScript.p2pk_correct","BitcoinScript.p2pkh_correct"]
