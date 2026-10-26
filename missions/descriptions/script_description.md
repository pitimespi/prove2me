## Why the script interpreter is the heart of consensus

Every Bitcoin transaction input is authorized by running a small stack program: the input's `scriptSig` followed by the spent output's `scriptPubKey`, on the same stack, and the spend is valid when the program leaves a true value on top. Nearly every historical consensus failure in Bitcoin touched this interpreter — the disabled opcodes (CVE-2010-5137), the concatenation bug that let any output be spent (CVE-2010-5141), the overflow in numeric opcodes that prompted the four-byte limit, the `CHECKMULTISIG` off-by-one that consumes an extra element. Bitcoin Core's `EvalScript` is 800 lines of C++ with a `switch` over a hundred opcodes, and `VerifyScript` wraps it with the pay-to-script-hash and witness-program rules. ([`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp), [`script.h`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h))

This mission transcribes the legacy execution path (`SigVersion::BASE`) — the number representation `CScriptNum`, the truth test `CastToBool`, the full non-push opcode table of `EvalScript` with its resource limits, and `VerifyScript` for output scripts that are neither pay-to-script-hash nor witness programs — and proves the properties the rest of validation relies on: that script numbers round-trip and are minimal, that truth is "nonzero as a number", that the resource limits and the disabled-opcode rule behave as stated, and that the two classic payment templates do exactly what they are meant to.

## Numbers, truth, and the machine

A **byte** is an 8-bit word and a stack element is a list of bytes. A **script number** is a little-endian magnitude whose last byte's top bit is the sign: $\mathrm{setVch}(v)$ reads it, $\mathrm{serialize}(n)$ writes the shortest such encoding (appending a sign byte when the magnitude's top bit is already set), and the `CScriptNum` constructor rejects encodings longer than four bytes (five for the lock-time opcodes) and, under `MINIMALDATA`, non-minimal ones. $\mathrm{castToBool}(v)$ is true when some byte is nonzero, except that a negative zero (`0x80` after zero bytes) is false.

A **script** is the sequence of instructions `GetOp` yields: a data push carrying its bytes, or a non-push opcode. The interpreter's **state** is the main stack, the alt stack, the condition stack `vfExec`, and `nOpCount`; stacks are lists with the top first. One **step** on a push checks the 520-byte element limit and pushes when all conditions are true; on an opcode it counts it against the 201-operation limit, rejects the fifteen disabled opcodes regardless of execution state, and when executing (or for `IF`/`NOTIF`/`ELSE`/`ENDIF` always) runs the opcode's case — pushes of small integers, flow control, the stack-manipulation family, `EQUAL`, the numeric family on four-byte operands, `WITHIN`, the hash opcodes, `CODESEPARATOR`, `CHECKSIG`, `CHECKMULTISIG` with its key-count accounting, the `NOP`s, and `CHECKLOCKTIMEVERIFY`/`CHECKSEQUENCEVERIFY` when their flags are set — then checks the 1000-element stack limit. Hashes, the lock-time checks, and the signature check (with its encoding rules and `FindAndDelete`) are an abstract **oracle**, exactly the role of `BaseSignatureChecker` and the hash primitives in the source. **Running** a script steps through it and fails on an unbalanced conditional; **verifying** evaluates `scriptSig` then `scriptPubKey` and requires a non-empty stack with a true top.

## Formalization targets

### Goal — pay-to-public-key-hash does what it says
$$
\mathrm{verifyScriptPlain}\big([\langle sig\rangle, \langle pk\rangle],\ \mathtt{DUP\ HASH160}\ \langle h\rangle\ \mathtt{EQUALVERIFY\ CHECKSIG}\big) = \mathtt{true}
\iff \mathrm{hash160}(pk) = h \;\wedge\; \mathrm{checkSig}(sig, pk) = \mathrm{some}\ \mathtt{true},
$$
for all signatures, keys and hashes within the 520-byte element limit, every flag setting and every oracle. This is `BitcoinScript.p2pkh_correct`: the template that carries most of Bitcoin's history is correct against the transcribed interpreter, in both directions, with the signature check and hash left abstract. It is the weakest stable statement, since it fixes nothing about the oracle.

### Supporting milestones
1. **Round-trip** (`serialize_roundtrip`): $\mathrm{setVch}(\mathrm{serialize}(n)) = n$ for every integer.
2. **Minimality** (`serialize_minimal`): the serializer's output always passes the minimal-encoding test; (`toNum_serialize`): a serialized number of at most four bytes is accepted by the strict constructor and reads back as itself.
3. **Truth is nonzero** (`castToBool_iff`): $\mathrm{castToBool}(v) \iff \mathrm{setVch}(v) \ne 0$, for every byte string, including both encodings of zero.
4. **Pushes** (`eval_pushes`): a push-only script within the element and stack limits leaves exactly its pushes, top-first.
5. **Disabled opcodes** (`disabled_fails`): a script containing any of the fifteen disabled opcodes fails from every state, executed or not.
6. **Operation limit** (`op_count_fails`): a script with more than 201 non-push instructions never succeeds.
7. **Pay-to-public-key** (`p2pk_correct`): $\langle sig\rangle$ against $\langle pk\rangle\ \mathtt{CHECKSIG}$ succeeds iff the oracle accepts the signature.

## What the result establishes

The goal and milestones give kernel-checked semantics for the pieces of the legacy interpreter that every later layer consumes. The number theorems fix what `CScriptNum` means on the wire and show the interpreter's own outputs are always minimal — which is why `MINIMALDATA` can be a policy rule. The truth theorem is what makes `VERIFY`, `IF` and the final check well-defined on arbitrary byte strings. The limit and disabled-opcode theorems are the denial-of-service and CVE-2010-5137 defences, stated as universal properties of the transcription rather than of test cases. And the template theorems are the first end-to-end statements that a real Bitcoin spending condition is enforced by the code, modulo the cryptography.

What is deliberately abstract: hash functions, the signature check with its DER/strict-encoding rules and `FindAndDelete`, and the lock-time checks. These are oracle fields, so every theorem holds for every oracle; instantiating them is the work of the hash, sighash and signature layers. Not modeled: byte-level script parsing (`GetOp`, `MAX_SCRIPT_SIZE`), pay-to-script-hash and witness programs in `VerifyScript`, SegWit v0 and Tapscript execution, and the policy flags (`MINIMALDATA`, `NULLFAIL`, `CONST_SCRIPTCODE`, `DISCOURAGE_UPGRADABLE_NOPS`, `MINIMALIF`), which are fixed to off as in block validation.

Status: all statements are open with intentional placeholder proofs. The opcode table has been checked by evaluation against the source's documented stack effects (`x1 x2 x3 -- x2 x3 x1` and the like) and the CVE-2010-5137 and limit behaviours; nothing about compiled Bitcoin Core is claimed.

## Where the obvious argument fails

The number round-trip looks like bookkeeping until the sign byte: when the magnitude's top byte already has bit 7 set, the serializer appends a whole byte for the sign, and the reader must then see a cleared top bit on that extra byte while the magnitude is unchanged. The proof splits on this case and on the sign, and needs the precise effect of `|= 0x80` and `& 0x7f` on bytes below 128. Minimality has the matching trap: the serializer never emits a trailing zero magnitude byte, which is what makes its output pass the test.

For the templates, the naive approach is to compute. It works, but only after the interpreter's resource checks are discharged on every step — the element size on each push, the op count on each opcode, the stack size after each step — which is why the template theorems carry element-size hypotheses and why the push lemma is stated with its limits. For the op-count theorem the trap is `CHECKMULTISIG`, which adds its key count to `nOpCount` mid-execution; the invariant has to allow that increase while keeping it under the limit.

## Formalization scope

Bytes are `BitVec 8`; numbers are `Int` with `natAbs` for the magnitude; bit tests are the source's masks (`& 0x80`, `& 0x7f`, `| 0x80`) read through `toNat`. Stacks are `List`s, top first; the `stacktop(-k)` indexing of the source becomes position $k-1$. Scripts are `List Instr`. `execOp` is one `if`-chain mirroring the `switch`; `step` performs the per-iteration checks in the source's order; `run` is the loop plus the final conditional check; `evalScript` returns the main stack. `Flags` carries `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY` and `NULLDUMMY`; `fRequireMinimal` is false. The oracle's `checkSig` returns `none` where an encoding check fails the whole script and `some b` for the signature verdict.

A trivializing formalization would define `verifyScriptPlain` on the two templates directly, or let the oracle see the script; the interpreter is the full opcode table and the oracle sees only the stack elements it is handed. Restricting the templates to canonical sizes beyond the 520-byte limit is out of scope.

No Mathlib is required; the development imports only `Std`. Proofs in any order are welcome; lemmas about individual opcodes' stack effects are reusable for every later script theorem.

## Selected references

- Bitcoin Core contributors. *`EvalScript`, `VerifyScript`, `CastToBool`, `EvalChecksigPreTapscript`*, `src/script/interpreter.cpp` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp)
- Bitcoin Core contributors. *`CScriptNum`, opcode table, `MAX_SCRIPT_ELEMENT_SIZE`, `MAX_OPS_PER_SCRIPT`, `MAX_STACK_SIZE`, `MAX_PUBKEYS_PER_MULTISIG`*, `src/script/script.h`, and *`GetScriptOp`*, `src/script/script.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h)
- Pieter Wuille. *BIP62: Dealing with malleability* (rules 3–6, minimal data and numbers), 2014. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0062.mediawiki)
- Satoshi Nakamoto. *Bitcoin: A Peer-to-Peer Electronic Cash System*, 2008, section 2. [Paper](https://bitcoin.org/bitcoin.pdf)
