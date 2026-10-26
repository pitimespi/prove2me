# Read-back: `Def_BitcoinVerify`

**Scope and notation.** This file lives in a namespace `BitcoinVerify` and depends on four earlier files: `BitcoinSer` (byte strings, transactions, SHA-256, RIPEMD-160, `hash160`), `BitcoinScript` (the stack interpreter `evalScript`, its `Flags`, its `Oracle`, `castToBool`, the constants `MAX_SCRIPT_ELEMENT_SIZE = 520`, `MAX_STACK_SIZE = 1000`, `OP_16 = 0x60`), `BitcoinSig` (the byte-level parser `getOp`/`parseScript`, the canonical push encoder `pushBytes`, the signature flags `SigFlags`, the two signature versions `base`/`witnessV0`, the concrete `legacyOracle`, and `p2pkhBytes`), and `BitcoinActivation` (the seven-field consensus flag record `ScriptFlags` with Boolean fields `p2sh, witness, taproot, dersig, cltv, csv, nulldummy`). Throughout, a *byte* is an 8-bit bit-vector, a *byte string* (`Bytes`) is a finite list of bytes, and a *stack* is a finite list of byte strings. Every stack handed to the interpreter is **top-first**: the head of the list is the top of the stack. Nothing in this file is a theorem; every declaration is a computable definition. The declarations are described below in file order.

**`MAX_SCRIPT_SIZE`, `WITNESS_V0_SCRIPTHASH_SIZE`, `WITNESS_V0_KEYHASH_SIZE`, `WITNESS_V1_TAPROOT_SIZE`.** Four natural-number constants: $10000$, $32$, $20$, $32$ respectively.

**`scriptFlagsOf`.** Given a consensus flag record $f$, produces the interpreter's three-field flag record $\langle f.\mathrm{cltv},\ f.\mathrm{csv},\ f.\mathrm{nulldummy}\rangle$. The fields `p2sh`, `witness`, `taproot`, `dersig` of $f$ are not forwarded to the interpreter.

**`sigFlagsOf`.** Given a consensus flag record $f$, produces the signature layer's four-field record $\langle \mathrm{dersig} = f.\mathrm{dersig},\ \mathrm{lowS} = \mathrm{false},\ \mathrm{strictenc} = \mathrm{false},\ \mathrm{witnessPubkeyType} = \mathrm{false}\rangle$. Only `dersig` is carried over; the other three are hard-wired to false.

**`Ctx`.** A record of four fields: `flags` (a consensus flag record), `tx` (a transaction: version, inputs, outputs, lock time), `nIn` (a natural number, the input index), and `amount` (an integer; the docstring says $-1$ is used where the amount is unknown). Nothing constrains `nIn` to be a valid index of `tx`, and nothing constrains `amount` to be non-negative.

**`evalBytes`.** Takes a context $c$, a signature version $v \in \{\mathrm{base}, \mathrm{witnessV0}\}$, a top-first stack, and a byte string `script`; returns either "failure" (`none`) or a resulting top-first stack. It proceeds:
1. If $10000 < |\mathrm{script}|$ (strictly), failure. A script of exactly $10000$ bytes is allowed.
2. Otherwise parse `script` byte-wise with `BitcoinSig.parseScript`; if parsing fails (a truncated push), failure.
3. Otherwise run the interpreter `BitcoinScript.evalScript` with flags `scriptFlagsOf c.flags`, with the oracle `BitcoinSig.legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount v script`, on the given stack and the parsed instruction list; the interpreter's own failure or success is the result.

Unfolding the oracle: its hash functions are the concrete SHA-256/RIPEMD-160/SHA-1/`hash160`/`hash256`; its signature check on $(\mathrm{sig}, \mathrm{pk})$ is `checkSigPreTapscript (sigFlagsOf c.flags) c.tx c.nIn c.amount v script sig pk`, in which the *script code* is the **entire byte string `script` being executed** (with the push of `sig` removed by `findAndDelete` when $v = \mathrm{base}$, and unchanged when $v = \mathrm{witnessV0}$); its lock-time and sequence checks are those of `c.tx` at input `c.nIn`. There is no handling of `OP_CODESEPARATOR` at this level (the interpreter treats that opcode as a no-op), so the script code is always the whole script.

**`isPayToScriptHash`.** For a byte string $s$: true exactly when $|s| = 23$ and $s_0 = \mathtt{0xa9}$ and $s_1 = \mathtt{0x14}$ and $s_{22} = \mathtt{0x87}$. (Out-of-range indices read as $0$, but with $|s| = 23$ all three indices are in range.) The 20 bytes $s_2 \ldots s_{21}$ are unconstrained.

**`decodeOpN`.** On a natural number $b$: $0$ if $b = 0$, else $b - \mathtt{0x50}$ with truncated natural subtraction (so any $0 < b < \mathtt{0x50}$ yields $0$ as well). It is only ever applied, below, to $b = 0$ or $b \in [\mathtt{0x51}, \mathtt{0x60}]$.

**`isWitnessProgram`.** For a byte string $s$, returns either nothing or a pair (version, program):
1. If $|s| < 4$ or $42 < |s|$: nothing. So $4 \le |s| \le 42$ is required.
2. Let $b_0 = s_0$. If $b_0 \ne 0$ and ($b_0 < \mathtt{0x51}$ or $\mathtt{0x60} < b_0$): nothing. So $b_0 \in \{0\} \cup [\mathtt{0x51}, \mathtt{0x60}]$; in particular $\mathtt{0x50}$ (`OP_RESERVED`) and all push opcodes other than $0$ are rejected.
3. If $s_1 + 2 = |s|$: the pair $(\mathrm{decodeOpN}\ b_0,\ s \text{ with its first two bytes dropped})$. Otherwise nothing.
Given the length bound, $s_1 \in [2, 40]$ and the returned program has exactly $s_1$ bytes. The version is $0$ for $b_0 = 0$ and $b_0 - \mathtt{0x50} \in [1, 16]$ otherwise.

**`isPushOnlyAux`, `isPushOnly`.** `isPushOnlyAux` takes a fuel counter and a byte string: an empty string is push-only (true); with zero fuel and a non-empty string, false; otherwise it parses one instruction with `getOp`: a parse failure gives false; a push instruction recurses on the remainder with one less fuel; a non-push opcode $c$ gives false if $\mathtt{0x60} < c$, else recurses. `isPushOnly s` calls this with fuel $|s|$. Since `getOp` always consumes at least one byte, fuel $|s|$ suffices to reach the end; the result is: every instruction parses and is either a data push (any of `OP_0`, direct pushes, `OP_PUSHDATA1/2/4`) or an opcode byte in $[\mathtt{0x4f}, \mathtt{0x60}]$ (`OP_1NEGATE`, `OP_RESERVED`, `OP_1`…`OP_16`). Push sizes are not bounded here.

**`isPayToAnchor`.** For a natural number `version` and a byte string `program`: true exactly when version $= 1$ and program is the two-byte string $[\mathtt{0x4e}, \mathtt{0x73}]$.

**`topTrue`.** For a top-first stack: false if the stack is empty; otherwise `castToBool` of the top element. `castToBool` of a byte string is: false for the empty string; for a string, true iff some byte is nonzero, except that a string whose only nonzero byte is a final $\mathtt{0x80}$ (negative zero) is false.

**`executeWitnessScriptV0`.** Takes a context $c$, a top-first stack and a byte string `exec`; returns a Boolean:
1. If some element of the stack has length strictly greater than $520$: false. (The size check is on the stack elements only; `exec` itself is not checked here.)
2. Otherwise run `evalBytes c witnessV0 stack exec`. Failure gives false.
3. Otherwise, with resulting stack $st$: true iff $|st| = 1$ (exactly one element) and `topTrue st`.

**`p2wpkhExec`.** For a byte string `program`: `BitcoinSig.p2pkhBytes program`, i.e. the byte string $\mathtt{0x76}\ \mathtt{0xa9}\ \|\ \mathrm{pushBytes}(\mathrm{program})\ \|\ \mathtt{0x88}\ \mathtt{0xac}$ (`OP_DUP OP_HASH160 <push> OP_EQUALVERIFY OP_CHECKSIG`). For a 20-byte program the push is $\mathtt{0x14}$ followed by the 20 bytes, so the script has 26 bytes.

**`TaprootHandler`.** A type abbreviation: a function from (context, list of byte strings, byte string) to Boolean. Per the docstring, the list is the witness stack in serialized order (last element on top) and the byte string is the 32-byte program. The file places no constraint whatsoever on such a function.

**`verifyWitnessProgram`.** Takes a handler `tap`, a context $c$, a witness stack `witness` (a list of byte strings in *serialized* order, i.e. **last element of the list is the top**, the opposite convention from the interpreter's stacks), a natural number `version`, a byte string `program`, and a Boolean `isP2sh`. Control flow, in order:

- **Case version $= 0$.**
  - If $|\mathrm{program}| = 32$ (P2WSH): take the **last** element of `witness` (`getLast?`). If `witness` is empty: **false**. Otherwise call it `script`; if $\mathrm{sha256}(\mathrm{script}) \ne \mathrm{program}$: **false**; else the result is `executeWitnessScriptV0 c (witness.dropLast.reverse) script` — the witness with its last element removed and then **reversed**, so the second-to-last serialized element becomes the interpreter's top. Note `script` is exempt from the 520-byte element check inside `executeWitnessScriptV0`, since it has been removed from the stack.
  - Else if $|\mathrm{program}| = 20$ (P2WPKH): if $|\mathrm{witness}| \ne 2$: **false**; else the result is `executeWitnessScriptV0 c witness.reverse (p2wpkhExec program)`, i.e. the two-element witness is reversed (its second serialized element becomes the top) and run against `OP_DUP OP_HASH160 <program> OP_EQUALVERIFY OP_CHECKSIG` under signature version `witnessV0`.
  - Else (version 0 with any other program length): **false**.
- **Case version $= 1$ and $|\mathrm{program}| = 32$ and `isP2sh` is false** (Taproot): if `c.flags.taproot` is false: **true** unconditionally (the witness is not inspected at all, even if empty); else the result is `tap c witness program` — the handler receives the witness in serialized (unreversed) order.
- **Otherwise**: if `isP2sh` is false and `isPayToAnchor version program`: **true**; else: **true**. Both arms yield true, so every remaining case — unknown versions $2$…$16$ (and any other natural number), version $1$ with a program length other than $32$, version $1$ with a 32-byte program under P2SH, and pay-to-anchor — succeeds regardless of the witness. The `isPayToAnchor` test has no effect on the result.

The `taproot` flag is the only flag consulted here; the `witness` flag is not (it gates the callers). The `isP2sh` argument matters only to exclude the Taproot branch.

**`verifyScript`.** Takes a handler `tap`, a context $c$, byte strings `scriptSig` and `scriptPubKey`, and a witness stack `witness` (serialized order). Control flow, in order:

1. Evaluate `scriptSig` with `evalBytes c base []` on the empty stack. Failure: **false**. Call the resulting top-first stack `stackSig`.
2. Evaluate `scriptPubKey` with `evalBytes c base stackSig` (same stack carried over, same signature version `base`). Failure: **false**. Call the result `stack`.
3. If `topTrue stack` is false (empty, or top casts to false): **false**.
4. Compute `native`, an optional Boolean: if `c.flags.witness` is true and `isWitnessProgram scriptPubKey` yields $(\mathrm{version}, \mathrm{program})$: if `scriptSig` is non-empty then `some false`, else `some (verifyWitnessProgram tap c witness version program false)`. If the `witness` flag is false, or `scriptPubKey` is not a witness program: `none`.
5. If `native` is `some false`: **false**. If `some true`: **true** (the function returns here; the P2SH and the "unexpected witness" checks below are never reached for a native witness program).
6. If `native` is `none`, and `c.flags.p2sh` is true and `isPayToScriptHash scriptPubKey`:
   - If `scriptSig` is not push-only (`isPushOnly`): **false**.
   - Restore the stack **`stackSig`** — the stack as it stood after step 1, *before* `scriptPubKey` ran. If it is empty: **false**. Otherwise its top element is `redeem` and the remainder is `rest`.
   - Evaluate `redeem` as a script: `evalBytes c base rest redeem`, signature version `base`, on the stack `rest` (with the redeem script popped). Failure: **false**. Call the result `stack2`.
   - If `topTrue stack2` is false: **false**.
   - If `c.flags.witness` is true: if `isWitnessProgram redeem` yields $(\mathrm{version}, \mathrm{program})$: if `scriptSig` is not byte-for-byte equal to `pushBytes redeem` (the single canonical push of the redeem script): **false**; else the result is `verifyWitnessProgram tap c witness version program true`. If `redeem` is not a witness program: **false** if (`c.flags.witness` and `witness` is non-empty) — the repeated `witness`-flag test is redundant here — else **true**.
   - If `c.flags.witness` is false: **true** (the witness is never consulted).
7. If `native` is `none` and the P2SH branch is not taken (flag off or not a P2SH script): **false** if `c.flags.witness` is true and `witness` is non-empty; else **true**.

Summary of the stack conventions: the interpreter's stacks (`stackSig`, `stack`, `rest`, `stack2`, and the arguments to `executeWitnessScriptV0`) are top-first; the `witness` list is bottom-first and is converted by `reverse` (P2WPKH) or `dropLast` then `reverse` (P2WSH); the Taproot handler gets the unconverted list. The `witness` stack is consulted only inside `verifyWitnessProgram` and in the two "non-empty witness" rejections. There is no "clean stack" requirement anywhere, and no restriction of `scriptSig` to pushes outside the P2SH branch.

**`p2shBytes`.** For a byte string $h$: $[\mathtt{0xa9}] \,\|\, \mathrm{pushBytes}(h) \,\|\, [\mathtt{0x87}]$ (`OP_HASH160 <push h> OP_EQUAL`). For $|h| = 20$ this is $\mathtt{0xa9}\ \mathtt{0x14}\ h\ \mathtt{0x87}$, 23 bytes; for other lengths of $h$ the result is generally not accepted by `isPayToScriptHash`.

**`witnessBytes`.** For a natural number `version` and byte string `program`: the single byte $\mathtt{0}$ if version $= 0$, else the byte $\mathtt{0x50} + \mathrm{version}$ reduced modulo $256$, followed by $\mathrm{pushBytes}(\mathrm{program})$. For $1 \le \mathrm{version} \le 16$ and $2 \le |\mathrm{program}| \le 40$ this is `OP_n`, the direct-push length byte, then the program. For version $\ge 17$ the first byte lies outside $[\mathtt{0x51}, \mathtt{0x60}]$ (and wraps for version $\ge 176$); for $|\mathrm{program}| \ge 76$ `pushBytes` emits an `OP_PUSHDATA` prefix.

**`pushesBytes`.** For a list of byte strings: the concatenation, in list order, of the canonical push `pushBytes` of each element. For the empty list, the empty byte string.

**Points a reader may find notable (descriptions only).** (a) `evalBytes` allows a script of exactly $10000$ bytes ($<$, not $\le$). (b) In `verifyWitnessProgram`, every non-version-0, non-Taproot case returns true, so the `isPayToAnchor` branch is indistinguishable from the fallthrough. (c) When the `taproot` flag is off, a version-1 32-byte native program is accepted with any witness, including an empty one, without calling the handler. (d) In `verifyScript`, a native witness program that passes returns true before any P2SH consideration, and a scriptPubKey can never be both a P2SH script and a witness program (first byte $\mathtt{0xa9}$ vs. $\{0\} \cup [\mathtt{0x51}, \mathtt{0x60}]$). (e) The P2SH branch restores `stackSig`, not `stack`. (f) The 520-byte check in `executeWitnessScriptV0` applies to the stack elements only; for P2WSH the script element is removed first. (g) Inside the P2SH-wrapped-witness branch, the redundant `c.flags.witness &&` in the non-witness-redeem case is always true. (h) `sigFlagsOf` forwards only `dersig`; `scriptFlagsOf` forwards only `cltv`, `csv`, `nulldummy`. (i) The script code for signature checks is always the whole executed script. (j) `decodeOpN` uses truncated subtraction.
