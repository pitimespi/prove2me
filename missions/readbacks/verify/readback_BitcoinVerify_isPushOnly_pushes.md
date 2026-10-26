# Read-back: `BitcoinVerify.isPushOnly_pushes`

**Binders and hypothesis.** One universally quantified variable $ps$, a finite list of byte strings (each byte string a finite list of 8-bit bytes). One hypothesis `hp`: for every element $p$ of the list $ps$, $|p| \le 520$ (the constant `MAX_SCRIPT_ELEMENT_SIZE`). The list may be empty, in which case the hypothesis is vacuous.

**Conclusion.**

$$\mathrm{isPushOnly}\big(\mathrm{pushesBytes}(ps)\big) = \mathrm{true}.$$

**Unfolding `pushesBytes`.** `pushesBytes ps` is the concatenation, in list order, of `pushBytes p` for each $p \in ps$, where `pushBytes p` is the canonical push encoding of $p$: if $|p| < 76$, the length byte $|p|$ followed by $p$ (for $p = []$ this is the single byte $\mathtt{0x00}$); if $76 \le |p| \le 255$, the byte $\mathtt{0x4c}$ (`OP_PUSHDATA1`), one length byte, then $p$; if $256 \le |p| \le 65535$, the byte $\mathtt{0x4d}$ (`OP_PUSHDATA2`), two little-endian length bytes, then $p$; otherwise $\mathtt{0x4e}$ (`OP_PUSHDATA4`), four little-endian length bytes, then $p$. Under the hypothesis $|p| \le 520$, only the first three forms occur. For the empty list, `pushesBytes [] = []`.

**Unfolding `isPushOnly`.** `isPushOnly s` runs `isPushOnlyAux` with fuel $|s|$ on $s$. The auxiliary returns true on the empty string; false when the fuel is $0$ and the string is non-empty; otherwise it calls the byte-level parser `getOp` on the string: if `getOp` fails (a push opcode whose declared length exceeds the remaining bytes, or a `PUSHDATA` prefix with too few length bytes), the result is false; if it returns a push instruction, the auxiliary recurses on the remaining bytes with one less fuel; if it returns a non-push opcode $c$, the result is false when $\mathtt{0x60} < c$ (opcodes above `OP_16`) and otherwise recurses. `getOp` consumes at least one byte per call, so fuel $|s|$ never runs out before the string is exhausted.

**What the theorem therefore says.** For every list of byte strings each of at most 520 bytes, the concatenation of their canonical pushes, when parsed instruction by instruction, consists only of instructions that are data pushes (or opcodes $\le \mathtt{0x60}$, which cannot arise from `pushBytes`), and the parse never fails. In particular the parser re-finds exactly the push boundaries written by `pushBytes`.

**What is not said.** The theorem does not state the converse (that every push-only byte string is of the form `pushesBytes ps`); it does not say anything about lists containing an element longer than 520 bytes (the statement is silent, not negative, for those — `isPushOnly` itself has no size test, but the theorem's hypothesis excludes them); it says nothing about the number of elements or the total length (no `MAX_SCRIPT_SIZE` or `MAX_STACK_SIZE` bound appears); it does not say that evaluating `pushesBytes ps` succeeds or produces any particular stack; and it does not relate `isPushOnly` to `parseScript` or to `verifyScript`.
