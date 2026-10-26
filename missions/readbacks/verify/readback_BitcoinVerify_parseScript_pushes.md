# Read-back: `BitcoinVerify.parseScript_pushes`

**Binders and hypothesis.** One universally quantified variable $ps$, a finite list of byte strings (each a finite list of 8-bit bytes). One hypothesis `hp`: every element $p$ of $ps$ satisfies $|p| \le 520$ (`MAX_SCRIPT_ELEMENT_SIZE`). The list may be empty, in which case the hypothesis holds vacuously.

**Conclusion.**

$$\mathrm{parseScript}\big(\mathrm{pushesBytes}(ps)\big) = \mathrm{some}\big(\mathrm{map}\ \mathrm{push}\ ps\big),$$

i.e. the byte-level parser succeeds on the concatenated canonical pushes and returns exactly the instruction list consisting of one push instruction per element of $ps$, carrying that element's bytes, in the same order. For $ps = []$ this says `parseScript [] = some []`.

**Unfolding `pushesBytes`.** `pushesBytes ps` concatenates `pushBytes p` over the elements $p$ of $ps$ in order. `pushBytes p` is: for $|p| < 76$, the single byte $|p|$ followed by $p$ (for $p = []$, the lone byte $\mathtt{0x00}$); for $76 \le |p| \le 255$, $\mathtt{0x4c}$, one length byte, then $p$; for $256 \le |p| \le 65535$, $\mathtt{0x4d}$, two little-endian length bytes, then $p$; otherwise $\mathtt{0x4e}$, four little-endian length bytes, then $p$. Under $|p| \le 520$ only the first three shapes occur.

**Unfolding `parseScript`.** `parseScript s` runs `parseScriptAux` with fuel $|s|$: on the empty string it returns `some []`; with zero fuel on a non-empty string it returns nothing; otherwise it calls `getOp` on $s$ and, on success with instruction $i$ and remainder $r$, recursively parses $r$ with one less fuel and prepends $i$; any failure propagates as nothing. `getOp` on a non-empty string with first byte $o$: if $o \le \mathtt{0x4e}$ it is a push — for $o < \mathtt{0x4c}$ the push length is $o$ itself; for $o = \mathtt{0x4c}$ the next byte is the length (nothing if absent); for $o = \mathtt{0x4d}$ the next two bytes little-endian (nothing if fewer than two remain); for $o = \mathtt{0x4e}$ the next four (nothing if fewer than four) — and then nothing if fewer than that many bytes remain, else the push of those bytes and the rest; if $o > \mathtt{0x4e}$ it is the non-push opcode $o$. Each successful `getOp` consumes at least one byte, so fuel $|s|$ never runs out early.

**Logical content.** The theorem asserts that the encoder `pushBytes` and the decoder `getOp` are inverse along concatenations: parsing re-splits the byte string exactly at the boundaries the encoder wrote, and recovers each element's bytes unchanged as a `push` instruction, provided every element has at most 520 bytes. It is an equality of optional instruction lists, so it also asserts that the parse does not fail.

**What is not said.** The theorem does not say anything about elements longer than 520 bytes (the `PUSHDATA2`/`PUSHDATA4` shapes are then outside the statement, even though the hypothesis is not visibly used by the parser); it does not say that the parsed instructions *execute* successfully or satisfy the interpreter's 520-byte push limit — it is only about parsing; it does not bound the total length (no `MAX_SCRIPT_SIZE` condition, and `parseScript` has none); it does not assert the converse (that every byte string parsing to a list of pushes is of the form `pushesBytes ps` — other encodings of the same pushes exist); and it does not relate to `isPushOnly` or `verifyScript`.
