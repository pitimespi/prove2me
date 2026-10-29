# Read-back: `BitcoinScriptV2.annotate_op_suffix`

**Statement.** For every byte string $s$, every list $l$ of pairs (instruction, byte string), every byte $c$ and every byte string $r$: if
$$\mathrm{annotate}(s) = \mathsf{some}(l) \quad\text{and}\quad (\mathrm{op}(c), r) \text{ is an element of } l,$$
then there exists a natural number $p$ such that
$$s[p] = c \quad\text{and}\quad r = \mathrm{drop}_{p+1}(s),$$
i.e. $p < |s|$, the byte of $s$ at 0-based index $p$ is $c$, and $r$ consists exactly of the bytes of $s$ after index $p$.

Notes on the literal content:

- Membership of $(\mathrm{op}(c), r)$ in $l$ is plain list membership; the statement does not mention the position of that pair in $l$, and it does not say that $p$ is the offset at which the instruction was read — only that *some* index $p$ holding the byte $c$ has $r$ as the bytes following it. (Since $r$ determines $p = |s| - |r| - 1$, such a $p$ is unique if it exists.)
- If $\mathrm{annotate}(s) = \mathsf{none}$ (malformed push) the statement says nothing. For $s = \varepsilon$, $l$ is empty and the statement is vacuous. Since $\mathrm{getOp}$ only yields $\mathrm{op}(c)$ with $c > \texttt{0x4e}$, the hypothesis can only hold for such $c$.

---

## Unfolded definitions used above

### Basic objects and notation

- A **byte** is an 8-bit word, identified with its value in $\{0,\dots,255\}$ and written in hexadecimal (e.g. $\texttt{0xab}$). $\mathcal B^*$ is the set of finite byte strings (lists of bytes); $|x|$ is the length, $x \mathbin{+\!\!+} y$ concatenation, $\varepsilon$ the empty string.
- $\mathrm{take}_k(x)$ is the first $\min(k,|x|)$ entries of a list $x$; $\mathrm{drop}_k(x)$ is what is left after removing the first $k$ entries, which is the empty list when $k \ge |x|$.
- For a 0-based index $p$, the statement "$x[p] = c$" means: $p < |x|$ and the entry of $x$ at index $p$ is $c$. Indexing out of range yields *no value*, so such an equation can only hold with $p<|x|$.
- A partial result is either $\mathsf{none}$ or $\mathsf{some}(y)$. Applying a function $g$ "under $\mathsf{some}$" ($\mathrm{map}_g$) sends $\mathsf{none}\mapsto\mathsf{none}$ and $\mathsf{some}(y)\mapsto\mathsf{some}(g(y))$.
- An **instruction** is either $\mathrm{push}(d)$, carrying a data string $d\in\mathcal B^*$, or $\mathrm{op}(c)$, carrying an opcode byte $c$. A **script** (parsed) is a finite list of instructions.
- Opcode bytes named below: $\texttt{OP\_16}=\texttt{0x60}$, $\texttt{OP\_IF}=\texttt{0x63}$, $\texttt{OP\_ENDIF}=\texttt{0x68}$, $\texttt{OP\_CODESEPARATOR}=\texttt{0xab}$, $\texttt{OP\_CHECKSIG}=\texttt{0xac}$, $\texttt{OP\_CHECKSIGVERIFY}=\texttt{0xad}$, $\texttt{OP\_CHECKMULTISIG}=\texttt{0xae}$, $\texttt{OP\_CHECKMULTISIGVERIFY}=\texttt{0xaf}$.
- A **signature version** $v$ is one of exactly two values: $\mathsf{base}$ (legacy) or $\mathsf{witnessV0}$.

### Reading one instruction from bytes: $\mathrm{getOp}$

$\mathrm{getOp}(x)$ returns either $\mathsf{none}$ or $\mathsf{some}(i, y)$ with $i$ an instruction and $y$ the remaining bytes:

- $x = \varepsilon$: $\mathsf{none}$.
- Otherwise let $b$ be the first byte and $y_0$ the rest.
  - If $b \le \texttt{0x4e}$ (a push opcode), a data length $n$ and a position are determined: if $b < \texttt{0x4c}$, $n = b$ and the data starts right after $b$; if $b = \texttt{0x4c}$, $n$ is the next byte ($\mathsf{none}$ if there is none); if $b = \texttt{0x4d}$, $n$ is the little-endian value of the next 2 bytes ($\mathsf{none}$ if fewer than 2 remain); if $b=\texttt{0x4e}$, $n$ is the little-endian value of the next 4 bytes ($\mathsf{none}$ if fewer than 4 remain). Then, if fewer than $n$ bytes remain, $\mathsf{none}$; otherwise $\mathsf{some}(\mathrm{push}(\text{next } n \text{ bytes}),\ \text{the bytes after them})$. (So $b=\texttt{0x00}$ gives $\mathrm{push}(\varepsilon)$.)
  - If $b > \texttt{0x4e}$: $\mathsf{some}(\mathrm{op}(b), y_0)$.

On success the remainder is a suffix of $x$ that is at least one byte shorter than $x$. $\mathrm{getOp}$ never returns $\mathrm{op}(c)$ with $c \le \texttt{0x4e}$.

### The annotated parse: $\mathrm{annotate}$

$\mathrm{annotate}(s) = \mathrm{annotateAux}(|s|, s)$, where, with a fuel counter $n$:

- $\mathrm{annotateAux}(n, \varepsilon) = \mathsf{some}([\,])$ for every $n$;
- $\mathrm{annotateAux}(0, x) = \mathsf{none}$ for $x \neq \varepsilon$;
- $\mathrm{annotateAux}(n+1, x)$ for $x\ne\varepsilon$: if $\mathrm{getOp}(x)=\mathsf{none}$ then $\mathsf{none}$; if $\mathrm{getOp}(x) = \mathsf{some}(i, r)$ then, if $\mathrm{annotateAux}(n, r) = \mathsf{none}$ the result is $\mathsf{none}$, and if it is $\mathsf{some}(L)$ the result is $\mathsf{some}([(i,r)] \mathbin{+\!\!+} L)$.

So on success $\mathrm{annotate}(s) = \mathsf{some}([(i_1, r_1), \dots, (i_n, r_n)])$, where $i_1$ is read from $s$ leaving $r_1$, $i_{j+1}$ is read from $r_j$ leaving $r_{j+1}$, and $r_n = \varepsilon$: each instruction is paired with the bytes that follow it in $s$. $\mathrm{annotate}(\varepsilon) = \mathsf{some}([\,])$. Since every successful $\mathrm{getOp}$ consumes at least one byte, the fuel $|s|$ never runs out while input remains; hence $\mathrm{annotate}(s) = \mathsf{none}$ exactly when $\mathrm{getOp}$ fails at some instruction boundary, i.e. on a malformed push (a truncated length field, or fewer data bytes than announced).

