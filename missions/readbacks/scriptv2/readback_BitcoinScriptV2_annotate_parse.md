# Read-back: `BitcoinScriptV2.annotate_parse`

**Statement.** For every byte string $s$,
$$\mathrm{map}_{\,L \mapsto \pi_1(L)}\big(\mathrm{annotate}(s)\big) = \mathrm{parseScript}(s),$$
where for a list $L = [(i_1, r_1), \dots, (i_n, r_n)]$ of pairs, $\pi_1(L) = [i_1, \dots, i_n]$ is the list of first components. Spelled out, this is the conjunction of:

- $\mathrm{annotate}(s) = \mathsf{none}$ if and only if $\mathrm{parseScript}(s) = \mathsf{none}$;
- whenever $\mathrm{annotate}(s) = \mathsf{some}(L)$, $\mathrm{parseScript}(s) = \mathsf{some}(\pi_1(L))$, i.e. the annotated parse and the plain parse produce the same instructions in the same order.

There are no hypotheses; it is asserted for every $s$, including $s = \varepsilon$ (both sides $\mathsf{some}([\,])$) and malformed scripts (both sides $\mathsf{none}$).

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

### The plain parse: $\mathrm{parseScript}$

$\mathrm{parseScript}(s) = \mathrm{parseScriptAux}(|s|, s)$ follows exactly the same recursion as $\mathrm{annotateAux}$ (empty input gives $\mathsf{some}([\,])$; fuel $0$ on non-empty input gives $\mathsf{none}$; a failing $\mathrm{getOp}$ gives $\mathsf{none}$), but on success records only the instructions: $\mathsf{some}([i_1,\dots,i_n])$.

