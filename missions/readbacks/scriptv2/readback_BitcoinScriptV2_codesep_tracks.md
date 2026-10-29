# Read-back: `BitcoinScriptV2.codesep_tracks`

**Statement.** Let $f$ be interpreter flags, $v$ a signature version ($\mathsf{base}$ or $\mathsf{witnessV0}$), $o$ a V2 oracle, $\mathit{script}$ a byte string, $l$ a list of (instruction, byte string) pairs, $k$ a natural number, $r$ a byte string, and $S, S'$ V2 states. Assume

1. $\mathrm{annotate}(\mathit{script}) = \mathsf{some}(l)$;
2. $l[k] = (\mathrm{op}(\texttt{0xab}), r)$, i.e. $k < |l|$ and the entry of $l$ at 0-based index $k$ is the pair ($\texttt{OP\_CODESEPARATOR}$, $r$);
3. $\mathrm{allTrue}(\mathrm{vfExec}(S)) = \mathrm{true}$ (every entry of $S$'s condition stack is true; this includes an empty condition stack);
4. $\mathrm{stepV2}\big(f, v, o, S, (\mathrm{op}(\texttt{0xab}), r)\big) = \mathsf{some}(S')$.

Then both

$$S'.\mathrm{sc} = r \qquad\text{and}\qquad \exists p\in\mathbb N:\ \mathit{script}[p] = \texttt{0xab}\ \text{ and }\ r = \mathrm{drop}_{p+1}(\mathit{script}),$$

the second meaning: $p < |\mathit{script}|$, the byte of $\mathit{script}$ at 0-based index $p$ is $\texttt{0xab}$, and $r$ is exactly the bytes of $\mathit{script}$ after index $p$.

Notes on the literal content:

- The states $S$ and $S'$ are arbitrary apart from hypotheses 3 and 4; $S$ is not required to be the state reached by running the first $k$ entries of $l$ from any initial state, and $S.\mathrm{sc}$ is unconstrained. The index $k$ and hypotheses 1–2 serve only to say that $(\mathrm{op}(\texttt{0xab}), r)$ is an entry of the annotated parse of $\mathit{script}$; the conclusion does not mention $k$, and $p$ is not stated to be related to $k$.
- The second conjunct depends only on hypotheses 1–2; the first only on 3–4.
- Hypothesis 4 can fail (e.g. when the operation counter of $S$ is already $201$, since $\texttt{0xab} > \texttt{0x60}$ is counted, or when the stacks of $S$ exceed $1000$ elements); then the statement is vacuous for that $S$.

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

### Signature-push deletion: $\mathrm{pushBytes}$, $\mathrm{findAndDelete}$, $\mathrm{fadSig}$, $\mathrm{fadAll}$

- $\mathrm{pushBytes}(d)$, the canonical push of $d$: if $|d| < \texttt{0x4c}$ it is the byte $|d|$ followed by $d$; else if $|d| \le 255$ it is $\texttt{0x4c}$, the byte $|d|$, then $d$; else if $|d| \le 65535$ it is $\texttt{0x4d}$, $|d|$ as 2 little-endian bytes, then $d$; otherwise $\texttt{0x4e}$, $|d| \bmod 2^{32}$ as 4 little-endian bytes, then $d$. It is never empty ($\mathrm{pushBytes}(\varepsilon) = [\texttt{0x00}]$).
- $\mathrm{findAndDelete}(x, b)$ returns a pair (resulting string, count); only the first component (written $\mathrm{FD}(x,b)$) is used here. If $b = \varepsilon$ the result is $(x, 0)$. Otherwise $x$ is scanned from the start: at the current instruction boundary, copies of $b$ are removed as long as the remaining string begins with $b$ (each removal counted); then one instruction is read with $\mathrm{getOp}$: if that fails, the whole remaining string is kept verbatim and the scan stops; if it succeeds, that instruction's bytes are kept and the scan continues right after it. The result is the concatenation of the kept bytes. (The recursion carries fuel $|x|+1$, and when fuel is exhausted the remaining bytes are kept verbatim; every iteration of the scan consumes at least one byte.)
- $\mathrm{fadSig}(v, \mathit{sc}, \mathit{sig})$:
$$\mathrm{fadSig}(\mathsf{base}, \mathit{sc}, \mathit{sig}) = \mathrm{FD}\big(\mathit{sc}, \mathrm{pushBytes}(\mathit{sig})\big), \qquad \mathrm{fadSig}(\mathsf{witnessV0}, \mathit{sc}, \mathit{sig}) = \mathit{sc}.$$
- $\mathrm{fadAll}(v, \mathit{sc}, [\sigma_1,\dots,\sigma_m])$ is the left fold of $\mathrm{fadSig}(v,\cdot,\cdot)$ over the list, in list order:
$$\mathrm{fadAll}(v, \mathit{sc}, [\sigma_1,\dots,\sigma_m]) = \mathrm{fadSig}\big(v, \cdots \mathrm{fadSig}(v, \mathrm{fadSig}(v, \mathit{sc}, \sigma_1), \sigma_2) \cdots, \sigma_m\big),$$
and $\mathrm{fadAll}(v, \mathit{sc}, [\,]) = \mathit{sc}$.

### Script numbers and $\mathrm{multisigSigs}$

- $\mathrm{toNum}(x)$ (the call with "minimal encoding not required" and maximum size $4$): $\mathsf{none}$ if $|x| > 4$; otherwise $\mathsf{some}(z)$ with $z \in \mathbb Z$ obtained by reading $x$ little-endian, the bit $\texttt{0x80}$ of the last byte being a sign bit: if it is set, $z$ is minus the little-endian value of $x$ with that bit cleared; else $z$ is the little-endian value of $x$. $\mathrm{toNum}(\varepsilon) = \mathsf{some}(0)$. No minimality check is performed.
- For an integer $z$, $z^{+} := \max(z, 0)$ (negative integers convert to the natural number $0$).
- $\mathrm{multisigSigs}(\Sigma)$, for a stack $\Sigma$ listed top first, is a list of byte strings:
  - $\Sigma$ empty: $[\,]$.
  - $\Sigma = [n_k] \mathbin{+\!\!+} R$: if $\mathrm{toNum}(n_k) = \mathsf{none}$, $[\,]$. If $\mathrm{toNum}(n_k) = \mathsf{some}(N_K)$, let $R' = \mathrm{drop}_{N_K^{+}}(R)$. If $R'$ is empty, $[\,]$. If $R' = [n_s] \mathbin{+\!\!+} R''$: if $\mathrm{toNum}(n_s) = \mathsf{none}$, $[\,]$; if $\mathrm{toNum}(n_s) = \mathsf{some}(N_S)$, the result is $\mathrm{take}_{N_S^{+}}(R'')$ (all of $R''$ if it has fewer than $N_S^{+}$ elements).

  No range checks are made on $N_K$, $N_S$ (e.g. $N_S > N_K$, or negative counts, are accepted).

### Oracles

- A **published oracle** $O$ consists of five functions $\mathcal B^*\to\mathcal B^*$ (RIPEMD-160, SHA-1, SHA-256, HASH160, HASH256), a function $O.\mathrm{checkSig}(\mathit{sig}, \mathit{pk}) \in \{\mathsf{none}, \mathsf{some}(\mathrm{true}), \mathsf{some}(\mathrm{false})\}$, and two predicates $\mathrm{checkLockTime}, \mathrm{checkSequence} : \mathbb Z \to \{\mathrm{true},\mathrm{false}\}$.
- A **V2 oracle** $o$ has the same five hash functions and two predicates, but its signature check takes a script code as an extra first argument: $o.\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk}) \in \{\mathsf{none}, \mathsf{some}(\mathrm{true}), \mathsf{some}(\mathrm{false})\}$. All components are arbitrary functions.
- $\mathrm{toOracle}(o)$: the published oracle with $o$'s hashes and predicates and the signature check that always returns $\mathsf{none}$.
- $\mathrm{withCode}(o, \mathit{sc})$: $\mathrm{toOracle}(o)$ with signature check $(\mathit{sig}, \mathit{pk}) \mapsto o.\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk})$.
- $\mathrm{withCodeSig}(o, v, \mathit{sc})$: $\mathrm{toOracle}(o)$ with signature check $(\mathit{sig}, \mathit{pk}) \mapsto o.\mathrm{checkSig}\big(\mathrm{fadSig}(v, \mathit{sc}, \mathit{sig}), \mathit{sig}, \mathit{pk}\big)$.

### V2 states and $\mathrm{oracleAt}$

- A **V2 state** $S$ is a pair $(S.\mathrm{st}, S.\mathrm{sc})$ of a published interpreter state $S.\mathrm{st}$ (a main stack and an alt stack of byte strings listed top first, a boolean condition stack $\mathrm{vfExec}$, and an operation counter) and a byte string $S.\mathrm{sc}$, the *script code*. Write $\mathrm{stack}(S)$ and $\mathrm{vfExec}(S)$ for the main stack and condition stack of $S.\mathrm{st}$.
- $\mathrm{oracleAt}(v, o, S, i)$, the published oracle used for instruction $i$ from state $S$:
  - if $i = \mathrm{op}(c)$ with $c = \texttt{0xae}$ or $c = \texttt{0xaf}$: $\mathrm{withCode}\big(o,\ \mathrm{fadAll}(v, S.\mathrm{sc}, \mathrm{multisigSigs}(\mathrm{stack}(S)))\big)$;
  - for every other $\mathrm{op}(c)$, and for every $\mathrm{push}(d)$: $\mathrm{withCodeSig}(o, v, S.\mathrm{sc})$.

### The published interpreter: $\mathrm{step}$, $\mathrm{run}$, $\mathrm{evalScript}$

- **Flags** $f$ are three booleans $(f.\mathrm{cltv}, f.\mathrm{csv}, f.\mathrm{nulldummy})$.
- A **published state** is a tuple (main stack, alt stack, $\mathrm{vfExec}$, $\mathrm{opCount}$): two stacks of byte strings listed top first, a list of booleans, and a natural number. $\mathrm{initial}(\Sigma) = (\Sigma, [\,], [\,], 0)$. $\mathrm{allTrue}(L)$ is true iff every entry of the boolean list $L$ is true (in particular $\mathrm{allTrue}([\,])$ is true).
- $\mathrm{step}(f, O, T, i)$, one instruction from published state $T$ with published oracle $O$:
  - $i = \mathrm{push}(d)$: $\mathsf{none}$ if $|d| > 520$; otherwise $T'$ is $T$ with $d$ pushed on the main stack if $\mathrm{allTrue}(T.\mathrm{vfExec})$, and $T' = T$ otherwise; the result is $\mathsf{none}$ if the two stacks of $T'$ together hold more than $1000$ elements, else $\mathsf{some}(T')$. The oracle is not used.
  - $i = \mathrm{op}(c)$: let $e = \mathrm{allTrue}(T.\mathrm{vfExec})$. If $c > \texttt{0x60}$ and $T.\mathrm{opCount} + 1 > 201$, $\mathsf{none}$; otherwise the counter is incremented when $c > \texttt{0x60}$. Then: if $c$ is one of the fifteen disabled opcodes ($\texttt{0x7e}$–$\texttt{0x81}$, $\texttt{0x83}$–$\texttt{0x86}$, $\texttt{0x8d}$, $\texttt{0x8e}$, $\texttt{0x95}$–$\texttt{0x99}$), $\mathsf{none}$ (whether or not executing). Else if $e$ is true or $\texttt{0x63} \le c \le \texttt{0x68}$, the result is $\mathrm{execOp}(f, O, e, c, T)$ followed by the same 1000-element check; else (a non-executed, non-conditional opcode) the state (with updated counter) is returned unchanged, subject to the 1000-element check.
- $\mathrm{execOp}$ is the opcode switch (one case per opcode; any opcode not handled gives $\mathsf{none}$). Its use of the oracle and the cases relevant here:
  - the hash opcodes $\texttt{0xa6}$–$\texttt{0xaa}$ replace the top element by the corresponding hash function of $O$; $\texttt{0xb1}$ (when $f.\mathrm{cltv}$) consults $O.\mathrm{checkLockTime}$ and $\texttt{0xb2}$ (when $f.\mathrm{csv}$) $O.\mathrm{checkSequence}$;
  - $\texttt{0xab}$ ($\texttt{OP\_CODESEPARATOR}$) returns the state unchanged;
  - $\texttt{0xac}$/$\texttt{0xad}$: the main stack must be $[\mathit{pk}, \mathit{sig}] \mathbin{+\!\!+} R$ (else $\mathsf{none}$); $O.\mathrm{checkSig}(\mathit{sig}, \mathit{pk})$ is called; $\mathsf{none}$ gives $\mathsf{none}$; $\mathsf{some}(b)$: for $\texttt{0xad}$ the stack becomes $R$ if $b$, else $\mathsf{none}$; for $\texttt{0xac}$ the stack becomes $[\,[\texttt{0x01}]\,] \mathbin{+\!\!+} R$ if $b$ and $[\varepsilon] \mathbin{+\!\!+} R$ if not;
  - $\texttt{0xae}$/$\texttt{0xaf}$: the main stack must be $[n_k] \mathbin{+\!\!+} R$; $N_K = \mathrm{toNum}(n_k)$ must exist with $0 \le N_K \le 20$; $\mathrm{opCount} + N_K \le 201$; the next $N_K$ elements are the keys (there must be that many); then an element $n_s$ with $N_S = \mathrm{toNum}(n_s)$ existing and $0 \le N_S \le N_K$; the next $N_S$ elements are the signatures (there must be that many); then the matching loop below must not return $\mathsf{none}$; then one more element (the dummy) must exist, and if $f.\mathrm{nulldummy}$ it must be empty; the stack becomes the elements below the dummy, with $[\,[\texttt{0x01}]\,]$ or $[\varepsilon]$ pushed for $\texttt{0xae}$ according to the loop's verdict, while for $\texttt{0xaf}$ a false verdict gives $\mathsf{none}$; $\mathrm{opCount}$ becomes $\mathrm{opCount}+N_K$. Any failed requirement gives $\mathsf{none}$. The **matching loop** on signatures and keys (both top first): no signatures left gives $\mathrm{true}$; signatures left but no keys gives $\mathrm{false}$; otherwise $O.\mathrm{checkSig}(\text{current sig}, \text{current key})$ is called, $\mathsf{none}$ aborts with $\mathsf{none}$; on success both advance, on failure only the key advances; whenever fewer keys than signatures remain the verdict is $\mathrm{false}$.
- $\mathrm{run}(f, O, T, [i_1,\dots,i_n])$ applies $\mathrm{step}$ to $i_1, \dots, i_n$ in turn, giving $\mathsf{none}$ as soon as a step does; after the last instruction it returns $\mathsf{some}(\text{final state})$ if the final $\mathrm{vfExec}$ is empty and $\mathsf{none}$ otherwise.
- $\mathrm{evalScript}(f, O, \Sigma, P) = \mathrm{map}_{\text{main stack}}\big(\mathrm{run}(f, O, \mathrm{initial}(\Sigma), P)\big)$: the final main stack, or $\mathsf{none}$.

### The V2 interpreter: $\mathrm{stepV2}$, $\mathrm{runV2}$, $\mathrm{evalScriptV2}$

- $\mathrm{stepV2}(f, v, o, S, (i, r))$, for a V2 state $S$ and a pair of an instruction $i$ and a byte string $r$:
$$\mathrm{stepV2}(f,v,o,S,(i,r)) = \mathrm{map}_{\,T \mapsto (T,\ \mathit{sc}')}\Big(\mathrm{step}\big(f, \mathrm{oracleAt}(v,o,S,i), S.\mathrm{st}, i\big)\Big),$$
where $\mathit{sc}' = r$ if $i = \mathrm{op}(\texttt{0xab})$ **and** $\mathrm{allTrue}(\mathrm{vfExec}(S))$ (the condition stack *before* the step), and $\mathit{sc}' = S.\mathrm{sc}$ otherwise. So it fails exactly when the published step fails, and otherwise the published part is the published step's result.
- $\mathrm{runV2}(f, v, o, S, [x_1,\dots,x_n])$ applies $\mathrm{stepV2}$ to $x_1,\dots,x_n$ in turn, giving $\mathsf{none}$ as soon as a step does; after the last one it returns $\mathsf{some}(\text{final V2 state})$ if the final $\mathrm{vfExec}$ is empty and $\mathsf{none}$ otherwise.
- $\mathrm{evalScriptV2}(f, v, o, \Sigma, \mathit{script})$ for a byte string $\mathit{script}$: if $\mathrm{annotate}(\mathit{script}) = \mathsf{none}$ the result is $\mathsf{none}$; if it is $\mathsf{some}(l)$, the result is the main stack of $\mathrm{runV2}\big(f, v, o, (\mathrm{initial}(\Sigma), \mathit{script}), l\big)$ under $\mathrm{map}$ (so $\mathsf{none}$ if that run fails). The initial script code is the whole byte string $\mathit{script}$.

