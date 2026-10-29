# Read-back: `BitcoinScriptV2.evalOk_of_static`

**Statement.** For every verification context $c$, every signature version $v$ ($\mathsf{base}$ or $\mathsf{witnessV0}$), every initial stack $\Sigma$ and every byte string $\mathit{script}$: if

$$\text{for every parsed script } P \text{ with } \mathrm{parseScript}(\mathit{script}) = \mathsf{some}(P):\quad \mathrm{NoCodeSep}(P) \ \text{ and }\ \mathrm{NoMultisig}(P),$$

i.e. the plain parse of $\mathit{script}$, if it exists, contains none of the instructions $\mathrm{op}(\texttt{0xab})$, $\mathrm{op}(\texttt{0xae})$, $\mathrm{op}(\texttt{0xaf})$ anywhere, then
$$\mathrm{EvalOk}(c, v, \Sigma, \mathit{script}).$$

The hypothesis is vacuous when $\mathrm{parseScript}(\mathit{script}) = \mathsf{none}$ (in which case the conclusion is asserted outright). It concerns parsed instructions, not raw bytes: a byte $\texttt{0xab}$, $\texttt{0xae}$ or $\texttt{0xaf}$ occurring inside pushed data does not violate it. No assumption is made on $c$, $\Sigma$, $v$ or $|\mathit{script}|$.

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

### Side conditions: $\mathrm{StepOk}$, $\mathrm{RunOk}$

- $\mathrm{StepOk}(v, S, i)$ for a V2 state $S$ and instruction $i$:
  - $i = \mathrm{push}(d)$: always true.
  - $i = \mathrm{op}(c)$: **if** $\mathrm{allTrue}(\mathrm{vfExec}(S))$ is true, **then** both (a) $c \ne \texttt{0xab}$, and (b) if $c = \texttt{0xae}$ or $c = \texttt{0xaf}$, then for every $\mathit{sig}$ in the list $\mathrm{multisigSigs}(\mathrm{stack}(S))$, $\mathrm{fadSig}(v, S.\mathrm{sc}, \mathit{sig}) = S.\mathrm{sc}$.

  Consequences of the definition: when $\mathrm{allTrue}(\mathrm{vfExec}(S))$ is false (inside a non-executed branch), $\mathrm{StepOk}$ holds for every instruction, including $\mathrm{op}(\texttt{0xab})$. When it is true, $\mathrm{StepOk}(v,S,\mathrm{op}(\texttt{0xab}))$ is false. For $v = \mathsf{witnessV0}$, $\mathrm{fadSig}$ is the identity, so clause (b) always holds. Clause (b) also holds when $\mathrm{multisigSigs}(\mathrm{stack}(S))$ is empty. No condition is placed on $\texttt{0xac}$/$\texttt{0xad}$.
- $\mathrm{RunOk}(f, v, o, S, l)$ for a list $l$ of (instruction, bytes) pairs:
  - $l$ empty: true.
  - $l = [(i_1, r_1)] \mathbin{+\!\!+} l'$: $\mathrm{StepOk}(v, S, i_1)$ holds, **and** for every V2 state $S'$ with $\mathrm{stepV2}(f, v, o, S, (i_1,r_1)) = \mathsf{some}(S')$, $\mathrm{RunOk}(f, v, o, S', l')$ holds.

  Unwound: along the V2 run from $S$ over $l$, $\mathrm{StepOk}$ holds at each instruction that is reached (the state before instruction $j$ being the result of the $j-1$ preceding successful steps), including the instruction whose step fails; once a step returns $\mathsf{none}$, nothing is required of the later instructions. The final empty-$\mathrm{vfExec}$ check of $\mathrm{runV2}$ plays no role. $\mathrm{RunOk}$ depends on $f$ and $o$ only through which states the steps reach.

### Static conditions: $\mathrm{NoCodeSep}$, $\mathrm{NoMultisig}$

For a parsed script $P$ (a list of instructions): $\mathrm{NoCodeSep}(P)$ means $\mathrm{op}(\texttt{0xab})$ does not occur in $P$; $\mathrm{NoMultisig}(P)$ means neither $\mathrm{op}(\texttt{0xae})$ nor $\mathrm{op}(\texttt{0xaf})$ occurs in $P$. (Occurrences anywhere count, including inside branches that would not be executed.)

### Concrete oracles

- **Signature flags** $g = (g.\mathrm{dersig}, g.\mathrm{lowS}, g.\mathrm{strictenc}, g.\mathrm{witnessPubkeyType})$, four booleans. $\mathrm{SigEnc}_g(\mathit{sig})$ (signature-encoding check): true if $\mathit{sig} = \varepsilon$; false if one of $\mathrm{dersig}, \mathrm{lowS}, \mathrm{strictenc}$ is set and $\mathit{sig}$ is not strict DER plus a hash-type byte; false if $\mathrm{lowS}$ is set and the signature does not have low $S$; false if $\mathrm{strictenc}$ is set and the hash type is undefined; true otherwise. $\mathrm{PkEnc}_{g,v}(\mathit{pk})$ (public-key encoding check): false if $\mathrm{strictenc}$ is set and $\mathit{pk}$ is not a 33-byte compressed ($\texttt{02}/\texttt{03}$) or 65-byte uncompressed ($\texttt{04}$) key; false if $\mathrm{witnessPubkeyType}$ is set, $v=\mathsf{witnessV0}$ and $\mathit{pk}$ is not compressed; true otherwise.
- $\mathrm{ECDSA}(\mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sig}, \mathit{pk}, \mathit{sc})$ (the transaction checker's ECDSA check, with $\mathit{tx}$ a transaction, $n_{\mathrm{in}}\in\mathbb N$ an input index, $a\in\mathbb Z$ an amount): false if $\mathit{pk}$'s length does not match its header byte or $\mathit{sig} = \varepsilon$; otherwise the last byte of $\mathit{sig}$ is the hash type, the signature hash of $\mathit{tx}$ for input $n_{\mathrm{in}}$ with script code $\mathit{sc}$ is computed (legacy algorithm for $\mathsf{base}$, BIP143 algorithm with amount $a$ for $\mathsf{witnessV0}$), the result is false if $v = \mathsf{witnessV0}$ and $a < 0$, and otherwise it is the secp256k1 ECDSA verification of $\mathit{sig}$ without its last byte against $\mathit{pk}$ and that hash.
- $\mathrm{legacyOracleV2}(g, \mathit{tx}, n_{\mathrm{in}}, a, v)$ is the V2 oracle with Bitcoin Core's RIPEMD-160, SHA-1, SHA-256, HASH160, HASH256, the lock-time and sequence checks of $\mathit{tx}$ at input $n_{\mathrm{in}}$, and
$$\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk}) = \mathsf{none} \quad \text{if } \neg\mathrm{SigEnc}_g(\mathit{sig}) \text{ or } \neg\mathrm{PkEnc}_{g,v}(\mathit{pk}),$$
  and otherwise
$$\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk}) = \mathsf{some}\big(\mathrm{ECDSA}(\mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sig}, \mathit{pk}, \mathit{sc})\big).$$
  The script code $\mathit{sc}$ is used as given (no deletion inside the oracle).
- $\mathrm{legacyOracle}(g, \mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sc})$ is the published oracle with the same hashes and lock-time/sequence checks and signature check $\mathrm{checkSigPreTapscript}$: for $(\mathit{sig}, \mathit{pk})$, let $\mathit{sc}' = \mathrm{FD}(\mathit{sc}, \mathrm{pushBytes}(\mathit{sig}))$ if $v=\mathsf{base}$ and $\mathit{sc}' = \mathit{sc}$ if $v = \mathsf{witnessV0}$; the result is $\mathsf{none}$ if $\neg\mathrm{SigEnc}_g(\mathit{sig})$ or $\neg\mathrm{PkEnc}_{g,v}(\mathit{pk})$, and $\mathsf{some}(\mathrm{ECDSA}(\mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sig}, \mathit{pk}, \mathit{sc}'))$ otherwise.

### Verification context and byte-level evaluators

- A **context** $c$ consists of consensus flags $c.\mathrm{flags}$ (seven booleans $\mathrm{p2sh}, \mathrm{witness}, \mathrm{taproot}, \mathrm{dersig}, \mathrm{cltv}, \mathrm{csv}, \mathrm{nulldummy}$), a transaction $c.\mathrm{tx}$, an input index $c.n_{\mathrm{in}} \in \mathbb N$ and an amount $c.a \in \mathbb Z$. From it: interpreter flags $f_c = (\mathrm{cltv}, \mathrm{csv}, \mathrm{nulldummy})$ and signature flags $g_c = (\mathrm{dersig}, \mathrm{false}, \mathrm{false}, \mathrm{false})$; write $o_{c,v} = \mathrm{legacyOracleV2}(g_c, c.\mathrm{tx}, c.n_{\mathrm{in}}, c.a, v)$.
- $\mathrm{evalBytesV2}(c, v, \Sigma, \mathit{script})$: $\mathsf{none}$ if $|\mathit{script}| > 10000$; otherwise $\mathrm{evalScriptV2}(f_c, v, o_{c,v}, \Sigma, \mathit{script})$.
- $\mathrm{evalBytes}(c, v, \Sigma, \mathit{script})$ (published): $\mathsf{none}$ if $|\mathit{script}| > 10000$; otherwise, if $\mathrm{parseScript}(\mathit{script}) = \mathsf{none}$ then $\mathsf{none}$, and if it is $\mathsf{some}(P)$ then $\mathrm{evalScript}\big(f_c,\ \mathrm{legacyOracle}(g_c, c.\mathrm{tx}, c.n_{\mathrm{in}}, c.a, v, \mathit{script}),\ \Sigma,\ P\big)$ — i.e. the signature check always uses the whole byte string $\mathit{script}$ as script code, with only the checked signature's push deleted (for $\mathsf{base}$).

### $\mathrm{EvalOk}$

$\mathrm{EvalOk}(c, v, \Sigma, \mathit{script})$ means: for every list $l$ with $\mathrm{annotate}(\mathit{script}) = \mathsf{some}(l)$,
$$\mathrm{RunOk}\big(f_c, v, o_{c,v}, (\mathrm{initial}(\Sigma), \mathit{script}), l\big).$$
Since $\mathrm{annotate}$ is a function there is at most one such $l$; if $\mathrm{annotate}(\mathit{script}) = \mathsf{none}$ (malformed push), $\mathrm{EvalOk}$ holds vacuously. No bound on $|\mathit{script}|$ is involved (it is also required of scripts longer than $10000$ bytes, on which $\mathrm{evalBytesV2}$ returns $\mathsf{none}$ without running).

