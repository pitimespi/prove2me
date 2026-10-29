# Read-back: `BitcoinScriptV2.checksig_deletes_one`

**Statement.** For every signature version $v$ ($\mathsf{base}$ or $\mathsf{witnessV0}$), every V2 oracle $o$, every V2 state $S$, every byte $c$ with
$$c = \texttt{0xac}\ (\texttt{OP\_CHECKSIG}) \quad\text{or}\quad c = \texttt{0xad}\ (\texttt{OP\_CHECKSIGVERIFY}),$$
and all byte strings $\mathit{sig}, \mathit{pk}$:
$$\mathrm{oracleAt}(v, o, S, \mathrm{op}(c)).\mathrm{checkSig}(\mathit{sig}, \mathit{pk}) = o.\mathrm{checkSig}\big(\mathrm{fadSig}(v, S.\mathrm{sc}, \mathit{sig}),\ \mathit{sig},\ \mathit{pk}\big).$$

In words: the published-oracle signature check that the V2 interpreter supplies for $\texttt{OP\_CHECKSIG}$/$\texttt{OP\_CHECKSIGVERIFY}$ at state $S$, applied to $(\mathit{sig},\mathit{pk})$, equals the V2 oracle's check on the script code obtained from the state's current script code $S.\mathrm{sc}$ by deleting the canonical push of $\mathit{sig}$ (for $v = \mathsf{base}$), or on $S.\mathrm{sc}$ itself (for $v = \mathsf{witnessV0}$). The equation is about the oracle only; it involves neither the stack contents nor whether the opcode is executed ($\mathrm{vfExec}$), and $\mathit{sig}, \mathit{pk}$ are arbitrary (not required to be the stack elements). Only the $\mathrm{checkSig}$ component of the oracle is compared.

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

