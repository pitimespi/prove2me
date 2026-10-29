# Read-back: `BitcoinScriptV2.legacyOracle_eq`

**Statement.** For all signature flags $g$ (four arbitrary booleans $\mathrm{dersig}, \mathrm{lowS}, \mathrm{strictenc}, \mathrm{witnessPubkeyType}$), every transaction $\mathit{tx}$, input index $n_{\mathrm{in}} \in \mathbb N$, amount $a \in \mathbb Z$, signature version $v$ ($\mathsf{base}$ or $\mathsf{witnessV0}$) and byte string $\mathit{sc}$, the two published oracles are equal:
$$\mathrm{legacyOracle}(g, \mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sc}) = \mathrm{withCodeSig}\big(\mathrm{legacyOracleV2}(g, \mathit{tx}, n_{\mathrm{in}}, a, v),\ v,\ \mathit{sc}\big).$$

This is equality of the whole eight-component structures, with function components equal as functions. Unfolded, the components are: the same five hash functions and lock-time/sequence checks on both sides, and signature checks which for every $(\mathit{sig}, \mathit{pk})$ are, on the left, "$\mathsf{none}$ if the signature- or public-key-encoding check fails, else $\mathsf{some}$ of the ECDSA check with script code $\mathit{sc}'$", where $\mathit{sc}' = \mathrm{FD}(\mathit{sc}, \mathrm{pushBytes}(\mathit{sig}))$ for $\mathsf{base}$ and $\mathit{sc}$ for $\mathsf{witnessV0}$; on the right, $\mathrm{legacyOracleV2}$'s check applied to the script code $\mathrm{fadSig}(v, \mathit{sc}, \mathit{sig})$, which is the same encoding tests followed by the same ECDSA check on that script code. No hypotheses.

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

### Oracles

- A **published oracle** $O$ consists of five functions $\mathcal B^*\to\mathcal B^*$ (RIPEMD-160, SHA-1, SHA-256, HASH160, HASH256), a function $O.\mathrm{checkSig}(\mathit{sig}, \mathit{pk}) \in \{\mathsf{none}, \mathsf{some}(\mathrm{true}), \mathsf{some}(\mathrm{false})\}$, and two predicates $\mathrm{checkLockTime}, \mathrm{checkSequence} : \mathbb Z \to \{\mathrm{true},\mathrm{false}\}$.
- A **V2 oracle** $o$ has the same five hash functions and two predicates, but its signature check takes a script code as an extra first argument: $o.\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk}) \in \{\mathsf{none}, \mathsf{some}(\mathrm{true}), \mathsf{some}(\mathrm{false})\}$. All components are arbitrary functions.
- $\mathrm{toOracle}(o)$: the published oracle with $o$'s hashes and predicates and the signature check that always returns $\mathsf{none}$.
- $\mathrm{withCode}(o, \mathit{sc})$: $\mathrm{toOracle}(o)$ with signature check $(\mathit{sig}, \mathit{pk}) \mapsto o.\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk})$.
- $\mathrm{withCodeSig}(o, v, \mathit{sc})$: $\mathrm{toOracle}(o)$ with signature check $(\mathit{sig}, \mathit{pk}) \mapsto o.\mathrm{checkSig}\big(\mathrm{fadSig}(v, \mathit{sc}, \mathit{sig}), \mathit{sig}, \mathit{pk}\big)$.

### Concrete oracles

- **Signature flags** $g = (g.\mathrm{dersig}, g.\mathrm{lowS}, g.\mathrm{strictenc}, g.\mathrm{witnessPubkeyType})$, four booleans. $\mathrm{SigEnc}_g(\mathit{sig})$ (signature-encoding check): true if $\mathit{sig} = \varepsilon$; false if one of $\mathrm{dersig}, \mathrm{lowS}, \mathrm{strictenc}$ is set and $\mathit{sig}$ is not strict DER plus a hash-type byte; false if $\mathrm{lowS}$ is set and the signature does not have low $S$; false if $\mathrm{strictenc}$ is set and the hash type is undefined; true otherwise. $\mathrm{PkEnc}_{g,v}(\mathit{pk})$ (public-key encoding check): false if $\mathrm{strictenc}$ is set and $\mathit{pk}$ is not a 33-byte compressed ($\texttt{02}/\texttt{03}$) or 65-byte uncompressed ($\texttt{04}$) key; false if $\mathrm{witnessPubkeyType}$ is set, $v=\mathsf{witnessV0}$ and $\mathit{pk}$ is not compressed; true otherwise.
- $\mathrm{ECDSA}(\mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sig}, \mathit{pk}, \mathit{sc})$ (the transaction checker's ECDSA check, with $\mathit{tx}$ a transaction, $n_{\mathrm{in}}\in\mathbb N$ an input index, $a\in\mathbb Z$ an amount): false if $\mathit{pk}$'s length does not match its header byte or $\mathit{sig} = \varepsilon$; otherwise the last byte of $\mathit{sig}$ is the hash type, the signature hash of $\mathit{tx}$ for input $n_{\mathrm{in}}$ with script code $\mathit{sc}$ is computed (legacy algorithm for $\mathsf{base}$, BIP143 algorithm with amount $a$ for $\mathsf{witnessV0}$), the result is false if $v = \mathsf{witnessV0}$ and $a < 0$, and otherwise it is the secp256k1 ECDSA verification of $\mathit{sig}$ without its last byte against $\mathit{pk}$ and that hash.
- $\mathrm{legacyOracleV2}(g, \mathit{tx}, n_{\mathrm{in}}, a, v)$ is the V2 oracle with Bitcoin Core's RIPEMD-160, SHA-1, SHA-256, HASH160, HASH256, the lock-time and sequence checks of $\mathit{tx}$ at input $n_{\mathrm{in}}$, and
$$\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk}) = \mathsf{none} \quad \text{if } \neg\mathrm{SigEnc}_g(\mathit{sig}) \text{ or } \neg\mathrm{PkEnc}_{g,v}(\mathit{pk}),$$
  and otherwise
$$\mathrm{checkSig}(\mathit{sc}, \mathit{sig}, \mathit{pk}) = \mathsf{some}\big(\mathrm{ECDSA}(\mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sig}, \mathit{pk}, \mathit{sc})\big).$$
  The script code $\mathit{sc}$ is used as given (no deletion inside the oracle).
- $\mathrm{legacyOracle}(g, \mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sc})$ is the published oracle with the same hashes and lock-time/sequence checks and signature check $\mathrm{checkSigPreTapscript}$: for $(\mathit{sig}, \mathit{pk})$, let $\mathit{sc}' = \mathrm{FD}(\mathit{sc}, \mathrm{pushBytes}(\mathit{sig}))$ if $v=\mathsf{base}$ and $\mathit{sc}' = \mathit{sc}$ if $v = \mathsf{witnessV0}$; the result is $\mathsf{none}$ if $\neg\mathrm{SigEnc}_g(\mathit{sig})$ or $\neg\mathrm{PkEnc}_{g,v}(\mathit{pk})$, and $\mathsf{some}(\mathrm{ECDSA}(\mathit{tx}, n_{\mathrm{in}}, a, v, \mathit{sig}, \mathit{pk}, \mathit{sc}'))$ otherwise.

