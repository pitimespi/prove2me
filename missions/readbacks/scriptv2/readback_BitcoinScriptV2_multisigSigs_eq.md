# Read-back: `BitcoinScriptV2.multisigSigs_eq`

**Statement.** Let $n_k, n_s$ be byte strings, $K$, $\mathit{Sg}$, $R$ lists of byte strings, and $N_K, N_S$ integers. Assume

1. $\mathrm{toNum}(n_k) = \mathsf{some}(N_K)$;
2. $|K| = N_K^{+} = \max(N_K, 0)$;
3. $\mathrm{toNum}(n_s) = \mathsf{some}(N_S)$;
4. $|\mathit{Sg}| = N_S^{+} = \max(N_S, 0)$.

Then
$$\mathrm{multisigSigs}\big([n_k] \mathbin{+\!\!+} K \mathbin{+\!\!+} [n_s] \mathbin{+\!\!+} \mathit{Sg} \mathbin{+\!\!+} R\big) = \mathit{Sg},$$
where the stack is listed top first: $n_k$ on top, then the elements of $K$, then $n_s$, then the elements of $\mathit{Sg}$, then those of $R$.

Notes on the literal content: $N_K$ and $N_S$ are not required to be non-negative, at most $20$, or to satisfy $N_S \le N_K$; a negative count forces the corresponding list ($K$ or $\mathit{Sg}$) to be empty. $R$ is arbitrary (it may be empty, i.e. no dummy element is required). Hypotheses 1 and 3 require $|n_k| \le 4$ and $|n_s| \le 4$, with the values read as described below (no minimal-encoding requirement).

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

### Script numbers and $\mathrm{multisigSigs}$

- $\mathrm{toNum}(x)$ (the call with "minimal encoding not required" and maximum size $4$): $\mathsf{none}$ if $|x| > 4$; otherwise $\mathsf{some}(z)$ with $z \in \mathbb Z$ obtained by reading $x$ little-endian, the bit $\texttt{0x80}$ of the last byte being a sign bit: if it is set, $z$ is minus the little-endian value of $x$ with that bit cleared; else $z$ is the little-endian value of $x$. $\mathrm{toNum}(\varepsilon) = \mathsf{some}(0)$. No minimality check is performed.
- For an integer $z$, $z^{+} := \max(z, 0)$ (negative integers convert to the natural number $0$).
- $\mathrm{multisigSigs}(\Sigma)$, for a stack $\Sigma$ listed top first, is a list of byte strings:
  - $\Sigma$ empty: $[\,]$.
  - $\Sigma = [n_k] \mathbin{+\!\!+} R$: if $\mathrm{toNum}(n_k) = \mathsf{none}$, $[\,]$. If $\mathrm{toNum}(n_k) = \mathsf{some}(N_K)$, let $R' = \mathrm{drop}_{N_K^{+}}(R)$. If $R'$ is empty, $[\,]$. If $R' = [n_s] \mathbin{+\!\!+} R''$: if $\mathrm{toNum}(n_s) = \mathsf{none}$, $[\,]$; if $\mathrm{toNum}(n_s) = \mathsf{some}(N_S)$, the result is $\mathrm{take}_{N_S^{+}}(R'')$ (all of $R''$ if it has fewer than $N_S^{+}$ elements).

  No range checks are made on $N_K$, $N_S$ (e.g. $N_S > N_K$, or negative counts, are accepted).

