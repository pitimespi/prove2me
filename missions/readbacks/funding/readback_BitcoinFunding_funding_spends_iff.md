# Read-back: `BitcoinFunding.funding_spends_iff`

A **byte** is an 8-bit word; a **byte string** ($\mathsf{Bytes}$) is a finite list of bytes; a **stack** is a finite list of byte strings whose first entry is the top.

## Statement

The theorem quantifies over:

- a flag record $f$ with exactly three boolean fields $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$;
- an **oracle** $o$: a record of abstract functions $o.\mathrm{ripemd160}, o.\mathrm{sha1}, o.\mathrm{sha256}, o.\mathrm{hash160}, o.\mathrm{hash256} : \mathsf{Bytes}\to\mathsf{Bytes}$; $o.\mathrm{checkSig} : \mathsf{Bytes}\times\mathsf{Bytes}\to\mathrm{Option}(\mathrm{Bool})$ (first argument "signature", second "public key"; value $\mathrm{none}$, $\mathrm{some}\,\mathrm{true}$ or $\mathrm{some}\,\mathrm{false}$); $o.\mathrm{checkLockTime}, o.\mathrm{checkSequence}:\mathbb{Z}\to\mathrm{Bool}$. Nothing is assumed about any of these functions;
- two byte strings $k_1,k_2$ (`pubkey1`, `pubkey2`), unconstrained in content;
- a stack $st$ (any finite list of byte strings: empty, or of any length, with elements of any length);

and assumes $|k_1|\le520$ and $|k_2|\le520$ ($520$ = `MAX_SCRIPT_ELEMENT_SIZE`). No bound is placed on the number or the sizes of the elements of $st$.

Under these, the theorem asserts the logical equivalence

$$
\Big(\exists\, res:\ \mathrm{evalScript}\big(f,o,st,\mathrm{fundingScript}(k_1,k_2)\big)=\mathrm{some}(res)\ \wedge\ |res|=1\ \wedge\ \mathrm{topTrue}(res)=\mathrm{true}\Big)
\;\Longleftrightarrow\;
\mathrm{FundingSpend}(f,o,k_1,k_2,st).
$$

The left-hand side says: the interpreter run of the funding script on the initial stack $st$ does not fail, its final main stack $res$ has exactly one element, and that element is "true" in the sense of $\mathrm{castToBool}$. The right-hand side is the proposition $\mathrm{FundingSpend}$, unfolded below.

## `topTrue` and `castToBool`

$\mathrm{topTrue}(res)$ is $\mathrm{false}$ when $res$ is empty, and $\mathrm{castToBool}(\text{top element})$ otherwise. $\mathrm{castToBool}(b)$ for a byte string $b$ is: $\mathrm{false}$ for $b=[\,]$; for a single byte $[x]$, true iff $x\ne\mathtt{0x00}$ and $x\ne\mathtt{0x80}$; for $x::\mathit{rest}$ with $\mathit{rest}$ non-empty, true iff $x\ne\mathtt{0x00}$ or $\mathrm{castToBool}(\mathit{rest})$. Equivalently: some byte other than the last is non-zero, or the last byte is neither $\mathtt{0x00}$ nor $\mathtt{0x80}$.

## The right-hand side: `FundingSpend`

$$
\mathrm{FundingSpend}(f,o,k_1,k_2,st)\ :\Longleftrightarrow\
\exists\, s_1,s_2,d\in\mathsf{Bytes}:\ st=[\,s_2,\,s_1,\,d\,]\ \wedge\ o.\mathrm{checkSig}(s_1,k_1)=\mathrm{some}\,\mathrm{true}\ \wedge\ o.\mathrm{checkSig}(s_2,k_2)=\mathrm{some}\,\mathrm{true}\ \wedge\ \big(f.\mathrm{nulldummy}=\mathrm{true}\Rightarrow d=[\,]\big).
$$

That is: $st$ has exactly three elements — top $s_2$, then $s_1$, then $d$ at the bottom (so for any $st$ of length $\ne3$ the right-hand side is false); $s_1$ paired with $k_1$ and $s_2$ paired with $k_2$ both receive the verdict $\mathrm{some}\,\mathrm{true}$ from the oracle (a verdict of $\mathrm{none}$ or $\mathrm{some}\,\mathrm{false}$ for either pair falsifies it); and if $f.\mathrm{nulldummy}$ is true then $d$ is the empty byte string, while if it is false $d$ is arbitrary. No lengths of $s_1,s_2,d$ are constrained; $f.\mathrm{cltv}$, $f.\mathrm{csv}$ and the oracle's hash and lock-time fields are not consulted.

## The script

$$
\mathrm{fundingScript}(k_1,k_2) = \big[\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{push}(k_1),\ \mathrm{push}(k_2),\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{op}(\mathtt{0xae})\ \big],
$$

where $\mathrm{op}(\mathtt{0x52})$ is $\mathrm{numInstr}(2)$ (for $n=-1$ or $1\le n\le16$, $\mathrm{numInstr}(n)=\mathrm{op}(n+\mathtt{0x50})$; otherwise a push of the script-number encoding of $n$), $\mathrm{push}(x)$ is a data push, and $\mathtt{0xae}$ is `OP_CHECKMULTISIG`.

## The left-hand side: the interpreter `evalScript`

$\mathrm{evalScript}(f,o,st_0,S)$ is $\mathrm{none}$ (failure) or $\mathrm{some}(st)$ for a stack $st$. The machine state is (main stack, alternate stack, condition stack $\mathit{vfExec}$ — a list of booleans —, opcode counter), initially $(st_0,[\,],[\,],0)$. The instructions of $S$ are run in order by the one-step rule below; any failure makes the whole result $\mathrm{none}$. After the last instruction the run fails if $\mathit{vfExec}$ is non-empty; otherwise the result is $\mathrm{some}$ of the final main stack.

One step:

- $\mathrm{push}(x)$: fail if $|x|>520$. Otherwise, if every entry of $\mathit{vfExec}$ is $\mathrm{true}$ (vacuously so when empty), $x$ is placed on top of the main stack; else the state is unchanged. Then fail if $|\text{main}|+|\text{alt}|>1000$.
- $\mathrm{op}(c)$: *counted* iff $c>\mathtt{0x60}$. If counted and counter$+1>201$: fail; else if counted, increment the counter. Fail if $c$ is one of the fifteen disabled opcodes ($\mathtt{0x7e}$–$\mathtt{0x81}$, $\mathtt{0x83}$–$\mathtt{0x86}$, $\mathtt{0x8d}$, $\mathtt{0x8e}$, $\mathtt{0x95}$–$\mathtt{0x99}$). Then, if every entry of $\mathit{vfExec}$ is true or $\mathtt{0x63}\le c\le\mathtt{0x68}$: apply the one-opcode executor (fail if it fails), then fail if $|\text{main}|+|\text{alt}|>1000$; otherwise skip the opcode (same size check).

The one-opcode executor on the two opcodes occurring in the funding script (other branches not reproduced):

- $c=\mathtt{0x52}$ (branch for $c=\mathtt{0x4f}$ or $\mathtt{0x51}\le c\le\mathtt{0x60}$; not counted): push $\mathrm{serialize}(c-\mathtt{0x50})$, where $\mathrm{serialize}(n)$ is $[\,]$ for $n=0$ and otherwise the little-endian bytes of $|n|$ without trailing zeros, plus an extra byte $\mathtt{0x80}$/$\mathtt{0x00}$ (negative/positive) if the top bit of the last magnitude byte is set, or else the top bit of the last byte set when $n<0$. For $\mathtt{0x52}$ this pushes $[\mathtt{0x02}]$.
- $c=\mathtt{0xae}$ (`OP_CHECKMULTISIG`; counted). With main stack $st$ and the already-incremented counter $\kappa$:
  1. Fail if $st=[\,]$. Else $st=n_k::r$.
  2. $N_k:=\mathrm{toNum}(n_k)$: fail if $|n_k|>4$; otherwise the signed little-endian value of $n_k$ (sign = top bit of last byte, magnitude = little-endian value with that bit cleared; empty string $=0$). Fail if $N_k<0$ or $N_k>20$.
  3. $\kappa':=\kappa+N_k$; fail if $\kappa'>201$.
  4. $\mathit{keys}:=$ first $N_k$ entries of $r$, $r:=$ rest; fail if fewer than $N_k$ were available.
  5. Fail if $r=[\,]$; else $r=n_s::r$. $N_s:=\mathrm{toNum}(n_s)$ (fail if $|n_s|>4$); fail if $N_s<0$ or $N_s>N_k$.
  6. $\mathit{sigs}:=$ first $N_s$ entries of $r$, $r:=$ rest; fail if fewer than $N_s$ were available.
  7. $\mathrm{multisigLoop}(o,\mathit{sigs},\mathit{keys})$ (below): fail if $\mathrm{none}$; else let $ok$ be its boolean.
  8. Fail if $r=[\,]$; else $r=d'::r'$. Fail if $f.\mathrm{nulldummy}=\mathrm{true}$ and $d'\ne[\,]$.
  9. New main stack $\mathrm{boolBytes}(ok)::r'$ with $\mathrm{boolBytes}(\mathrm{true})=[\mathtt{0x01}]$, $\mathrm{boolBytes}(\mathrm{false})=[\,]$; counter $\kappa'$.

$\mathrm{multisigLoop}(o,\mathit{sigs},\mathit{keys})$, both lists top-first:

- $\mathit{sigs}=[\,]$: $\mathrm{some}\,\mathrm{true}$ (whatever $\mathit{keys}$ is).
- $\mathit{sigs}\ne[\,]$, $\mathit{keys}=[\,]$: $\mathrm{some}\,\mathrm{false}$.
- $\mathit{sigs}=s::\mathit{sigs}'$, $\mathit{keys}=k::\mathit{keys}'$: evaluate $o.\mathrm{checkSig}(s,k)$. $\mathrm{none}\Rightarrow\mathrm{none}$. $\mathrm{some}\,\mathrm{true}\Rightarrow$ if $|\mathit{keys}'|<|\mathit{sigs}'|$ then $\mathrm{some}\,\mathrm{false}$ else $\mathrm{multisigLoop}(o,\mathit{sigs}',\mathit{keys}')$ (both consumed). $\mathrm{some}\,\mathrm{false}\Rightarrow$ if $|\mathit{keys}'|<|\mathit{sigs}|$ then $\mathrm{some}\,\mathrm{false}$ else $\mathrm{multisigLoop}(o,\mathit{sigs},\mathit{keys}')$ (only the key consumed; the same signature is retried against the next key). The top signature is thus tried against the top key first.

## What the quantification silently includes

- $st$ ranges over all stacks, including the empty stack, stacks with fewer or more than three elements, and stacks whose elements exceed $520$ bytes (the interpreter checks the $520$-byte bound only on data *pushed by the script*, i.e. $k_1,k_2$, not on the initial stack; the $1000$-element bound applies to the whole stack at every step).
- $k_1,k_2$ are arbitrary byte strings of length at most $520$; no public-key format is required.
- The oracle is arbitrary; in particular $o.\mathrm{checkSig}$ may return $\mathrm{none}$ on any pair, and the theorem's two sides refer to the same $o$.
- The flags $f.\mathrm{cltv}$ and $f.\mathrm{csv}$ are quantified over but are not consulted by either side.
