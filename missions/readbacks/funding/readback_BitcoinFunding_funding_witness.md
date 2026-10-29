# Read-back: `BitcoinFunding.funding_witness`

A **byte** is an 8-bit word; a **byte string** ($\mathsf{Bytes}$) is a finite list of bytes; a **stack** is a finite list of byte strings whose first entry is the top.

## Statement

The theorem quantifies over:

- a flag record $f$ with exactly three boolean fields $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$;
- an **oracle** $o$: a record of abstract functions $o.\mathrm{ripemd160}, o.\mathrm{sha1}, o.\mathrm{sha256}, o.\mathrm{hash160}, o.\mathrm{hash256} : \mathsf{Bytes}\to\mathsf{Bytes}$; $o.\mathrm{checkSig} : \mathsf{Bytes}\times\mathsf{Bytes}\to\mathrm{Option}(\mathrm{Bool})$ (first argument "signature", second "public key"; value $\mathrm{none}$, $\mathrm{some}\,\mathrm{true}$ or $\mathrm{some}\,\mathrm{false}$); $o.\mathrm{checkLockTime}, o.\mathrm{checkSequence}:\mathbb{Z}\to\mathrm{Bool}$. Nothing is assumed about any of these functions;
- five byte strings $k_1, k_2, s_1, s_2, d$ (`pubkey1`, `pubkey2`, `sig1`, `sig2`, `dummy`), unconstrained in content;

and assumes the two hypotheses $|k_1|\le 520$ and $|k_2|\le 520$ ($520$ = `MAX_SCRIPT_ELEMENT_SIZE`). **No bound is placed on $|s_1|$, $|s_2|$ or $|d|$.**

Under these, the theorem asserts an equality of two values in $\mathrm{Option}(\text{stack})$:

$$
\mathrm{evalScript}\big(f,\ o,\ [\,s_2,\ s_1,\ d\,],\ \mathrm{fundingScript}(k_1,k_2)\big)
\;=\;
\begin{cases}
\mathrm{none} & \text{if } \mathrm{multisigLoop}(o,[s_2,s_1],[k_2,k_1]) = \mathrm{none},\\[2pt]
\mathrm{none} & \text{if } \mathrm{multisigLoop}(o,[s_2,s_1],[k_2,k_1]) = \mathrm{some}(ok) \text{ and } f.\mathrm{nulldummy}=\mathrm{true} \text{ and } d\neq[\,],\\[2pt]
\mathrm{some}\,[\,\mathrm{boolBytes}(ok)\,] & \text{if } \mathrm{multisigLoop}(o,[s_2,s_1],[k_2,k_1]) = \mathrm{some}(ok) \text{ otherwise,}
\end{cases}
$$

where $\mathrm{boolBytes}(\mathrm{true}) = [\mathtt{0x01}]$ and $\mathrm{boolBytes}(\mathrm{false}) = [\,]$ (the empty byte string). The initial stack on the left has $s_2$ on top, $s_1$ beneath it, and $d$ at the bottom. On the right, the result stack (when not $\mathrm{none}$) has exactly one element, either $[\mathtt{0x01}]$ or $[\,]$.

## The script

$$
\mathrm{fundingScript}(k_1,k_2) = \big[\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{push}(k_1),\ \mathrm{push}(k_2),\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{op}(\mathtt{0xae})\ \big],
$$

where $\mathrm{op}(\mathtt{0x52})$ is $\mathrm{numInstr}(2)$ (for $n=-1$ or $1\le n\le16$, $\mathrm{numInstr}(n)=\mathrm{op}(n+\mathtt{0x50})$; otherwise a push of the script-number encoding of $n$) and $\mathtt{0xae}$ is `OP_CHECKMULTISIG`.

## The right-hand side: `multisigLoop`

$\mathrm{multisigLoop}(o, \mathit{sigs}, \mathit{keys})$, with both lists top-first, is defined by:

- $\mathit{sigs}=[\,]$: $\mathrm{some}\,\mathrm{true}$ (whatever $\mathit{keys}$ is).
- $\mathit{sigs}\ne[\,]$ and $\mathit{keys}=[\,]$: $\mathrm{some}\,\mathrm{false}$.
- $\mathit{sigs}=s::\mathit{sigs}'$ and $\mathit{keys}=k::\mathit{keys}'$: compute $o.\mathrm{checkSig}(s,k)$:
  - $\mathrm{none}$ $\Rightarrow$ result $\mathrm{none}$;
  - $\mathrm{some}\,\mathrm{true}$ $\Rightarrow$ if $|\mathit{keys}'|<|\mathit{sigs}'|$ then $\mathrm{some}\,\mathrm{false}$, else $\mathrm{multisigLoop}(o,\mathit{sigs}',\mathit{keys}')$ (both the signature and the key are consumed);
  - $\mathrm{some}\,\mathrm{false}$ $\Rightarrow$ if $|\mathit{keys}'|<|\mathit{sigs}|$ then $\mathrm{some}\,\mathrm{false}$, else $\mathrm{multisigLoop}(o,\mathit{sigs},\mathit{keys}')$ (only the key is consumed; the same signature is retried against the next key).

Applied to $\mathit{sigs}=[s_2,s_1]$ and $\mathit{keys}=[k_2,k_1]$, the definition unrolls as follows. First $o.\mathrm{checkSig}(s_2,k_2)$ is evaluated:

- if $\mathrm{none}$: the loop returns $\mathrm{none}$;
- if $\mathrm{some}\,\mathrm{false}$: the remaining keys $[k_1]$ number $1 < 2 = |[s_2,s_1]|$, so the loop returns $\mathrm{some}\,\mathrm{false}$ — $s_2$ is **not** retried against $k_1$, and $s_1$ is never examined;
- if $\mathrm{some}\,\mathrm{true}$: since $|[k_1]| = 1 \not< 1 = |[s_1]|$, the loop continues with $([s_1],[k_1])$ and evaluates $o.\mathrm{checkSig}(s_1,k_1)$: $\mathrm{none}\Rightarrow\mathrm{none}$; $\mathrm{some}\,\mathrm{false}\Rightarrow$ ($0<1$) $\mathrm{some}\,\mathrm{false}$; $\mathrm{some}\,\mathrm{true}\Rightarrow$ ($0\not<0$) continue with $([\,],[\,])$, which is $\mathrm{some}\,\mathrm{true}$.

So the loop is $\mathrm{some}\,\mathrm{true}$ iff $o.\mathrm{checkSig}(s_2,k_2)=\mathrm{some}\,\mathrm{true}$ and $o.\mathrm{checkSig}(s_1,k_1)=\mathrm{some}\,\mathrm{true}$; it is $\mathrm{none}$ iff $o.\mathrm{checkSig}(s_2,k_2)=\mathrm{none}$, or $o.\mathrm{checkSig}(s_2,k_2)=\mathrm{some}\,\mathrm{true}$ and $o.\mathrm{checkSig}(s_1,k_1)=\mathrm{none}$; and $\mathrm{some}\,\mathrm{false}$ in the remaining cases. The pairing is: the top signature $s_2$ with the top key $k_2$; the second signature $s_1$ with the second key $k_1$. The *order* of evaluation is $s_2$ against $k_2$ first.

The outer `match` on the right-hand side then returns $\mathrm{none}$ when the loop is $\mathrm{none}$; otherwise, with the loop's boolean $ok$, it returns $\mathrm{none}$ if $f.\mathrm{nulldummy}$ is true **and** $d$ is non-empty, and $\mathrm{some}\,[\mathrm{boolBytes}(ok)]$ otherwise. When $f.\mathrm{nulldummy}$ is false, $d$ is never inspected on the right-hand side; when it is true, a non-empty $d$ yields $\mathrm{none}$ even if $ok=\mathrm{false}$.

## The left-hand side: the interpreter `evalScript`

$\mathrm{evalScript}(f,o,st_0,S)$ is $\mathrm{none}$ (failure) or $\mathrm{some}(st)$ for a stack $st$. The machine state is a tuple (main stack, alternate stack, condition stack $\mathit{vfExec}$ — a list of booleans — , opcode counter), initially $(st_0,[\,],[\,],0)$. The instructions of $S$ are run in order by the one-step rule below; any failure makes the whole result $\mathrm{none}$. After the last instruction, the run fails if $\mathit{vfExec}$ is non-empty; otherwise the result is $\mathrm{some}$ of the final main stack (the alternate stack and counter are discarded).

One step:

- $\mathrm{push}(x)$: fail if $|x|>520$. Otherwise, if every entry of $\mathit{vfExec}$ is $\mathrm{true}$ (vacuously true when $\mathit{vfExec}$ is empty), $x$ is placed on top of the main stack; else the state is unchanged. Then fail if $|\text{main}|+|\text{alt}|>1000$.
- $\mathrm{op}(c)$: the opcode is *counted* iff $c>\mathtt{0x60}$. If counted and counter$+1>201$: fail; else if counted, the counter is incremented. Fail if $c$ is one of the fifteen disabled opcodes ($\mathtt{0x7e}$–$\mathtt{0x81}$, $\mathtt{0x83}$–$\mathtt{0x86}$, $\mathtt{0x8d}$, $\mathtt{0x8e}$, $\mathtt{0x95}$–$\mathtt{0x99}$). Then, if every entry of $\mathit{vfExec}$ is true or $\mathtt{0x63}\le c\le\mathtt{0x68}$: apply the one-opcode executor $\mathrm{execOp}$ (fail if it fails), then fail if $|\text{main}|+|\text{alt}|>1000$; otherwise skip the opcode (same size check).

The one-opcode executor on the two opcodes occurring in the funding script (its branches for other opcodes are not reproduced):

- $c=\mathtt{0x52}$ (branch for $c=\mathtt{0x4f}$ or $\mathtt{0x51}\le c\le\mathtt{0x60}$; not counted): push $\mathrm{serialize}(c-\mathtt{0x50})$ onto the main stack, where $\mathrm{serialize}(n)$ is $[\,]$ for $n=0$, and otherwise the little-endian bytes of $|n|$ without trailing zero bytes, followed by an extra byte $\mathtt{0x80}$ (if $n<0$) or $\mathtt{0x00}$ (if $n>0$) when the top bit of the last magnitude byte is set, or else with the top bit of the last byte set when $n<0$. For $\mathtt{0x52}$ this pushes $[\mathtt{0x02}]$.
- $c=\mathtt{0xae}$ (`OP_CHECKMULTISIG`; counted). With main stack $st$ and the already-incremented counter $\kappa$:
  1. Fail if $st=[\,]$. Else $st=n_k::r$.
  2. $N_k:=\mathrm{toNum}(n_k)$: fail if $|n_k|>4$; otherwise $N_k$ is the signed little-endian value of $n_k$ (sign bit = top bit of the last byte; magnitude = little-endian value with that bit cleared; the empty string is $0$). Fail if $N_k<0$ or $N_k>20$.
  3. $\kappa':=\kappa+N_k$; fail if $\kappa'>201$.
  4. $\mathit{keys}:=$ the first $N_k$ entries of $r$, $r:=$ the rest; fail if fewer than $N_k$ entries were available.
  5. Fail if $r=[\,]$; else $r=n_s::r$. $N_s:=\mathrm{toNum}(n_s)$ (fail if $|n_s|>4$); fail if $N_s<0$ or $N_s>N_k$.
  6. $\mathit{sigs}:=$ the first $N_s$ entries of $r$, $r:=$ the rest; fail if fewer than $N_s$ were available.
  7. Compute $\mathrm{multisigLoop}(o,\mathit{sigs},\mathit{keys})$ (defined above): fail if $\mathrm{none}$; else let $ok$ be its boolean.
  8. Fail if $r=[\,]$; else $r=d'::r'$. Fail if $f.\mathrm{nulldummy}=\mathrm{true}$ and $d'\ne[\,]$.
  9. New main stack $\mathrm{boolBytes}(ok)::r'$, counter $\kappa'$.

The left-hand side of the theorem is this interpreter run on the initial main stack $[s_2,s_1,d]$ over the five instructions $\mathrm{op}(\mathtt{0x52}),\ \mathrm{push}(k_1),\ \mathrm{push}(k_2),\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{op}(\mathtt{0xae})$, with the flags $f$ and the oracle $o$. Note that the interpreter imposes the $520$-byte bound only on *pushed* data (here $k_1,k_2$, which the hypotheses already bound) and not on the elements $s_2,s_1,d$ of the initial stack; that only $f.\mathrm{nulldummy}$ among the flags is consulted by these opcodes; and that only $o.\mathrm{checkSig}$ among the oracle's fields is consulted by them.
