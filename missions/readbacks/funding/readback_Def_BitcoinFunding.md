# Read-back: `Def_BitcoinFunding.lean`

Throughout, a **byte** is an 8-bit word and a **byte string** is a finite list of bytes (written $\mathsf{Bytes}$). A **stack** is a finite list of byte strings whose *first* entry is the top of the stack. The file contains three definitions, read back below in order.

---

## Definition 1: `fundingScript`

For any two byte strings $k_1, k_2$ (called `pubkey1`, `pubkey2`; they are completely unconstrained byte strings — any length, including empty, any contents), $\mathrm{fundingScript}(k_1,k_2)$ is the following list of five *parsed script instructions*:

$$
\mathrm{fundingScript}(k_1,k_2) \;=\; \big[\ \mathrm{numInstr}(2),\ \mathrm{push}(k_1),\ \mathrm{push}(k_2),\ \mathrm{numInstr}(2),\ \mathrm{op}(\mathtt{0xae})\ \big].
$$

Here an instruction is either $\mathrm{push}(d)$ (a data push carrying the byte string $d$) or $\mathrm{op}(c)$ (a non-push opcode given by its byte $c$); $\mathtt{0xae}$ is the byte named `OP_CHECKMULTISIG`. The preamble's $\mathrm{numInstr}(n)$, for an integer $n$, is defined as: if $n = -1$ or $1 \le n \le 16$, then the opcode instruction $\mathrm{op}\big(n + \mathtt{0x50}\big)$ (as an 8-bit byte), otherwise the push $\mathrm{push}(\mathrm{serialize}(n))$ of the script-number encoding of $n$. For $n = 2$ the first case applies, so $\mathrm{numInstr}(2) = \mathrm{op}(\mathtt{0x52})$ (the byte usually called `OP_2`). Hence, concretely,

$$
\mathrm{fundingScript}(k_1,k_2) \;=\; \big[\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{push}(k_1),\ \mathrm{push}(k_2),\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{op}(\mathtt{0xae})\ \big].
$$

Note that two scripts are equal exactly when their instruction lists are equal entrywise, where $\mathrm{push}(d) = \mathrm{push}(d')$ iff $d = d'$ as byte strings; a push of a byte string of length $0$ is a legitimate instruction.

---

## Definition 2: `fundingBytes`

For any two byte strings $k_1, k_2$ (again unconstrained), $\mathrm{fundingBytes}(k_1,k_2)$ is the byte string obtained by concatenation:

$$
\mathrm{fundingBytes}(k_1,k_2) \;=\; \mathrm{numBytes}(2)\ \|\ \mathrm{pushBytes}(k_1)\ \|\ \mathrm{pushBytes}(k_2)\ \|\ \mathrm{numBytes}(2)\ \|\ [\mathtt{0xae}].
$$

The preamble's $\mathrm{numBytes}(n)$ is: if $n=-1$ or $1\le n\le 16$ then the single byte $[\,n+\mathtt{0x50}\,]$, otherwise $\mathrm{pushBytes}(\mathrm{serialize}(n))$. So $\mathrm{numBytes}(2) = [\mathtt{0x52}]$.

The preamble's $\mathrm{pushBytes}(d)$, for a byte string $d$ of length $\ell = |d|$, is the canonical push encoding:

- if $\ell < 76$ ($=\mathtt{0x4c}$): the single byte $\ell$ followed by $d$;
- else if $\ell \le 255$: the two bytes $\mathtt{0x4c},\ \ell$ followed by $d$;
- else if $\ell \le 65535$: the byte $\mathtt{0x4d}$, then $\ell$ as 2 little-endian bytes, then $d$;
- else: the byte $\mathtt{0x4e}$, then $\ell$ as 4 little-endian bytes (reduced modulo $2^{32}$), then $d$.

(In the first two cases the length byte is $\ell$ reduced modulo $256$, which is $\ell$ itself there.) In particular, for an empty $d$, $\mathrm{pushBytes}([\,]) = [\mathtt{0x00}]$.

Concretely,
$$
\mathrm{fundingBytes}(k_1,k_2) = [\mathtt{0x52}]\ \|\ \mathrm{pushBytes}(k_1)\ \|\ \mathrm{pushBytes}(k_2)\ \|\ [\mathtt{0x52},\ \mathtt{0xae}].
$$
Nothing in this definition bounds $|k_1|$ or $|k_2|$.

---

## Definition 3: `FundingSpend`

This is a proposition (a truth value, not a computation) depending on:

- a flag record $f$ of type $\mathsf{Flags}$, which consists of exactly three booleans $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$ (only the last is consulted here);
- an **oracle** $o$: a record of abstract functions $o.\mathrm{ripemd160}, o.\mathrm{sha1}, o.\mathrm{sha256}, o.\mathrm{hash160}, o.\mathrm{hash256} : \mathsf{Bytes}\to\mathsf{Bytes}$, a function $o.\mathrm{checkSig} : \mathsf{Bytes}\times\mathsf{Bytes} \to \mathrm{Option}(\mathrm{Bool})$ (first argument a "signature" byte string, second a "public key" byte string; its value is one of $\mathrm{none}$, $\mathrm{some}\,\mathrm{true}$, $\mathrm{some}\,\mathrm{false}$), and $o.\mathrm{checkLockTime}, o.\mathrm{checkSequence} : \mathbb{Z}\to\mathrm{Bool}$. The oracle is a free parameter: nothing in this definition says what any of its fields compute;
- two byte strings $k_1, k_2$ (`pubkey1`, `pubkey2`), unconstrained;
- a stack $st$ (a list of byte strings, top first), unconstrained.

$\mathrm{FundingSpend}(f, o, k_1, k_2, st)$ holds if and only if

$$
\exists\, s_1, s_2, d \in \mathsf{Bytes}:\quad
st = [\,s_2,\ s_1,\ d\,]
\ \wedge\ o.\mathrm{checkSig}(s_1, k_1) = \mathrm{some}\,\mathrm{true}
\ \wedge\ o.\mathrm{checkSig}(s_2, k_2) = \mathrm{some}\,\mathrm{true}
\ \wedge\ \big(f.\mathrm{nulldummy} = \mathrm{true} \;\Rightarrow\; d = [\,]\big).
$$

Spelled out:

- $st$ must have **exactly three** entries; the top entry is $s_2$, the second is $s_1$, the bottom is $d$. A stack of any other length (including the empty stack) never satisfies $\mathrm{FundingSpend}$.
- $s_1$ is paired with $k_1$ and $s_2$ with $k_2$; both oracle calls must return precisely $\mathrm{some}\,\mathrm{true}$. A return value of $\mathrm{none}$ or $\mathrm{some}\,\mathrm{false}$ for either pair makes the proposition false.
- If $f.\mathrm{nulldummy}$ is $\mathrm{true}$, $d$ must be the empty byte string; if $f.\mathrm{nulldummy}$ is $\mathrm{false}$, $d$ is arbitrary.
- No length bound is imposed on $s_1$, $s_2$, $d$, $k_1$ or $k_2$ by this definition; $f.\mathrm{cltv}$ and $f.\mathrm{csv}$ play no role; and no hash function of the oracle is consulted.
