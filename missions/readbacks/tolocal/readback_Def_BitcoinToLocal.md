# Read-back: `Def_BitcoinToLocal.lean`

Throughout, a *byte* is an 8-bit word, a *byte string* is a finite list of bytes, and $|x|$ denotes the length of a list $x$. Stacks are lists written top-first. Bitwise operations $\mathbin{\&}$, $\mid$ act on natural numbers. Integer-to-natural truncation $\operatorname{toNat}(z)$ sends every negative integer to $0$ and fixes non-negative ones. Several notions from the preamble are unfolded where first used.

---

## 1. `numInstr`

For an integer $n$, $\mathrm{numInstr}(n)$ is a single parsed script instruction (an instruction is either a *data push* carrying a byte string, or a *non-push opcode* carrying one byte), defined by cases:

- if $n = -1$, or $1 \le n \le 16$, it is the **opcode** whose byte is $\operatorname{toNat}(n + 80)$ reduced modulo $256$ (the constant $80$ is $\mathtt{0x51} - 1$, where $\mathtt{0x51} = 81$ is the byte called `OP_1`). Concretely this is byte $\mathtt{0x4f}$ ($=79$) for $n=-1$ and bytes $\mathtt{0x51},\dots,\mathtt{0x60}$ ($=81,\dots,96$) for $n = 1,\dots,16$; no truncation or modular reduction actually occurs in this branch;
- otherwise (so for $n = 0$, $n \le -2$, or $n \ge 17$), it is the **data push** of $\mathrm{serialize}(n)$.

Here $\mathrm{serialize} : \mathbb{Z} \to$ byte strings is the following encoding: $\mathrm{serialize}(0) = [\,]$ (the empty string). For $v \ne 0$ let $m$ be the little-endian base-$256$ digit list of $|v|$ with no trailing zero bytes (so $m$ is non-empty and its last byte is non-zero). If the last byte of $m$ has its $\mathtt{0x80}$ bit set, the result is $m$ followed by one extra byte, $\mathtt{0x80}$ if $v<0$ and $\mathtt{0x00}$ if $v>0$; otherwise, if $v<0$ the result is $m$ with the $\mathtt{0x80}$ bit set on its last byte, and if $v>0$ the result is $m$ itself. In particular $\mathrm{numInstr}(0)$ is a push of the **empty** byte string.

## 2. `numBytes`

For an integer $n$, $\mathrm{numBytes}(n)$ is a byte string:

- if $n = -1$ or $1 \le n \le 16$, the one-byte string $[\operatorname{toNat}(n+80) \bmod 256]$, i.e. $[\mathtt{0x4f}]$ for $n=-1$ and $[\mathtt{0x51}],\dots,[\mathtt{0x60}]$ for $n=1,\dots,16$;
- otherwise $\mathrm{pushBytes}(\mathrm{serialize}(n))$.

Here $\mathrm{pushBytes}(d)$, for a byte string $d$, is: if $|d| < 76$ ($\mathtt{0x4c}$), the byte $|d|$ followed by $d$; else if $|d| \le 255$, the bytes $\mathtt{0x4c}, |d|$ followed by $d$; else if $|d| \le 65535$, the byte $\mathtt{0x4d}$, then the two-byte little-endian encoding of $|d|$, then $d$; otherwise the byte $\mathtt{0x4e}$, the four-byte little-endian encoding of $|d|$, then $d$. In particular $\mathrm{numBytes}(0) = \mathrm{pushBytes}([\,]) = [\mathtt{0x00}]$.

## 3. `toLocalScript`

For byte strings $R$ (named `revocationPubkey`) and $D$ (named `localDelayedPubkey`) and an integer $d$ (named `toSelfDelay`), $\mathrm{toLocalScript}(R, d, D)$ is the following list of exactly nine instructions, in this order:

$$
\big[\ \mathrm{op}\,\mathtt{0x63},\ \ \mathrm{push}\,R,\ \ \mathrm{op}\,\mathtt{0x67},\ \ \mathrm{numInstr}(d),\ \ \mathrm{op}\,\mathtt{0xb2},\ \ \mathrm{op}\,\mathtt{0x75},\ \ \mathrm{push}\,D,\ \ \mathrm{op}\,\mathtt{0x68},\ \ \mathrm{op}\,\mathtt{0xac}\ \big]
$$

where the opcode bytes are named in the preamble `OP_IF` ($\mathtt{0x63}$), `OP_ELSE` ($\mathtt{0x67}$), `OP_CHECKSEQUENCEVERIFY` ($\mathtt{0xb2}$), `OP_DROP` ($\mathtt{0x75}$), `OP_ENDIF` ($\mathtt{0x68}$), `OP_CHECKSIG` ($\mathtt{0xac}$). No restriction is placed on $|R|$, $|D|$, or $d$ by this definition; the fourth instruction is an opcode when $d \in \{-1, 1, \dots, 16\}$ and a data push of $\mathrm{serialize}(d)$ otherwise (the empty push when $d = 0$).

## 4. `toLocalBytes`

For $R$, $d$, $D$ as above, $\mathrm{toLocalBytes}(R, d, D)$ is the byte string obtained by concatenation:

$$
[\mathtt{0x63}] \mathbin{+\!\!+} \mathrm{pushBytes}(R) \mathbin{+\!\!+} [\mathtt{0x67}] \mathbin{+\!\!+} \mathrm{numBytes}(d) \mathbin{+\!\!+} [\mathtt{0xb2}, \mathtt{0x75}] \mathbin{+\!\!+} \mathrm{pushBytes}(D) \mathbin{+\!\!+} [\mathtt{0x68}, \mathtt{0xac}],
$$

with $\mathrm{pushBytes}$ and $\mathrm{numBytes}$ as unfolded above. Again there is no restriction on $R$, $D$, $d$; for $|R|$ or $|D|$ above $75$ the push prefix becomes the two-byte ($\mathtt{0x4c}$) or longer forms.

## 5. `CsvPasses`

Let $f$ be a *flag record* — a triple of booleans $(f.\mathrm{cltv}, f.\mathrm{csv}, f.\mathrm{nulldummy})$ — and let $o$ be an *oracle*: a record of eight arbitrary functions, five hash functions $\mathrm{ripemd160}, \mathrm{sha1}, \mathrm{sha256}, \mathrm{hash160}, \mathrm{hash256}$ from byte strings to byte strings, a function $o.\mathrm{checkSig}$ from two byte strings (signature first, public key second) to an optional boolean (either "none" or "some $b$" with $b$ a boolean), $o.\mathrm{checkLockTime} : \mathbb{Z} \to \mathrm{Bool}$ and $o.\mathrm{checkSequence} : \mathbb{Z} \to \mathrm{Bool}$. Nothing is assumed about these functions. For an integer $\delta$ (named `delay`), the proposition $\mathrm{CsvPasses}(f, o, \delta)$ is

$$
f.\mathrm{csv} = \mathrm{false}\ \ \lor\ \ \Big( 0 \le \delta\ \land\ \big( (\operatorname{toNat}(\delta) \mathbin{\&} 2^{31}) \ne 0\ \ \lor\ \ o.\mathrm{checkSequence}(\delta) = \mathrm{true} \big) \Big),
$$

where $2^{31} = 2147483648$ is the constant the preamble calls `SEQUENCE_LOCKTIME_DISABLE_FLAG` (the script-layer copy of it). Edge cases: when $f.\mathrm{csv} = \mathrm{false}$ the proposition holds for every $\delta$, negative or not, whatever $o$ is; when $f.\mathrm{csv} = \mathrm{true}$ every negative $\delta$ fails it (the truncation $\operatorname{toNat}$ is never evaluated on a negative in a way that matters, because of the guard $0 \le \delta$); when $f.\mathrm{csv} = \mathrm{true}$ and $\delta \ge 0$ has bit $31$ set, it holds regardless of $o.\mathrm{checkSequence}$; otherwise it holds exactly when $o.\mathrm{checkSequence}(\delta) = \mathrm{true}$.

## 6. Decidability instance for `CsvPasses`

For every $f$, $o$, $\delta$ the proposition $\mathrm{CsvPasses}(f, o, \delta)$ is given a decision procedure (obtained by unfolding the definition and combining the decidability of boolean equality, integer order, natural-number disequality, and the connectives). This declaration asserts nothing mathematical beyond that; it is what allows later statements to write "if $\mathrm{CsvPasses}(f,o,\delta)$ then $\dots$ else $\dots$" as a computable branch.

## 7. `SpendCondition`

For a flag record $f$, an oracle $o$, byte strings $R$ (`revocationPubkey`), $D$ (`localDelayedPubkey`), an integer $d$ (`toSelfDelay`), and two further byte strings $b$ and $\mathrm{sig}$, the proposition $\mathrm{SpendCondition}(f, o, R, d, D, b, \mathrm{sig})$ is the disjunction

$$
\big( \mathrm{castToBool}(b) = \mathrm{true}\ \land\ o.\mathrm{checkSig}(\mathrm{sig}, R) = \mathrm{some}\,\mathrm{true} \big)
\ \ \lor\ \
\big( \mathrm{castToBool}(b) = \mathrm{false}\ \land\ \mathrm{CsvPasses}(f, o, d)\ \land\ o.\mathrm{checkSig}(\mathrm{sig}, D) = \mathrm{some}\,\mathrm{true} \big).
$$

Here $\mathrm{castToBool}$ of a byte string is: $\mathrm{false}$ for the empty string; for a one-byte string $[x]$, true iff $x \ne 0$ and $x \ne \mathtt{0x80}$; for a string $x :: \mathrm{rest}$ with $\mathrm{rest}$ non-empty, true iff $x \ne 0$ or $\mathrm{castToBool}(\mathrm{rest})$. Equivalently, some byte is non-zero, except that a string whose only non-zero byte is its last byte and that byte equals $\mathtt{0x80}$ is false. The two disjuncts are mutually exclusive since $\mathrm{castToBool}(b)$ is a single boolean. In both disjuncts the oracle's signature check must return exactly $\mathrm{some}\,\mathrm{true}$: the outcomes "none" and "$\mathrm{some}\,\mathrm{false}$" both fail the condition. $\mathrm{CsvPasses}$ is as in item 5; note it is trivially satisfied when $f.\mathrm{csv} = \mathrm{false}$.

## 8. `inputSequence`

A *transaction* $\mathrm{tx}$ is a record with fields $\mathrm{version} \in \mathbb{N}$, $\mathrm{vin}$ (a list of inputs), $\mathrm{vout}$ (a list of outputs) and $\mathrm{nLockTime} \in \mathbb{N}$; an *input* is a record with fields $\mathrm{prevout}$ (a pair of a byte string and a natural), $\mathrm{scriptSig}$ (a byte string), $\mathrm{nSequence} \in \mathbb{N}$, and $\mathrm{witness}$ (a list of byte strings). No upper bound on $\mathrm{version}$ or $\mathrm{nSequence}$ is imposed by these types. For a transaction $\mathrm{tx}$ and a natural $n_{\mathrm{in}}$,

$$
\mathrm{inputSequence}(\mathrm{tx}, n_{\mathrm{in}}) = \big(\mathrm{tx}.\mathrm{vin}[n_{\mathrm{in}}]\big).\mathrm{nSequence},
$$

the sequence number of the $n_{\mathrm{in}}$-th input (zero-indexed), where if $n_{\mathrm{in}} \ge |\mathrm{tx}.\mathrm{vin}|$ the "default input" $(([\,],0), [\,], 0, [\,])$ is used instead, so the value is $0$ in that out-of-range case.
