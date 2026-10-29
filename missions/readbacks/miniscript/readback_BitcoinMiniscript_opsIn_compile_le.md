# Read-back: `BitcoinMiniscript.opsIn_compile_le`

**Statement.** For **every** fragment $m$ (no typing hypothesis), the number of counted opcodes in the compiled script is at most the static bound:
$$\mathrm{opsIn}(\mathrm{compile}(m)) \le \mathrm{opsMax}(m),$$
where $\mathrm{opsIn}$ counts the instructions $\mathrm{op}(c)$ with $c > \mathtt{0x60}$ (pushes, and the opcodes `OP_1NEGATE`, `OP_1`…`OP_16` produced by $\mathrm{numInstr}$, are not counted). This is a purely static count of the script; it does not include the extra per-key amount that `OP_CHECKMULTISIG` adds to the counter at run time, and it is an inequality, not an equality.

## Definitions used in the statement, unfolded

### Basic data (from the script-interpreter preamble)

**Byte strings, stacks, witnesses.** A *byte string* is a finite list of 8-bit bytes (values $\mathtt{0x00}$–$\mathtt{0xff}$); $[\,]$ is the empty byte string and $|b|$ the length of $b$. Stacks, witnesses and outputs are finite lists of byte strings written **top element first**. For such lists, $x :: l$ is the list with $x$ placed on top of $l$, $l_1 \mathbin{+\!\!+} l_2$ is concatenation (in $w \mathbin{+\!\!+} \mathit{rest}$ all elements of $w$ lie above all elements of $\mathit{rest}$, the first element of $w$ being the top of the stack), and $|l|$ is the number of elements.

**Constants.**
$$\mathrm{MAX\_SCRIPT\_ELEMENT\_SIZE}=520,\quad \mathrm{MAX\_OPS\_PER\_SCRIPT}=201,\quad \mathrm{MAX\_PUBKEYS\_PER\_MULTISIG}=20,\quad \mathrm{MAX\_STACK\_SIZE}=1000.$$

**$\mathrm{castToBool}$.** For a byte string: $\mathrm{castToBool}([\,])=\text{false}$; $\mathrm{castToBool}([b_0]) = (b_0\neq \mathtt{0x00} \wedge b_0 \neq \mathtt{0x80})$; for a string with at least two bytes, $\mathrm{castToBool}(b_0 :: r) = (b_0 \neq 0) \vee \mathrm{castToBool}(r)$. So it is true exactly when some byte other than the last is nonzero, or the last byte is neither $\mathtt{0x00}$ nor $\mathtt{0x80}$; the empty string, all-zero strings, and strings of zero bytes followed by a final $\mathtt{0x80}$ are false.

**$\mathrm{boolBytes}$.** $\mathrm{boolBytes}(\text{true}) = [\mathtt{0x01}]$, $\mathrm{boolBytes}(\text{false}) = [\,]$.

**$\mathrm{serialize}$ (script-number encoding of an integer $n$).** $\mathrm{serialize}(0) = [\,]$. For $n\neq 0$, let $\mathit{mag}$ be the little-endian base-256 digits of $|n|$ with no most-significant zero bytes. If the last (most significant) byte of $\mathit{mag}$ has bit $\mathtt{0x80}$ set, the result is $\mathit{mag}$ followed by one extra byte, $\mathtt{0x80}$ if $n<0$ and $\mathtt{0x00}$ if $n>0$; otherwise the result is $\mathit{mag}$ with bit $\mathtt{0x80}$ of its last byte set if $n<0$, and $\mathit{mag}$ itself if $n>0$. Examples: $\mathrm{serialize}(1)=[\mathtt{0x01}]$, $\mathrm{serialize}(-1)=[\mathtt{0x81}]$, $\mathrm{serialize}(32)=[\mathtt{0x20}]$, $\mathrm{serialize}(128)=[\mathtt{0x80},\mathtt{0x00}]$, $\mathrm{serialize}(2^{31}-1)=[\mathtt{0xff},\mathtt{0xff},\mathtt{0xff},\mathtt{0x7f}]$.

**Flags $f$.** A record of three independent booleans $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$; every combination is allowed.

**Oracle $o$.** A record of **completely arbitrary** functions, with no property assumed of any of them (they are not required to be the real hash functions or a real signature check, need not produce outputs of any particular length, and need not be injective or collision resistant):
- $o.\mathrm{ripemd160},\ o.\mathrm{sha1},\ o.\mathrm{sha256},\ o.\mathrm{hash160},\ o.\mathrm{hash256}$: byte strings $\to$ byte strings;
- $o.\mathrm{checkSig}(\mathit{sig}, \mathit{pubkey}) \in \{\text{none}, \text{some}(\text{true}), \text{some}(\text{false})\}$, an arbitrary function of a signature and a public key ("none" means the script fails);
- $o.\mathrm{checkLockTime},\ o.\mathrm{checkSequence}$: integers $\to$ booleans.

**$\mathrm{multisigLoop}_o(\mathit{sigs}, \mathit{keys})$** (both lists top-first), with result none, some(true) or some(false):
- if $\mathit{sigs} = [\,]$: some(true);
- if $\mathit{sigs}$ is nonempty and $\mathit{keys} = [\,]$: some(false);
- if $\mathit{sigs} = s :: S$ and $\mathit{keys} = k :: K$: compute $o.\mathrm{checkSig}(s, k)$. If none, the result is none. If some(true): the result is some(false) when $|K| < |S|$, and otherwise $\mathrm{multisigLoop}_o(S, K)$. If some(false): the result is some(false) when $|K| < |S| + 1$, and otherwise $\mathrm{multisigLoop}_o(s :: S, K)$.

### The script interpreter (from the script-interpreter preamble)

**Instructions and scripts.** An instruction is either $\mathrm{push}(d)$ for a byte string $d$, or $\mathrm{op}(c)$ for an opcode byte $c$. A script is a finite list of instructions. Opcode bytes used below: `OP_1NEGATE` $=\mathtt{0x4f}$, `OP_RESERVED` $=\mathtt{0x50}$, `OP_1`…`OP_16` $=\mathtt{0x51}$…$\mathtt{0x60}$, `OP_NOP` $=\mathtt{0x61}$, `OP_IF` $=\mathtt{0x63}$, `OP_NOTIF` $=\mathtt{0x64}$, `OP_ELSE` $=\mathtt{0x67}$, `OP_ENDIF` $=\mathtt{0x68}$, `OP_VERIFY` $=\mathtt{0x69}$, `OP_RETURN` $=\mathtt{0x6a}$, `OP_TOALTSTACK` $=\mathtt{0x6b}$, `OP_FROMALTSTACK` $=\mathtt{0x6c}$, `OP_IFDUP` $=\mathtt{0x73}$, `OP_DUP` $=\mathtt{0x76}$, `OP_SWAP` $=\mathtt{0x7c}$, `OP_SIZE` $=\mathtt{0x82}$, `OP_EQUAL` $=\mathtt{0x87}$, `OP_EQUALVERIFY` $=\mathtt{0x88}$, `OP_0NOTEQUAL` $=\mathtt{0x92}$, `OP_BOOLAND` $=\mathtt{0x9a}$, `OP_BOOLOR` $=\mathtt{0x9b}$, `OP_RIPEMD160` $=\mathtt{0xa6}$, `OP_SHA1` $=\mathtt{0xa7}$, `OP_SHA256` $=\mathtt{0xa8}$, `OP_HASH160` $=\mathtt{0xa9}$, `OP_HASH256` $=\mathtt{0xaa}$, `OP_CODESEPARATOR` $=\mathtt{0xab}$, `OP_CHECKSIG` $=\mathtt{0xac}$, `OP_CHECKSIGVERIFY` $=\mathtt{0xad}$, `OP_CHECKMULTISIG` $=\mathtt{0xae}$, `OP_CHECKMULTISIGVERIFY` $=\mathtt{0xaf}$, `OP_NOP1` $=\mathtt{0xb0}$, `OP_CHECKLOCKTIMEVERIFY` $=\mathtt{0xb1}$, `OP_CHECKSEQUENCEVERIFY` $=\mathtt{0xb2}$, `OP_NOP4`…`OP_NOP10` $=\mathtt{0xb3}$…$\mathtt{0xb9}$ (plus the other standard stack/arithmetic opcodes named below).

**$\mathrm{opsIn}(\mathit{sc})$** is the number of instructions $\mathrm{op}(c)$ in the script $\mathit{sc}$ with $c > \mathtt{0x60}$ (pushes and opcodes $\le \mathtt{0x60}$ are not counted).

**States.** A state is a quadruple $(\mathit{stack}, \mathit{alt}, \mathit{vf}, k)$: the main stack and the alt stack (lists of byte strings, top first), the condition stack $\mathit{vf}$ (a list of booleans, innermost first) and the operation counter $k\in\mathbb{N}$. $\mathrm{initial}(\mathit{st}) = (\mathit{st}, [\,], [\,], 0)$. $\mathrm{allTrue}(\mathit{vf})$ means every entry of $\mathit{vf}$ is true (so it is true for $\mathit{vf} = [\,]$, and false exactly when $\mathit{vf}$ contains at least one false). The state is *executing* when $\mathrm{allTrue}(\mathit{vf})$.

**Decoding numbers.** "Decode $v$ with limit $L$" fails if $|v| > L$; otherwise it gives the sign–magnitude little-endian value of $v$: if the last byte has bit $\mathtt{0x80}$ set, minus the little-endian value of $v$ with that bit cleared, else the little-endian value of $v$ ($[\,]$ decodes to $0$). No minimal-encoding requirement is applied anywhere.

**$\mathrm{step}_{f,o}(s, i)$** — one instruction; result is a new state or failure.
- $i = \mathrm{push}(d)$: fail if $|d| > 520$. If executing, put $d$ on top of the main stack; otherwise leave the state unchanged. Then fail if $|\mathit{stack}| + |\mathit{alt}| > 1000$.
- $i = \mathrm{op}(c)$: (1) if $c > \mathtt{0x60}$ and $k + 1 > 201$, fail; if $c > \mathtt{0x60}$, increase $k$ by one (this happens also in non-executed branches). (2) If $c$ is one of the fifteen disabled opcodes (`OP_CAT`, `OP_SUBSTR`, `OP_LEFT`, `OP_RIGHT`, `OP_INVERT`, `OP_AND`, `OP_OR`, `OP_XOR`, `OP_2MUL`, `OP_2DIV`, `OP_MUL`, `OP_DIV`, `OP_MOD`, `OP_LSHIFT`, `OP_RSHIFT`), fail, executing or not. (3) If executing, or $\mathtt{0x63} \le c \le \mathtt{0x68}$, apply $\mathrm{execOp}$ (below, with the flag "executing" passed in); fail if it fails, and otherwise fail if the resulting $|\mathit{stack}| + |\mathit{alt}| > 1000$. (4) Otherwise the state is unchanged apart from $k$, and it fails if $|\mathit{stack}| + |\mathit{alt}| > 1000$.

**$\mathrm{execOp}_{f,o}(\mathit{fExec}, c, s)$.** "Top" is the first stack element, "second" the next; whenever a required element is missing the result is failure.
- `OP_1NEGATE` or `OP_1`…`OP_16`: push $\mathrm{serialize}(c - \mathtt{0x50})$, i.e. of $-1, 1, \dots, 16$.
- `OP_NOP`, `OP_NOP1`, `OP_NOP4`…`OP_NOP10`, `OP_CODESEPARATOR`: no change.
- `OP_CHECKLOCKTIMEVERIFY`: if $f.\mathrm{cltv}$ is false, no change. Otherwise decode the top with limit $5$ (not removing it); fail if that fails, if the value $n<0$, or if $o.\mathrm{checkLockTime}(n)$ is false; else no change.
- `OP_CHECKSEQUENCEVERIFY`: if $f.\mathrm{csv}$ is false, no change. Otherwise decode the top with limit $5$ (not removing it); fail if that fails or $n < 0$; if bit $2^{31}$ of $n$ is set, no change; otherwise fail if $o.\mathrm{checkSequence}(n)$ is false, else no change.
- `OP_IF` / `OP_NOTIF`: if $\mathit{fExec}$, remove the top $t$ and put $\mathrm{castToBool}(t)$ (negated for `OP_NOTIF`) in front of $\mathit{vf}$; if not $\mathit{fExec}$, put false in front of $\mathit{vf}$ and leave the stack alone.
- `OP_ELSE`: fail if $\mathit{vf}$ is empty, else negate its first entry. `OP_ENDIF`: fail if $\mathit{vf}$ is empty, else remove its first entry.
- `OP_VERIFY`: remove the top; fail if $\mathrm{castToBool}$ of it is false. `OP_RETURN`: fail.
- `OP_TOALTSTACK`: move the top of the main stack onto the alt stack. `OP_FROMALTSTACK`: move the top of the alt stack onto the main stack.
- `OP_2DROP`, `OP_2DUP`, `OP_3DUP`, `OP_2OVER`, `OP_2ROT`, `OP_2SWAP`, `OP_DROP`, `OP_NIP`, `OP_OVER`, `OP_ROT`, `OP_TUCK`: the standard rearrangements of the top two to six elements. `OP_DUP`: duplicate the top. `OP_SWAP`: exchange top and second. `OP_IFDUP`: duplicate the top if $\mathrm{castToBool}$ of it is true, else no change. `OP_DEPTH`: push $\mathrm{serialize}(|\mathit{stack}|)$. `OP_PICK`/`OP_ROLL`: remove the top, decode it (limit $4$) as $n$, require a nonempty remainder with $0 \le n <$ its length, and copy (PICK) or move (ROLL) its element of index $n$ (0 = top) to the top.
- `OP_SIZE`: push $\mathrm{serialize}(|t|)$ for the top $t$, which stays.
- `OP_EQUAL` / `OP_EQUALVERIFY`: remove the top $a$ and second $b$; `OP_EQUAL` pushes $\mathrm{boolBytes}(a=b)$; `OP_EQUALVERIFY` fails unless $a=b$.
- `OP_1ADD`, `OP_1SUB`, `OP_NEGATE`, `OP_ABS`, `OP_NOT`, `OP_0NOTEQUAL`: remove the top, decode it with limit $4$ as $n$ (fail if longer), push $\mathrm{serialize}$ of $n+1$, $n-1$, $-n$, $|n|$, ($1$ if $n=0$ else $0$), ($1$ if $n\neq 0$ else $0$) respectively.
- `OP_ADD`, `OP_SUB`, `OP_BOOLAND`, `OP_BOOLOR`, `OP_NUMEQUAL`, `OP_NUMEQUALVERIFY`, `OP_NUMNOTEQUAL`, `OP_LESSTHAN`, `OP_GREATERTHAN`, `OP_LESSTHANOREQUAL`, `OP_GREATERTHANOREQUAL`, `OP_MIN`, `OP_MAX`: remove the top $a$ and second $b$, decode $n_1$ from $b$ and $n_2$ from $a$ with limit $4$ (fail if either is longer), and push $\mathrm{serialize}$ of the result: $n_1+n_2$, $n_1-n_2$, ($1$ if $n_1\neq0$ and $n_2\neq 0$ else $0$), ($1$ if $n_1\neq 0$ or $n_2\neq0$ else $0$), and $1/0$ for $=,=,\neq,<,>,\le,\ge$, then $\min$, $\max$; `OP_NUMEQUALVERIFY` pushes nothing and fails unless $n_1 = n_2$.
- `OP_WITHIN`: remove three elements $a$ (top), $b$, $d$, decode each with limit $4$, push $\mathrm{boolBytes}(b \le d < a)$ of the decoded values.
- `OP_RIPEMD160`, `OP_SHA1`, `OP_SHA256`, `OP_HASH160`, `OP_HASH256`: replace the top $t$ by $o.\mathrm{ripemd160}(t)$, $o.\mathrm{sha1}(t)$, $o.\mathrm{sha256}(t)$, $o.\mathrm{hash160}(t)$, $o.\mathrm{hash256}(t)$ respectively.
- `OP_CHECKSIG` / `OP_CHECKSIGVERIFY`: with $\mathit{pubkey}$ the top and $\mathit{sig}$ the second, let $r = o.\mathrm{checkSig}(\mathit{sig}, \mathit{pubkey})$; fail if $r$ is none; `OP_CHECKSIG` replaces both by $\mathrm{boolBytes}(r)$; `OP_CHECKSIGVERIFY` removes both and fails unless $r$ is true.
- `OP_CHECKMULTISIG` / `OP_CHECKMULTISIGVERIFY`: remove the top and decode it (limit $4$) as $n_K$; fail if $n_K<0$ or $n_K>20$; let $k' = k + n_K$ and fail if $k' > 201$; the next $n_K$ elements (top-first) are the keys (fail if fewer); the following element is decoded (limit $4$) as $n_S$, failing if absent, if $n_S<0$ or $n_S>n_K$; the next $n_S$ elements (top-first) are the signatures (fail if fewer); let $r = \mathrm{multisigLoop}_o(\mathit{sigs}, \mathit{keys})$ and fail if none; one more element, the *dummy*, must be present and is removed; fail if $f.\mathrm{nulldummy}$ is true and the dummy is not $[\,]$; the counter becomes $k'$; `OP_CHECKMULTISIG` pushes $\mathrm{boolBytes}(r)$ onto what remains, the VERIFY form pushes nothing and fails unless $r$ is true.
- Every other byte (including `OP_RESERVED`, $\mathtt{0x65}$, $\mathtt{0x66}$ and any byte $\le \mathtt{0x4e}$ used as an opcode): fail.

**$\mathrm{run}_{f,o}(s, \mathit{sc})$**: $\mathrm{run}(s, [\,])$ is $s$ if its condition stack is empty and failure otherwise; $\mathrm{run}(s, i :: \mathit{sc}')$ fails if $\mathrm{step}(s,i)$ fails and is $\mathrm{run}(\mathrm{step}(s,i), \mathit{sc}')$ otherwise.

**$\mathrm{evalScript}_{f,o}(\mathit{st}, \mathit{sc})$**: if $\mathrm{run}(\mathrm{initial}(\mathit{st}), \mathit{sc})$ succeeds with final state $s'$, the result is "some" of the main stack of $s'$; otherwise it is failure (none). Nothing about the alt stack, the operation counter, or the truth of the top element is checked; the initial stack $\mathit{st}$ is not checked against any size limit.

**$\mathrm{runSeq}_{f,o}(s, \mathit{sc})$** (defined in the Miniscript file): exactly like $\mathrm{run}$ but without the final check: $\mathrm{runSeq}(s, [\,]) = \text{some}(s)$ (whatever its condition stack), and $\mathrm{runSeq}(s, i :: \mathit{sc}')$ fails if $\mathrm{step}(s,i)$ fails and is $\mathrm{runSeq}(\mathrm{step}(s,i), \mathit{sc}')$ otherwise.

### Miniscript definitions used

**$\mathrm{numInstr}(n)$** (from the `to_local` preamble), for an integer $n$: if $n = -1$ or $1 \le n \le 16$, it is the opcode instruction $\mathrm{op}(n + \mathtt{0x50})$, i.e. `OP_1NEGATE` for $-1$ and `OP_1`…`OP_16` for $1,\dots,16$ (these opcodes are $\le \mathtt{0x60}$, so they are not counted by the operation counter, and when executed they push $\mathrm{serialize}(n)$); otherwise it is $\mathrm{push}(\mathrm{serialize}(n))$ — in particular $\mathrm{numInstr}(0) = \mathrm{push}([\,])$, $\mathrm{numInstr}(32) = \mathrm{push}([\mathtt{0x20}])$, and $\mathrm{numInstr}(n) = \mathrm{push}(\mathrm{serialize}(n))$ for $n \ge 17$.

**Miniscript fragments $\mathrm{Ms}$.** The set of finite syntax trees built from exactly the following 23 constructors (byte-string, integer, natural-number and list parameters are arbitrary; no well-formedness is built in):
1. $\mathrm{pk\_k}(\kappa)$, $\kappa$ a byte string (a key);
2. $\mathrm{pk\_h}(h)$, $h$ a byte string (a key hash);
3. $\mathrm{older}(n)$, $n \in \mathbb{Z}$;
4. $\mathrm{after}(n)$, $n \in \mathbb{Z}$;
5. $\mathrm{sha256}(h)$, 6. $\mathrm{hash256}(h)$, 7. $\mathrm{ripemd160}(h)$, 8. $\mathrm{hash160}(h)$, each with $h$ a byte string;
9. $\mathrm{and\_v}(x, y)$, 10. $\mathrm{and\_b}(x, y)$, with $x, y$ fragments;
11. $\mathrm{or\_b}(x, z)$, 12. $\mathrm{or\_c}(x, z)$, 13. $\mathrm{or\_d}(x, z)$, 14. $\mathrm{or\_i}(x, z)$, with $x, z$ fragments;
15. $\mathrm{andor}(x, y, z)$, with $x, y, z$ fragments;
16. $\mathrm{multi}(k, \mathit{keys})$, $k \in \mathbb{N}$ and $\mathit{keys}$ a finite list of byte strings;
17.–23. the wrappers $\mathrm{wrap\_a}(x)$, $\mathrm{wrap\_s}(x)$, $\mathrm{wrap\_c}(x)$, $\mathrm{wrap\_d}(x)$, $\mathrm{wrap\_v}(x)$, $\mathrm{wrap\_j}(x)$, $\mathrm{wrap\_n}(x)$, with $x$ a fragment.

Two fragments are equal exactly when they are built identically.

**$\mathrm{compile}(m)$**, the script of a fragment $m$, written $C(m)$; opcode instructions are written by name, $\mathbin{+\!\!+}$ is concatenation of instruction lists:
1. $C(\mathrm{pk\_k}(\kappa)) = [\mathrm{push}(\kappa)]$.
2. $C(\mathrm{pk\_h}(h)) = [$`OP_DUP`, `OP_HASH160`, $\mathrm{push}(h)$, `OP_EQUALVERIFY`$]$ (no `OP_CHECKSIG`).
3. $C(\mathrm{older}(n)) = [\mathrm{numInstr}(n)$, `OP_CHECKSEQUENCEVERIFY`$]$.
4. $C(\mathrm{after}(n)) = [\mathrm{numInstr}(n)$, `OP_CHECKLOCKTIMEVERIFY`$]$.
5. $C(\mathrm{sha256}(h)) = [$`OP_SIZE`, $\mathrm{numInstr}(32)$, `OP_EQUALVERIFY`, `OP_SHA256`, $\mathrm{push}(h)$, `OP_EQUAL`$]$.
6. $C(\mathrm{hash256}(h))$: the same with `OP_HASH256` in place of `OP_SHA256`.
7. $C(\mathrm{ripemd160}(h))$: the same with `OP_RIPEMD160` (the size check is still against $32$).
8. $C(\mathrm{hash160}(h))$: the same with `OP_HASH160` (the size check is still against $32$).
9. $C(\mathrm{and\_v}(x,y)) = C(x) \mathbin{+\!\!+} C(y)$.
10. $C(\mathrm{and\_b}(x,y)) = C(x) \mathbin{+\!\!+} C(y) \mathbin{+\!\!+} [$`OP_BOOLAND`$]$.
11. $C(\mathrm{or\_b}(x,z)) = C(x) \mathbin{+\!\!+} C(z) \mathbin{+\!\!+} [$`OP_BOOLOR`$]$.
12. $C(\mathrm{or\_c}(x,z)) = C(x) \mathbin{+\!\!+} [$`OP_NOTIF`$] \mathbin{+\!\!+} C(z) \mathbin{+\!\!+} [$`OP_ENDIF`$]$.
13. $C(\mathrm{or\_d}(x,z)) = C(x) \mathbin{+\!\!+} [$`OP_IFDUP`, `OP_NOTIF`$] \mathbin{+\!\!+} C(z) \mathbin{+\!\!+} [$`OP_ENDIF`$]$.
14. $C(\mathrm{or\_i}(x,z)) = [$`OP_IF`$] \mathbin{+\!\!+} C(x) \mathbin{+\!\!+} [$`OP_ELSE`$] \mathbin{+\!\!+} C(z) \mathbin{+\!\!+} [$`OP_ENDIF`$]$.
15. $C(\mathrm{andor}(x,y,z)) = C(x) \mathbin{+\!\!+} [$`OP_NOTIF`$] \mathbin{+\!\!+} C(z) \mathbin{+\!\!+} [$`OP_ELSE`$] \mathbin{+\!\!+} C(y) \mathbin{+\!\!+} [$`OP_ENDIF`$]$ (note $z$ comes before $y$).
16. $C(\mathrm{multi}(k, [\kappa_1, \dots, \kappa_\ell])) = [\mathrm{numInstr}(k), \mathrm{push}(\kappa_1), \dots, \mathrm{push}(\kappa_\ell), \mathrm{numInstr}(\ell)$, `OP_CHECKMULTISIG`$]$ ($k$ and $\ell$ read as integers).
17. $C(\mathrm{wrap\_a}(x)) = [$`OP_TOALTSTACK`$] \mathbin{+\!\!+} C(x) \mathbin{+\!\!+} [$`OP_FROMALTSTACK`$]$.
18. $C(\mathrm{wrap\_s}(x)) = [$`OP_SWAP`$] \mathbin{+\!\!+} C(x)$.
19. $C(\mathrm{wrap\_c}(x)) = C(x) \mathbin{+\!\!+} [$`OP_CHECKSIG`$]$.
20. $C(\mathrm{wrap\_d}(x)) = [$`OP_DUP`, `OP_IF`$] \mathbin{+\!\!+} C(x) \mathbin{+\!\!+} [$`OP_ENDIF`$]$.
21. $C(\mathrm{wrap\_v}(x)) = C(x) \mathbin{+\!\!+} [$`OP_VERIFY`$]$ (always a separate `OP_VERIFY`).
22. $C(\mathrm{wrap\_j}(x)) = [$`OP_SIZE`, `OP_0NOTEQUAL`, `OP_IF`$] \mathbin{+\!\!+} C(x) \mathbin{+\!\!+} [$`OP_ENDIF`$]$.
23. $C(\mathrm{wrap\_n}(x)) = C(x) \mathbin{+\!\!+} [$`OP_0NOTEQUAL`$]$.

Opcode bytes: `OP_IF` $\mathtt{0x63}$, `OP_NOTIF` $\mathtt{0x64}$, `OP_ELSE` $\mathtt{0x67}$, `OP_ENDIF` $\mathtt{0x68}$, `OP_VERIFY` $\mathtt{0x69}$, `OP_TOALTSTACK` $\mathtt{0x6b}$, `OP_FROMALTSTACK` $\mathtt{0x6c}$, `OP_IFDUP` $\mathtt{0x73}$, `OP_DUP` $\mathtt{0x76}$, `OP_SWAP` $\mathtt{0x7c}$, `OP_SIZE` $\mathtt{0x82}$, `OP_EQUAL` $\mathtt{0x87}$, `OP_EQUALVERIFY` $\mathtt{0x88}$, `OP_0NOTEQUAL` $\mathtt{0x92}$, `OP_BOOLAND` $\mathtt{0x9a}$, `OP_BOOLOR` $\mathtt{0x9b}$, `OP_RIPEMD160` $\mathtt{0xa6}$, `OP_SHA256` $\mathtt{0xa8}$, `OP_HASH160` $\mathtt{0xa9}$, `OP_HASH256` $\mathtt{0xaa}$, `OP_CHECKSIG` $\mathtt{0xac}$, `OP_CHECKMULTISIG` $\mathtt{0xae}$, `OP_CHECKLOCKTIMEVERIFY` $\mathtt{0xb1}$, `OP_CHECKSEQUENCEVERIFY` $\mathtt{0xb2}$.

**$\mathrm{opsMax}(m) \in \mathbb{N}$**, defined by: $\mathrm{opsMax}(\mathrm{pk\_k}(\cdot)) = 0$; $\mathrm{opsMax}(\mathrm{pk\_h}(\cdot)) = 3$; $\mathrm{opsMax}(\mathrm{older}(\cdot)) = \mathrm{opsMax}(\mathrm{after}(\cdot)) = 1$; $\mathrm{opsMax}$ of each of $\mathrm{sha256}(\cdot)$, $\mathrm{hash256}(\cdot)$, $\mathrm{ripemd160}(\cdot)$, $\mathrm{hash160}(\cdot)$ is $4$; $\mathrm{opsMax}(\mathrm{and\_v}(x,y)) = \mathrm{opsMax}(x)+\mathrm{opsMax}(y)$; $\mathrm{opsMax}(\mathrm{and\_b}(x,y)) = \mathrm{opsMax}(x)+\mathrm{opsMax}(y)+1$; $\mathrm{opsMax}(\mathrm{or\_b}(x,z)) = \mathrm{opsMax}(x)+\mathrm{opsMax}(z)+1$; $\mathrm{opsMax}(\mathrm{or\_c}(x,z)) = \mathrm{opsMax}(x)+\mathrm{opsMax}(z)+2$; $\mathrm{opsMax}(\mathrm{or\_d}(x,z)) = \mathrm{opsMax}(\mathrm{or\_i}(x,z)) = \mathrm{opsMax}(x)+\mathrm{opsMax}(z)+3$; $\mathrm{opsMax}(\mathrm{andor}(x,y,z)) = \mathrm{opsMax}(x)+\mathrm{opsMax}(y)+\mathrm{opsMax}(z)+3$; $\mathrm{opsMax}(\mathrm{multi}(k,\mathit{keys})) = |\mathit{keys}| + 1$; $\mathrm{opsMax}(\mathrm{wrap\_a}(x)) = \mathrm{opsMax}(x)+2$; $\mathrm{opsMax}(\mathrm{wrap\_s}(x)) = \mathrm{opsMax}(\mathrm{wrap\_c}(x)) = \mathrm{opsMax}(\mathrm{wrap\_v}(x)) = \mathrm{opsMax}(\mathrm{wrap\_n}(x)) = \mathrm{opsMax}(x)+1$; $\mathrm{opsMax}(\mathrm{wrap\_d}(x)) = \mathrm{opsMax}(x)+3$; $\mathrm{opsMax}(\mathrm{wrap\_j}(x)) = \mathrm{opsMax}(x)+4$.
