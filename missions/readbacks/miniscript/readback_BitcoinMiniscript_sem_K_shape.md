# Read-back: `BitcoinMiniscript.sem_K_shape`

**Statement.** For any flags $f$, any oracle $o$ (arbitrary functions, see below), any fragment $m$ with $\mathrm{HasType}(m, \mathsf{K})$, and any lists $w, \mathit{out}$ of byte strings: if $\mathrm{Sem}_{f,o}(m, w, \mathit{out})$, then $\mathit{out}$ has exactly two elements:
$$\exists\, \kappa, \mathit{sig}:\quad \mathit{out} = [\kappa, \mathit{sig}].$$
Nothing further is said about $\kappa$ or $\mathit{sig}$ (e.g. their relation to the keys in $m$ or to $w$). No resource hypotheses.

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

### Miniscript definitions used

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

**Correctness types $\mathrm{Ty}$.** A four-element set $\{\mathsf{B}, \mathsf{V}, \mathsf{K}, \mathsf{W}\}$ of distinct labels (no meaning is attached to them other than through the rules below).

**Modifier records $\mathrm{Props}$.** A record of five booleans $(z, o, n, d, u)$.

**$\mathrm{props}(m) = (z, o, n, d, u)$**, computed syntactically. Write $z_x, o_x, n_x, d_x, u_x$ for the components of $\mathrm{props}(x)$ (similarly for $y$, $z$), $\wedge,\vee$ for boolean and/or, T/F for true/false. (The modifier letter $o$ is unrelated to the oracle $o$, and the modifier letter $z$ is unrelated to a sub-fragment named $z$; e.g. $z_z$ is the $z$-modifier of the sub-fragment $z$.)

| fragment | $z$ | $o$ | $n$ | $d$ | $u$ |
|---|---|---|---|---|---|
| $\mathrm{pk\_k}(\kappa)$ | F | T | T | T | T |
| $\mathrm{pk\_h}(h)$ | F | F | T | T | T |
| $\mathrm{older}(n)$, $\mathrm{after}(n)$ | T | F | F | F | F |
| $\mathrm{sha256}$, $\mathrm{hash256}$, $\mathrm{ripemd160}$, $\mathrm{hash160}$ | F | T | T | T | T |
| $\mathrm{and\_v}(x,y)$ | $z_x\wedge z_y$ | $(z_x\wedge o_y)\vee(o_x\wedge z_y)$ | $n_x\vee(z_x\wedge n_y)$ | F | $u_y$ |
| $\mathrm{and\_b}(x,y)$ | $z_x\wedge z_y$ | $(z_x\wedge o_y)\vee(o_x\wedge z_y)$ | $n_x\vee(z_x\wedge n_y)$ | $d_x\wedge d_y$ | T |
| $\mathrm{or\_b}(x,z)$ | $z_x\wedge z_z$ | $(z_x\wedge o_z)\vee(o_x\wedge z_z)$ | F | T | T |
| $\mathrm{or\_c}(x,z)$ | $z_x\wedge z_z$ | $o_x\wedge z_z$ | F | F | F |
| $\mathrm{or\_d}(x,z)$ | $z_x\wedge z_z$ | $o_x\wedge z_z$ | F | $d_z$ | $u_z$ |
| $\mathrm{or\_i}(x,z)$ | F | $z_x\wedge z_z$ | F | $d_x\vee d_z$ | $u_x\wedge u_z$ |
| $\mathrm{andor}(x,y,z)$ | $z_x\wedge z_y\wedge z_z$ | $(z_x\wedge o_y\wedge o_z)\vee(o_x\wedge z_y\wedge z_z)$ | F | $d_z$ | $u_y\wedge u_z$ |
| $\mathrm{multi}(k,\mathit{keys})$ | F | F | T | T | T |
| $\mathrm{wrap\_a}(x)$ | F | F | F | $d_x$ | $u_x$ |
| $\mathrm{wrap\_s}(x)$ | F | $o_x$ | F | $d_x$ | $u_x$ |
| $\mathrm{wrap\_c}(x)$ | F | $o_x$ | $n_x$ | $d_x$ | T |
| $\mathrm{wrap\_d}(x)$ | F | T | T | T | F |
| $\mathrm{wrap\_v}(x)$ | $z_x$ | $o_x$ | $n_x$ | F | F |
| $\mathrm{wrap\_j}(x)$ | F | $o_x$ | T | T | $u_x$ |
| $\mathrm{wrap\_n}(x)$ | $z_x$ | $o_x$ | $n_x$ | $d_x$ | T |

(The components do not depend on the byte-string, integer or list parameters of the leaves.)

**$\mathrm{HasType}(m, t)$**, "$m$ has type $t$", is the smallest relation closed under the following 23 rules (one per constructor; there is no other way to derive it). Throughout, $520 = \mathrm{MAX\_SCRIPT\_ELEMENT\_SIZE}$ and $20 = \mathrm{MAX\_PUBKEYS\_PER\_MULTISIG}$.
1. $\mathrm{pk\_k}(\kappa) : \mathsf{K}$ if $|\kappa| \le 520$.
2. $\mathrm{pk\_h}(h) : \mathsf{K}$ if $|h| \le 520$.
3. $\mathrm{older}(n) : \mathsf{B}$ if $1 \le n < 2^{31}$.
4. $\mathrm{after}(n) : \mathsf{B}$ if $1 \le n < 2^{31}$.
5.–8. $\mathrm{sha256}(h)$, $\mathrm{hash256}(h)$, $\mathrm{ripemd160}(h)$, $\mathrm{hash160}(h)$ $: \mathsf{B}$ if $|h| \le 520$ (no condition on $|h|$ being any particular hash length).
9. $\mathrm{and\_v}(x,y) : t$ if $x : \mathsf{V}$, $y : t$ and $t \neq \mathsf{W}$.
10. $\mathrm{and\_b}(x,y) : \mathsf{B}$ if $x : \mathsf{B}$ and $y : \mathsf{W}$.
11. $\mathrm{or\_b}(x,z) : \mathsf{B}$ if $x : \mathsf{B}$, $d_x$, $z : \mathsf{W}$, $d_z$.
12. $\mathrm{or\_c}(x,z) : \mathsf{V}$ if $x : \mathsf{B}$, $d_x$, $u_x$, $z : \mathsf{V}$.
13. $\mathrm{or\_d}(x,z) : \mathsf{B}$ if $x : \mathsf{B}$, $d_x$, $u_x$, $z : \mathsf{B}$.
14. $\mathrm{or\_i}(x,z) : t$ if $x : t$, $z : t$ and $t \ne \mathsf{W}$.
15. $\mathrm{andor}(x,y,z) : t$ if $x : \mathsf{B}$, $d_x$, $u_x$, $y : t$, $z : t$ and $t \ne \mathsf{W}$.
16. $\mathrm{multi}(k, \mathit{keys}) : \mathsf{B}$ if $1 \le k \le |\mathit{keys}| \le 20$ and every key in $\mathit{keys}$ has length $\le 520$.
17. $\mathrm{wrap\_a}(x) : \mathsf{W}$ if $x : \mathsf{B}$.
18. $\mathrm{wrap\_s}(x) : \mathsf{W}$ if $x : \mathsf{B}$ and $o_x$.
19. $\mathrm{wrap\_c}(x) : \mathsf{B}$ if $x : \mathsf{K}$.
20. $\mathrm{wrap\_d}(x) : \mathsf{B}$ if $x : \mathsf{V}$ and $z_x$.
21. $\mathrm{wrap\_v}(x) : \mathsf{V}$ if $x : \mathsf{B}$.
22. $\mathrm{wrap\_j}(x) : \mathsf{B}$ if $x : \mathsf{B}$ and $n_x$.
23. $\mathrm{wrap\_n}(x) : \mathsf{B}$ if $x : \mathsf{B}$.

Here $d_x$, $u_x$, $o_x$, $z_x$, $n_x$ mean the corresponding component of $\mathrm{props}(x)$ is true. Read off the rules: type $\mathsf{W}$ is concluded only by rules 17–18 ($\mathrm{wrap\_a}$, $\mathrm{wrap\_s}$); type $\mathsf{K}$ only by rules 1, 2, 9 (with $y : \mathsf{K}$), 14 and 15 (with both branches $\mathsf{K}$); type $\mathsf{V}$ only by rules 9, 12, 14, 15, 21. No rule constrains the modifiers $o, n, z, u$ of $y$ or $z$ beyond those listed, and no rule bounds the depth or total size of the fragment.

**$\mathrm{CsvPasses}_{f,o}(n)$** (from the `to_local` preamble), for $n\in\mathbb{Z}$: $f.\mathrm{csv} = \text{false}$, **or** ($n \ge 0$ and (bit $2^{31}$ of $n$ is set, or $o.\mathrm{checkSequence}(n) = \text{true}$)).

**$\mathrm{CltvPasses}_{f,o}(n)$** (from the HTLC preamble), for $n\in\mathbb{Z}$: $f.\mathrm{cltv} = \text{false}$, **or** ($n \ge 0$ and $o.\mathrm{checkLockTime}(n) = \text{true}$).

**$\mathrm{Sem}_{f,o}(m, w, \mathit{out})$** — a relation between a fragment $m$, a witness $w$ and an output $\mathit{out}$ (both lists of byte strings, top first), for fixed flags $f$ and oracle $o$; it is defined by recursion on $m$, and nothing in it refers to the type of $m$ or to any size or operation-count limit except where stated. "$\exists$" ranges over arbitrary byte strings / lists of byte strings / booleans as appropriate.
1. $\mathrm{pk\_k}(\kappa)$: $\exists\, \mathit{sig}$ with $w = [\mathit{sig}]$ and $\mathit{out} = [\kappa, \mathit{sig}]$.
2. $\mathrm{pk\_h}(h)$: $\exists\, \kappa, \mathit{sig}$ with $w = [\kappa, \mathit{sig}]$, $o.\mathrm{hash160}(\kappa) = h$ and $\mathit{out} = [\kappa, \mathit{sig}]$.
3. $\mathrm{older}(n)$: $w = [\,]$, $\mathrm{CsvPasses}_{f,o}(n)$ and $\mathit{out} = [\mathrm{serialize}(n)]$.
4. $\mathrm{after}(n)$: $w = [\,]$, $\mathrm{CltvPasses}_{f,o}(n)$ and $\mathit{out} = [\mathrm{serialize}(n)]$.
5. $\mathrm{sha256}(h)$: $\exists\, p$ with $w = [p]$, $|p| = 32$ and $\mathit{out} = [\mathrm{boolBytes}(o.\mathrm{sha256}(p) = h)]$ — so $\mathit{out} = [[\mathtt{0x01}]]$ if the oracle hash of $p$ equals $h$ and $\mathit{out} = [[\,]]$ otherwise (any 32-byte $p$ is accepted either way).
6.–8. $\mathrm{hash256}(h)$, $\mathrm{ripemd160}(h)$, $\mathrm{hash160}(h)$: the same with $o.\mathrm{hash256}$, $o.\mathrm{ripemd160}$, $o.\mathrm{hash160}$ respectively (and still $|p| = 32$).
9. $\mathrm{and\_v}(x,y)$: $\exists\, w_x, w_y$ with $w = w_x \mathbin{+\!\!+} w_y$, $\mathrm{Sem}(x, w_x, [\,])$ and $\mathrm{Sem}(y, w_y, \mathit{out})$.
10. $\mathrm{and\_b}(x,y)$: $\exists\, w_x, w_y, v_x, v_y$ with $w = w_x \mathbin{+\!\!+} w_y$, $\mathrm{Sem}(x, w_x, [v_x])$, $\mathrm{Sem}(y, w_y, [v_y])$ and $\mathit{out} = [\mathrm{boolBytes}(\mathrm{castToBool}(v_x) \wedge \mathrm{castToBool}(v_y))]$.
11. $\mathrm{or\_b}(x,z)$: $\exists\, w_x, w_z, v_x, v_z$ with $w = w_x \mathbin{+\!\!+} w_z$, $\mathrm{Sem}(x, w_x, [v_x])$, $\mathrm{Sem}(z, w_z, [v_z])$ and $\mathit{out} = [\mathrm{boolBytes}(\mathrm{castToBool}(v_x) \vee \mathrm{castToBool}(v_z))]$ (both sides may be true simultaneously).
12. $\mathrm{or\_c}(x,z)$: $\mathit{out} = [\,]$ and $\exists\, w_x, v_x$ with $\mathrm{Sem}(x, w_x, [v_x])$ and either ($\mathrm{castToBool}(v_x)$ true and $w = w_x$) or ($\mathrm{castToBool}(v_x)$ false and $\exists\, w_z$ with $w = w_x \mathbin{+\!\!+} w_z$ and $\mathrm{Sem}(z, w_z, [\,])$). ($v_x$ in the second alternative is any value with $\mathrm{castToBool}$ false, not necessarily $[\,]$.)
13. $\mathrm{or\_d}(x,z)$: $\exists\, w_x, v_x$ with $\mathrm{Sem}(x, w_x, [v_x])$ and either ($\mathrm{castToBool}(v_x)$ true, $w = w_x$ and $\mathit{out} = [v_x]$) or ($\mathrm{castToBool}(v_x)$ false and $\exists\, w_z$ with $w = w_x \mathbin{+\!\!+} w_z$ and $\mathrm{Sem}(z, w_z, \mathit{out})$).
14. $\mathrm{or\_i}(x,z)$: $\exists\, b, w'$ with $w = b :: w'$ and either ($\mathrm{castToBool}(b)$ true and $\mathrm{Sem}(x, w', \mathit{out})$) or ($\mathrm{castToBool}(b)$ false and $\mathrm{Sem}(z, w', \mathit{out})$). The selector $b$ is any byte string (not only $[\mathtt{0x01}]$ / $[\,]$), with no length bound.
15. $\mathrm{andor}(x,y,z)$: $\exists\, w_x, v_x$ with $\mathrm{Sem}(x, w_x, [v_x])$ and either ($\mathrm{castToBool}(v_x)$ true and $\exists\, w_y$ with $w = w_x \mathbin{+\!\!+} w_y$ and $\mathrm{Sem}(y, w_y, \mathit{out})$) or ($\mathrm{castToBool}(v_x)$ false and $\exists\, w_z$ with $w = w_x \mathbin{+\!\!+} w_z$ and $\mathrm{Sem}(z, w_z, \mathit{out})$).
16. $\mathrm{multi}(k, \mathit{keys})$: $\exists$ a list $\mathit{sigs}$, a byte string $\mathit{dummy}$ and a boolean $\mathit{ok}$ with $w = \mathit{sigs} \mathbin{+\!\!+} [\mathit{dummy}]$ (the dummy is the deepest witness element), $|\mathit{sigs}| = k$, $\mathrm{multisigLoop}_o(\mathit{sigs}, \mathrm{reverse}(\mathit{keys})) = \text{some}(\mathit{ok})$ (keys taken last-listed first), ($f.\mathrm{nulldummy}$ true $\Rightarrow \mathit{dummy} = [\,]$), and $\mathit{out} = [\mathrm{boolBytes}(\mathit{ok})]$. Both $\mathit{ok}$ true and false are allowed.
17. $\mathrm{wrap\_a}(x)$: $\mathrm{Sem}(x, w, \mathit{out})$.
18. $\mathrm{wrap\_s}(x)$: $\mathrm{Sem}(x, w, \mathit{out})$.
19. $\mathrm{wrap\_c}(x)$: $\exists\, \kappa, \mathit{sig}, \mathit{ok}$ with $\mathrm{Sem}(x, w, [\kappa, \mathit{sig}])$, $o.\mathrm{checkSig}(\mathit{sig}, \kappa) = \text{some}(\mathit{ok})$ and $\mathit{out} = [\mathrm{boolBytes}(\mathit{ok})]$ ($\mathit{ok}$ may be false).
20. $\mathrm{wrap\_d}(x)$: either ($w = [[\mathtt{0x01}]]$, $\mathrm{Sem}(x, [\,], [\,])$ and $\mathit{out} = [[\mathtt{0x01}]]$) or ($w = [[\,]]$ and $\mathit{out} = [[\,]]$). The selector must be exactly the one-byte string $[\mathtt{0x01}]$ or exactly the empty string.
21. $\mathrm{wrap\_v}(x)$: $\exists\, v$ with $\mathrm{Sem}(x, w, [v])$, $\mathrm{castToBool}(v)$ true, and $\mathit{out} = [\,]$.
22. $\mathrm{wrap\_j}(x)$: either ($w = e :: w'$ for some $e, w'$ with $e \ne [\,]$, $|e| \le 520$, and $\mathrm{Sem}(x, w, \mathit{out})$ — note $x$ receives the whole $w$, including $e$) or ($w = [[\,]]$ and $\mathit{out} = [[\,]]$).
23. $\mathrm{wrap\_n}(x)$: $\exists\, v$ with $\mathrm{Sem}(x, w, [v])$ and $\mathit{out} = [\mathrm{boolBytes}(\mathrm{castToBool}(v))]$.
