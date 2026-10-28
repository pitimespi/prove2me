# Read-back: `BitcoinMalleability.txid_determined`

## Statement in words

For every consensus flag set $f$, every ledger $u$ and every two transactions $\mathrm{tx}, \mathrm{tx}'$: if the witness flag of $f$ is on, $\mathrm{tx}$ and $\mathrm{tx}'$ have the same intent, each of $\mathrm{tx}$ and $\mathrm{tx}'$ has all its input scripts verifying against $u$ under $f$, and every input of $\mathrm{tx}$ (the hypothesis is stated for $\mathrm{tx}$ only) spends in $u$ an output whose script is a witness program, then $\mathrm{tx}$ and $\mathrm{tx}'$ have the same transaction identifier.

## Binders and hypotheses

- $f$: a record of seven Booleans $(\mathrm{p2sh}, \mathrm{witness}, \mathrm{taproot}, \mathrm{dersig}, \mathrm{cltv}, \mathrm{csv}, \mathrm{nulldummy})$; arbitrary except as stated.
- $u$: a ledger: a finite association list of (outpoint, coin) pairs; outpoint $(h, n)$ with $h$ a byte string of any length and $n \in \mathbb N$; coin $(\mathrm{out}, \mathrm{height}, \mathrm{isCoinbase})$ with $\mathrm{out} = (\mathrm{nValue} \in \mathbb Z, \mathrm{scriptPubKey})$. Keys need not be distinct.
- $\mathrm{tx}, \mathrm{tx}'$: transactions $(\mathrm{version} \in \mathbb N, \mathrm{vin}, \mathrm{vout}, \mathrm{nLockTime} \in \mathbb N)$ with inputs $(\mathrm{prevout}, \mathrm{scriptSig}, \mathrm{nSequence}, \mathrm{witness})$ and outputs $(\mathrm{nValue} \in \mathbb Z, \mathrm{scriptPubKey})$. No well-formedness is assumed.
- $h_f$: $f.\mathrm{witness} = \mathrm{true}$.
- $h_I$: $\mathrm{intentOf}(\mathrm{tx}) = \mathrm{intentOf}(\mathrm{tx}')$.
- $h$: $\mathrm{inputScriptsOk}(f, u, \mathrm{tx}) = \mathrm{true}$.
- $h'$: $\mathrm{inputScriptsOk}(f, u, \mathrm{tx}') = \mathrm{true}$ (same $f$, same $u$).
- $h_w$: $\mathrm{SpendsWitnessPrograms}(u, \mathrm{tx})$. There is **no** corresponding hypothesis for $\mathrm{tx}'$.

## Conclusion

$$
\mathrm{txid}(\mathrm{tx}) = \mathrm{txid}(\mathrm{tx}'),
$$

an equality of 32-byte digests.

## The notions, unfolded

**Same intent.** $\mathrm{intentOf}(t) = (t.\mathrm{version}, [(i.\mathrm{prevout}, i.\mathrm{nSequence}) \mid i \in t.\mathrm{vin}], t.\mathrm{vout}, t.\mathrm{nLockTime})$. So $h_I$ says exactly: $\mathrm{tx}.\mathrm{version} = \mathrm{tx}'.\mathrm{version}$; $\mathrm{tx}$ and $\mathrm{tx}'$ have the same number $m$ of inputs and, for each position $j < m$, the $j$-th inputs have equal outpoints and equal sequence numbers; $\mathrm{tx}.\mathrm{vout} = \mathrm{tx}'.\mathrm{vout}$ as lists (same values and scripts in the same order); $\mathrm{tx}.\mathrm{nLockTime} = \mathrm{tx}'.\mathrm{nLockTime}$. The $j$-th inputs may have different $\mathrm{scriptSig}$s and different witness lists; nothing else may differ. In particular the two transactions reference the same outpoints at the same positions, so the coins $\mathrm{accessCoin}(u, \cdot)$ looked up for position $j$ are the same for both.

**Transaction identifier.** $\mathrm{txid}(t) = \mathrm{SHA256}(\mathrm{SHA256}(\mathrm{ser}_0(t)))$ with
$$
\mathrm{ser}_0(t) = \mathrm{LE}_4(\mathrm{version}) \,\|\, \mathrm{CS}(|\mathrm{vin}|) \,\|\, \big\|_{i \in \mathrm{vin}} \big( i.\mathrm{prevout}.h \,\|\, \mathrm{LE}_4(i.\mathrm{prevout}.n) \,\|\, \mathrm{CS}(|i.\mathrm{scriptSig}|) \,\|\, i.\mathrm{scriptSig} \,\|\, \mathrm{LE}_4(i.\mathrm{nSequence}) \big) \,\|\, \mathrm{CS}(|\mathrm{vout}|) \,\|\, \big\|_{o \in \mathrm{vout}} \big( \mathrm{LE}_8^{\pm}(o.\mathrm{nValue}) \,\|\, \mathrm{CS}(|o.\mathrm{scriptPubKey}|) \,\|\, o.\mathrm{scriptPubKey} \big) \,\|\, \mathrm{LE}_4(\mathrm{nLockTime}),
$$
where $\mathrm{LE}_4(x)$ is the 4-byte little-endian encoding of $x \bmod 2^{32}$, $\mathrm{LE}_8^{\pm}(z)$ the 8-byte two's-complement little-endian encoding of $z \bmod 2^{64}$, $\mathrm{CS}$ the CompactSize encoding, and the outpoint hash is written raw at whatever length it has. Witnesses never appear; every $\mathrm{scriptSig}$ appears with its length prefix. Under $h_I$ the serializations of $\mathrm{tx}$ and $\mathrm{tx}'$ can differ only in the $\mathrm{scriptSig}$ fields (and their length prefixes), so the conclusion asserts the double-SHA-256 digests agree despite any such difference.

**Lookup.** $\mathrm{accessCoin}(u, o)$ is the coin of the first pair of $u$ whose outpoint equals $o$, or the dummy coin $((-1,[\,]),0,\mathrm{false})$.

**Witness program.** For $s$ of length $k$: defined iff $4 \le k \le 42$, $s_0 = 0$ or $\mathrm{0x51} \le s_0 \le \mathrm{0x60}$, and $s_1 + 2 = k$; version $0$ or $s_0 - \mathrm{0x50}$; program $s_2 \ldots s_{k-1}$. $h_w$ says every input of $\mathrm{tx}$ (by membership) has a looked-up output script of this shape; since the empty script is not of this shape, every input's outpoint has an entry in $u$.

**Input scripts OK** for a transaction $t$ with inputs $[i_0, \ldots, i_{m-1}]$, $c_n = \mathrm{accessCoin}(u, i_n.\mathrm{prevout})$, $\mathrm{spent} = [c_0.\mathrm{out}, \ldots, c_{m-1}.\mathrm{out}]$: for every $0 \le n < m$,
$$
\mathrm{verifyScript}\big(T_{\mathrm{spent}},\ (f, t, n, c_n.\mathrm{out}.\mathrm{nValue}),\ i_n.\mathrm{scriptSig},\ c_n.\mathrm{out}.\mathrm{scriptPubKey},\ i_n.\mathrm{witness}\big) = \mathrm{true}.
$$
For $h$ the context carries $t = \mathrm{tx}$ and for $h'$ it carries $t = \mathrm{tx}'$ (the spending transaction enters signature hashing and lock-time checks through the context); $\mathrm{spent}$ is the same list for both.

**verifyScript** $(T, c, \sigma, \pi, w)$: (1) evaluate $\sigma$ (signature version *base*) on the empty stack; failure gives false; result $S_\sigma$; (2) evaluate $\pi$ on $S_\sigma$; failure gives false; result $S$; false if $S$ is empty or its top is not true (true iff some byte non-zero, except a string whose only non-zero byte is a final $\mathrm{0x80}$); (3) if $c.\mathrm{flags}.\mathrm{witness}$ is on and $\mathrm{isWitnessProgram}(\pi) = (v,p)$: false if $\sigma \ne [\,]$, else $\mathrm{verifyWitnessProgram}(T, c, w, v, p, \mathrm{false})$, final; (4) else if $c.\mathrm{flags}.\mathrm{p2sh}$ is on and $\pi = \mathrm{0xa9}\,\mathrm{0x14}\,\langle 20\text{ bytes}\rangle\,\mathrm{0x87}$: $\sigma$ must be push-only, $S_\sigma$ non-empty with top $r$ (the redeem script), $r$ evaluated on the rest must succeed with a true top; then with the witness flag on: if $r$ is a witness program $(v,p)$, $\sigma$ must equal $\mathrm{pushBytes}(r)$ and $\mathrm{verifyWitnessProgram}(T,c,w,v,p,\mathrm{true})$ decides, otherwise $w$ must be empty; with the witness flag off, true; (5) else false if the witness flag is on and $w \ne [\,]$, else true. Script evaluation is undefined if the script exceeds $10000$ bytes or fails to parse, and otherwise is the Script interpreter's final stack under flags $(\mathrm{cltv}, \mathrm{csv}, \mathrm{nulldummy})$ of $c$ with the legacy oracle for $(c.\mathrm{flags}.\mathrm{dersig}, c.\mathrm{tx}, c.\mathrm{nIn}, c.\mathrm{amount}$, signature version, script code$)$. $\mathrm{pushBytes}(d)$ is the canonical push ($|d|$ as one byte then $d$ if $|d| < \mathrm{0x4c}$; $\mathrm{0x4c}$/$\mathrm{0x4d}$/$\mathrm{0x4e}$ with 1/2/4 little-endian length bytes otherwise). $\mathrm{verifyWitnessProgram}(T,c,w,v,p,\mathrm{isP2sh})$: $v=0,|p|=32$: last element of $w$ must SHA-256 to $p$ and is run as a witness-v0 script on the reversed remaining elements (all $\le 520$ bytes, exactly one element left, true); $v=0,|p|=20$: $|w|=2$ and the implied P2PKH script is run on $w$ reversed; $v=0$ other lengths: false; $v=1,|p|=32$, not P2SH: true if $c.\mathrm{flags}.\mathrm{taproot}$ is off, else $T(c,w,p)$; all other cases: true. $T_{\mathrm{spent}}(c,w,p)$: false on empty $w$; else strip an optional annex; one element: Schnorr key-path check against $p$ over $c.\mathrm{tx}$, $\mathrm{spent}$, $c.\mathrm{nIn}$; more: control block of length $33+32k$ ($0\le k\le 128$) committing $p$ to the leaf script, tapscript executed for leaf version $\mathrm{0xc0}$, true for other leaf versions.

## Edge cases made explicit

- If $\mathrm{tx}.\mathrm{vin} = [\,]$ then by $h_I$ also $\mathrm{tx}'.\mathrm{vin} = [\,]$; $h$, $h'$, $h_w$ hold vacuously and $\mathrm{tx} = \mathrm{tx}'$ outright.
- $h_w$ is asserted for $\mathrm{tx}$ only. Because $h_I$ makes the outpoint sequences of $\mathrm{tx}$ and $\mathrm{tx}'$ identical, the looked-up scripts for $\mathrm{tx}'$ are the same strings; but the statement does not itself assert $\mathrm{SpendsWitnessPrograms}(u, \mathrm{tx}')$.
- $h_I$ allows $\mathrm{tx}$ and $\mathrm{tx}'$ to differ in every $\mathrm{scriptSig}$ and every witness, including having different numbers of witness elements and non-empty versus empty $\mathrm{scriptSig}$s; it forbids any difference elsewhere.
- $h$ and $h'$ each require every input to verify; both use the same ledger $u$ and the same flags $f$; the amount passed to each context is the looked-up coin's value, $-1$ for a missing coin.
- Any witness version $0$–$16$ and program length $2$–$40$ satisfies $h_w$, including versions and lengths for which $\mathrm{verifyWitnessProgram}$ returns true without inspecting the witness.
- $\mathrm{txid}$ reduces 32-bit fields modulo $2^{32}$ and values modulo $2^{64}$; outpoint hashes of any length are written raw.
- The conclusion is equality of digests, not of transactions and not of witness-including identifiers; nothing is said about $\mathrm{wtxid}$.
- No constraint on $f.\mathrm{p2sh}$, $f.\mathrm{taproot}$, $f.\mathrm{dersig}$, $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$, on distinctness of ledger keys, on coinbase status, or on well-formedness is assumed.
