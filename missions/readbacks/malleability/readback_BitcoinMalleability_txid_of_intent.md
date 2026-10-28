# Read-back: `BitcoinMalleability.txid_of_intent`

## Statement in words

For every consensus flag set $f$, every ledger $u$ and every transaction $\mathrm{tx}$: if the witness flag of $f$ is on, every input script of $\mathrm{tx}$ verifies against $u$ under $f$ (in the sense of $\mathrm{inputScriptsOk}$), and every input of $\mathrm{tx}$ spends, in $u$, an output whose script is a witness program, then the transaction identifier of $\mathrm{tx}$ equals the transaction identifier of the transaction obtained from $\mathrm{tx}$ by emptying every input's $\mathrm{scriptSig}$ and witness.

## Binders and hypotheses

- $f$: a record of seven Booleans $(\mathrm{p2sh}, \mathrm{witness}, \mathrm{taproot}, \mathrm{dersig}, \mathrm{cltv}, \mathrm{csv}, \mathrm{nulldummy})$; arbitrary except as stated.
- $u$: a ledger: a finite association list of pairs (outpoint, coin). An outpoint is $(h, n)$, $h$ a byte string of any length, $n \in \mathbb N$. A coin is $(\mathrm{out}, \mathrm{height}, \mathrm{isCoinbase})$ with $\mathrm{out} = (\mathrm{nValue} \in \mathbb Z, \mathrm{scriptPubKey})$. Keys need not be distinct.
- $\mathrm{tx}$: a transaction $(\mathrm{version} \in \mathbb N, \mathrm{vin}, \mathrm{vout}, \mathrm{nLockTime} \in \mathbb N)$; each input is $(\mathrm{prevout}, \mathrm{scriptSig}, \mathrm{nSequence}, \mathrm{witness})$, each output $(\mathrm{nValue} \in \mathbb Z, \mathrm{scriptPubKey})$. No well-formedness or range condition is assumed.
- $h_f$: $f.\mathrm{witness} = \mathrm{true}$.
- $h$: $\mathrm{inputScriptsOk}(f, u, \mathrm{tx}) = \mathrm{true}$ (unfolded below).
- $h_w$: $\mathrm{SpendsWitnessPrograms}(u, \mathrm{tx})$, i.e. for every input $i$ occurring in $\mathrm{tx}.\mathrm{vin}$, $\mathrm{isWitnessProgram}(\mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out}.\mathrm{scriptPubKey})$ is defined.

## Conclusion

$$
\mathrm{txid}(\mathrm{tx}) \;=\; \mathrm{txid}\big(\mathrm{ofIntent}(\mathrm{intentOf}(\mathrm{tx}))\big),
$$

an equality of byte strings (the 32-byte double-SHA-256 digests).

## The notions, unfolded

**Intent round trip.** $\mathrm{intentOf}(\mathrm{tx}) = (\mathrm{version}, [(i.\mathrm{prevout}, i.\mathrm{nSequence}) \mid i \in \mathrm{vin}], \mathrm{vout}, \mathrm{nLockTime})$, and $\mathrm{ofIntent}$ of that is the transaction $\mathrm{tx}^\circ$ with the same version, outputs and lock time as $\mathrm{tx}$, and whose $j$-th input has the same outpoint and sequence number as the $j$-th input of $\mathrm{tx}$ but $\mathrm{scriptSig} = [\,]$ and $\mathrm{witness} = [\,]$. So the conclusion is $\mathrm{txid}(\mathrm{tx}) = \mathrm{txid}(\mathrm{tx}^\circ)$.

**Transaction identifier.** $\mathrm{txid}(t) = \mathrm{SHA256}(\mathrm{SHA256}(\mathrm{ser}_0(t)))$, where $\mathrm{ser}_0$ is the witness-stripped serialization:

$$
\mathrm{ser}_0(t) = \mathrm{LE}_4(\mathrm{version}) \,\|\, \mathrm{CS}(|\mathrm{vin}|) \,\|\, \big\|_{i \in \mathrm{vin}} \big( i.\mathrm{prevout}.h \,\|\, \mathrm{LE}_4(i.\mathrm{prevout}.n) \,\|\, \mathrm{CS}(|i.\mathrm{scriptSig}|) \,\|\, i.\mathrm{scriptSig} \,\|\, \mathrm{LE}_4(i.\mathrm{nSequence}) \big) \,\|\, \mathrm{CS}(|\mathrm{vout}|) \,\|\, \big\|_{o \in \mathrm{vout}} \big( \mathrm{LE}_8^{\pm}(o.\mathrm{nValue}) \,\|\, \mathrm{CS}(|o.\mathrm{scriptPubKey}|) \,\|\, o.\mathrm{scriptPubKey} \big) \,\|\, \mathrm{LE}_4(\mathrm{nLockTime}).
$$

Here $\mathrm{LE}_4(x)$ is the 4-byte little-endian encoding of $x \bmod 2^{32}$; $\mathrm{LE}_8^{\pm}(z)$ is the 8-byte little-endian encoding of $z \bmod 2^{64}$ (two's complement); $\mathrm{CS}$ is Bitcoin's CompactSize encoding; the outpoint hash $h$ is emitted as its raw bytes, whatever its length. Witness stacks never contribute to $\mathrm{ser}_0$, and no marker/flag bytes are written. The $\mathrm{scriptSig}$ of every input does contribute, with its length prefix. Thus the conclusion asserts that the double-SHA-256 of the byte string above computed with the actual $\mathrm{scriptSig}$s equals the one computed with every $\mathrm{scriptSig}$ replaced by the empty string (whose length prefix is the single byte $0$).

**Lookup.** $\mathrm{accessCoin}(u, o)$ is the coin of the first pair of $u$ whose outpoint equals $o$, or the dummy coin $((-1,[\,]),0,\mathrm{false})$ if none.

**Witness program.** For $s$ of length $k$, $\mathrm{isWitnessProgram}(s)$ is defined iff $4 \le k \le 42$, $s_0 = 0$ or $\mathrm{0x51} \le s_0 \le \mathrm{0x60}$, and $s_1 + 2 = k$; it yields version $0$ (if $s_0 = 0$) or $s_0 - \mathrm{0x50}$, and program $s_2 \ldots s_{k-1}$. The empty script is not a witness program, so $h_w$ forces every input's outpoint to have an entry in $u$.

**Input scripts OK.** With $\mathrm{vin} = [i_0, \ldots, i_{m-1}]$, $c_n = \mathrm{accessCoin}(u, i_n.\mathrm{prevout})$ and $\mathrm{spent} = [c_0.\mathrm{out}, \ldots, c_{m-1}.\mathrm{out}]$, the hypothesis $h$ says that for every $0 \le n < m$,
$$
\mathrm{verifyScript}\big(T_{\mathrm{spent}},\ (f, \mathrm{tx}, n, c_n.\mathrm{out}.\mathrm{nValue}),\ i_n.\mathrm{scriptSig},\ c_n.\mathrm{out}.\mathrm{scriptPubKey},\ i_n.\mathrm{witness}\big) = \mathrm{true},
$$
where $T_{\mathrm{spent}}$ is the Taproot file's BIP341 handler for the spent outputs, and $(f, \mathrm{tx}, n, a)$ is a verification context (flags, spending transaction, input index, amount).

**verifyScript** $(T, c, \sigma, \pi, w)$: (1) evaluate $\sigma$ (signature version *base*) on the empty stack, failing gives false, result $S_\sigma$; (2) evaluate $\pi$ on $S_\sigma$, failing gives false, result $S$; false if $S$ is empty or its top is not true (a byte string is true iff some byte is non-zero, except that a string whose only non-zero byte is a final $\mathrm{0x80}$ is false); (3) if $c.\mathrm{flags}.\mathrm{witness}$ is on and $\mathrm{isWitnessProgram}(\pi) = (v, p)$: false if $\sigma \ne [\,]$, else the verdict of $\mathrm{verifyWitnessProgram}(T, c, w, v, p, \mathrm{isP2sh}=\mathrm{false})$, final; (4) else if $c.\mathrm{flags}.\mathrm{p2sh}$ is on and $\pi$ is $\mathrm{0xa9}\,\mathrm{0x14}\,\langle 20 \text{ bytes}\rangle\,\mathrm{0x87}$: the P2SH path (push-only $\sigma$, top of $S_\sigma$ is the redeem script $r$, evaluated on the rest with a true top; if the witness flag is on and $r$ is a witness program then $\sigma$ must equal $\mathrm{pushBytes}(r)$ and $\mathrm{verifyWitnessProgram}(T, c, w, v, p, \mathrm{true})$ decides; if the witness flag is on and $r$ is not a witness program then $w$ must be empty; with the witness flag off, true); (5) else false if the witness flag is on and $w \ne [\,]$, else true. Evaluation ("evalBytes") of a script $s$ from stack $S$ in context $c$ is undefined if $|s| > 10000$ or $s$ does not parse, and otherwise is the Script interpreter's final stack under flags $(c.\mathrm{flags}.\mathrm{cltv}, c.\mathrm{flags}.\mathrm{csv}, c.\mathrm{flags}.\mathrm{nulldummy})$ with the legacy oracle for $(c.\mathrm{flags}.\mathrm{dersig}, c.\mathrm{tx}, c.\mathrm{nIn}, c.\mathrm{amount}$, the signature version, script code $s)$. $\mathrm{verifyWitnessProgram}(T,c,w,v,p,\mathrm{isP2sh})$: for $v=0$, $|p|=32$, the last element of $w$ must hash (SHA-256) to $p$ and is executed as a witness-v0 script on the reversed remaining elements (every element $\le 520$ bytes, exactly one element left, true); for $v=0$, $|p|=20$, $|w|$ must be $2$ and the implied P2PKH script $\mathrm{0x76}\,\mathrm{0xa9}\,\mathrm{pushBytes}(p)\,\mathrm{0x88}\,\mathrm{0xac}$ is executed on $w$ reversed; $v=0$ with other lengths is false; $v=1$, $|p|=32$, not P2SH is true when $c.\mathrm{flags}.\mathrm{taproot}$ is off and otherwise $T(c, w, p)$; every other case is true. $T_{\mathrm{spent}}(c,w,p)$ is false on an empty $w$; otherwise it strips an optional annex, checks a single remaining element as a Schnorr key-path signature against $p$ over $c.\mathrm{tx}$, $\mathrm{spent}$, $c.\mathrm{nIn}$, or, with more elements, checks a control block (length $33 + 32k$, $0 \le k \le 128$) committing $p$ to the leaf script and executes the tapscript for leaf version $\mathrm{0xc0}$ (true for other leaf versions).

## Edge cases made explicit

- If $\mathrm{tx}.\mathrm{vin} = [\,]$: $h$ and $h_w$ hold vacuously, $\mathrm{tx}^\circ = \mathrm{tx}$, and the conclusion is an identity.
- $h_w$ is by membership and $h$ by position; both cover every input, so duplicated inputs are covered at each occurrence.
- $h_w$ admits every witness version $0$–$16$ and program length $2$–$40$ (version-0 programs of length other than $20$ or $32$, version $1$ of any length, versions $2$–$16$), not only those for which $\mathrm{verifyWitnessProgram}$ performs a check.
- $\mathrm{txid}$ reduces $\mathrm{version}$, $\mathrm{prevout}.n$, $\mathrm{nSequence}$ and $\mathrm{nLockTime}$ modulo $2^{32}$ and $\mathrm{nValue}$ modulo $2^{64}$ before hashing; outpoint hashes of any length are written raw.
- The conclusion is an equality of hash digests, not of transactions; it does not say $\mathrm{tx} = \mathrm{tx}^\circ$ nor that every $\mathrm{scriptSig}$ of $\mathrm{tx}$ is empty.
- Nothing constrains $f.\mathrm{p2sh}$, $f.\mathrm{taproot}$, $f.\mathrm{dersig}$, $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$, the distinctness of ledger keys, coinbase status, or the well-formedness of $\mathrm{tx}$.
