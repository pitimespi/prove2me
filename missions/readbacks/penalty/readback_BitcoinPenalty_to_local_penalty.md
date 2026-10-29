# Read-back: `BitcoinPenalty.to_local_penalty`

## What the declaration literally asserts

For every Taproot handler $tap$, every verification context $c$ with $c.\mathrm{flags}.\mathrm{witness} = \mathrm{true}$, every commitment-key record $K$ satisfying $\mathrm{WellFormed}(K)$, under the two hypotheses

* $\mathrm{castToBool}(\mathrm{sha256}(\mathcal S_{\mathrm{toLocal}}(K))) = \mathrm{true}$ (the SHA-256 of the `to_local` script is neither all zeros nor "negative zero"), and
* $\mathrm{HoldsRevocation}(o_{\mathrm{toLocal}}, K)$ where $o_{\mathrm{toLocal}} := \mathrm{oracleOf}(c, \mathcal S_{\mathrm{toLocal}}(K))$, i.e. there exists a byte string $sig_R$ with $|sig_R| \le 520$ and $o_{\mathrm{toLocal}}.\mathrm{checkSig}(sig_R, K.\mathrm{revPk}) = \mathrm{some\ true}$, **and** $\mathrm{hash160}(K.\mathrm{revPk}) = K.\mathrm{revHash}$ (concrete RIPEMD160∘SHA256),

the conclusion is **existential**:

$$\exists\, sig_R \in \mathrm{Bytes},\quad V\bigl(\mathcal S_{\mathrm{toLocal}}(K),\ [\,sig_R,\ [\mathtt{0x01}],\ \mathcal S_{\mathrm{toLocal}}(K)\,]\bigr),$$

i.e. some byte string $sig_R$ makes `verifyScript` with the Taproot handler $tap$, context $c$, empty scriptSig, output script $\mathrm{p2wshOf}(\mathcal S_{\mathrm{toLocal}}(K))$ and witness $\mathrm{toLocalPenaltyWitness}(K, sig_R)$ return $\mathrm{true}$. The witness's executed stack (top first) is $[[\mathtt{0x01}], sig_R]$ and the script run is $\mathcal S_{\mathrm{toLocal}}(K)$ under flags $f = \mathrm{scriptFlagsOf}(c.\mathrm{flags})$ and oracle $o_{\mathrm{toLocal}}$.

## Notes on the binders and edge cases

* The flags $c.\mathrm{flags}.\mathrm{p2sh}$, $\mathrm{taproot}$, $\mathrm{dersig}$, $\mathrm{cltv}$, $\mathrm{csv}$, $\mathrm{nulldummy}$ are unconstrained. $c.tx$, $c.\mathrm{nIn}$ and $c.\mathrm{amount}$ are unconstrained except through $\mathrm{HoldsRevocation}$ (whose signature clause, under the concrete oracle, can only hold if $c.\mathrm{amount} \ge 0$ and $K.\mathrm{revPk}$ is a 33- or 65-byte key whose header byte matches its length, since otherwise the concrete `checkSig` never returns $\mathrm{some\ true}$).
* The existential $sig_R$ in the conclusion is **not** tied to the $sig_R$ of the hypothesis by the statement; the statement only asserts that some byte string works.
* $\mathrm{WellFormed}(K)$ bounds the eight byte-string fields of $K$ by $520$ bytes and puts $0 \le K.\mathrm{toSelfDelay} < 2^{16}$; it is the only constraint on $K.\mathrm{localDelayedPk}$ and $K.\mathrm{toSelfDelay}$ here.
* The hash-equality clause of $\mathrm{HoldsRevocation}$ ($\mathrm{hash160}(K.\mathrm{revPk}) = K.\mathrm{revHash}$) is part of the hypothesis even though $\mathcal S_{\mathrm{toLocal}}(K)$ does not mention $K.\mathrm{revHash}$.

---

## Shared setting and unfolded definitions

Everything below is the literal content of the definitions the statement uses, unfolded from the preamble files. It is identical across the read-backs of this bundle; nothing in it is specific to one theorem except where a theorem's own section says so.

### Basic objects

* A **byte** is an 8-bit word; a **byte string** ($\mathrm{Bytes}$) is a finite list of bytes. Byte strings are the only kind of value scripts push and keys, hashes, signatures, witness elements are all byte strings with **no length or format constraint** unless a hypothesis states one.
* A **transaction** $tx$ has a version $tx.\mathrm{version} \in \mathbb N$, a list of inputs $tx.\mathrm{vin}$ (each input has a previous outpoint, a $\mathrm{scriptSig}$, a sequence number $\mathrm{nSequence} \in \mathbb N$ and a witness stack), a list of outputs $tx.\mathrm{vout}$ (each with an amount $\in \mathbb Z$ and an output script) and a lock time $tx.\mathrm{nLockTime} \in \mathbb N$. In these statements **none of these fields is range-restricted**: version, sequence numbers and lock time are arbitrary natural numbers (not bounded by $2^{32}$) unless a hypothesis says otherwise.
* A **consensus flag set** $F$ consists of seven booleans: $F.\mathrm{p2sh}$, $F.\mathrm{witness}$, $F.\mathrm{taproot}$, $F.\mathrm{dersig}$, $F.\mathrm{cltv}$, $F.\mathrm{csv}$, $F.\mathrm{nulldummy}$. Every flag not fixed by a hypothesis is **arbitrary** (the statement is asserted for both values).
* A **verification context** $c$ is a quadruple: flags $c.\mathrm{flags}$, a transaction $c.tx$, an input index $c.\mathrm{nIn} \in \mathbb N$ (not required to be a valid index into $c.tx.\mathrm{vin}$ unless a hypothesis says so) and an amount $c.\mathrm{amount} \in \mathbb Z$ (may be negative).
* A **Taproot handler** $tap$ is any function from (context, witness stack, 32-byte program) to booleans. It is universally quantified; in the unfolding below the version-0 witness branch never calls it, so the asserted statement is the same for every $tap$.
* $f := \mathrm{scriptFlagsOf}(c.\mathrm{flags})$ is the interpreter flag triple $(f.\mathrm{cltv}, f.\mathrm{csv}, f.\mathrm{nulldummy}) := (c.\mathrm{flags}.\mathrm{cltv},\ c.\mathrm{flags}.\mathrm{csv},\ c.\mathrm{flags}.\mathrm{nulldummy})$.
* $\mathrm{sigFlagsOf}(c.\mathrm{flags}) := (\mathrm{dersig} = c.\mathrm{flags}.\mathrm{dersig},\ \mathrm{lowS} = \mathrm{false},\ \mathrm{strictenc} = \mathrm{false},\ \mathrm{witnessPubkeyType} = \mathrm{false})$.
* $\mathrm{MAX\_SCRIPT\_ELEMENT\_SIZE} = 520$, $\mathrm{MAX\_SCRIPT\_SIZE} = 10000$, $\mathrm{MAX\_STACK\_SIZE} = 1000$, $\mathrm{MAX\_OPS\_PER\_SCRIPT} = 201$.
* $\mathrm{SEQUENCE\_LOCKTIME\_DISABLE\_FLAG} = 2^{31} = 2147483648$ (the same value is defined both in the script file and in the signature file; the theorems name the signature file's copy). $\mathrm{LOCKTIME\_THRESHOLD} = 500000000$. $\mathrm{SEQUENCE\_FINAL} = 2^{32}-1 = \mathtt{0xffffffff}$. $\mathrm{SEQUENCE\_LOCKTIME\_TYPE\_FLAG} = 2^{22}$, $\mathrm{SEQUENCE\_LOCKTIME\_MASK} = \mathtt{0xffff}$.

### `castToBool`

For a byte string $v$, $\mathrm{castToBool}(v) = \mathrm{true}$ iff some byte of $v$ is nonzero, **except** that a string whose bytes are all zero apart from a last byte equal to $\mathtt{0x80}$ ("negative zero") is $\mathrm{false}$. The empty string is $\mathrm{false}$. Hence for a 32-byte hash $H$, "$\mathrm{castToBool}(H) = \mathrm{true}$" means $H$ is neither the all-zero string nor $31$ zero bytes followed by $\mathtt{0x80}$.

### Commitment keys and the size hypotheses

A **`CommitmentKeys`** record $K$ has nine fields: byte strings $K.\mathrm{revPk}$, $K.\mathrm{revHash}$, $K.\mathrm{localDelayedPk}$, $K.\mathrm{remoteKey}$, $K.\mathrm{localHtlcKey}$, $K.\mathrm{remoteHtlcKey}$, $K.\mathrm{fundingKeyLocal}$, $K.\mathrm{fundingKeyRemote}$, and an integer $K.\mathrm{toSelfDelay} \in \mathbb Z$.

**`WellFormed`$(K)$** is the conjunction of ten facts: each of the eight byte-string fields has length $\le 520$, and $0 \le K.\mathrm{toSelfDelay} < 2^{16}$. Nothing else is required: the "keys" need not be valid public keys, $K.\mathrm{revHash}$ need not be 20 bytes, and no relation between $K.\mathrm{revHash}$ and $K.\mathrm{revPk}$ is imposed here.

An **`Htlc`** record $h$ has two fields: a byte string $h.\mathrm{payHash}$ and an integer $h.\mathrm{expiry} \in \mathbb Z$. **`HtlcWellFormed`$(h)$** is: $|h.\mathrm{payHash}| \le 520$ and $|h.\mathrm{expiry}| < 2^{32}$ (absolute value; $h.\mathrm{expiry}$ may be negative or zero).

### Script serialization primitives

* $\mathrm{pushBytes}(d)$: if $|d| < 76$, the byte $|d|$ followed by $d$; if $|d| \le 255$, $\mathtt{0x4c}, |d|$ then $d$; if $|d| \le 65535$, $\mathtt{0x4d}$, two little-endian length bytes, then $d$; otherwise $\mathtt{0x4e}$, four little-endian length bytes, then $d$. (For the empty string this is the single byte $\mathtt{0x00}$.)
* $\mathrm{serialize}(v)$ for $v \in \mathbb Z$ is the `CScriptNum` encoding: empty for $0$; otherwise the little-endian magnitude bytes with the sign carried in bit 7 of the last byte (an extra byte $\mathtt{0x00}$/$\mathtt{0x80}$ appended when the top bit of the magnitude is set).
* $\mathrm{numBytes}(n)$ for $n \in \mathbb Z$: if $n = -1$ or $1 \le n \le 16$, the single opcode byte $\mathtt{0x50} + n$ (so $\mathtt{0x4f}$ for $-1$, $\mathtt{0x51}$ = `OP_1` for $1$, $\mathtt{0x52}$ = `OP_2` for $2$, $\mathtt{0x60}$ = `OP_16` for $16$); otherwise $\mathrm{pushBytes}(\mathrm{serialize}(n))$ (so $\mathtt{0x00}$ for $0$, and $\mathtt{0x01}\,\mathtt{0x20}$ for $32$).

Opcode bytes used: `OP_IF` $=\mathtt{0x63}$, `OP_NOTIF` $=\mathtt{0x64}$, `OP_ELSE` $=\mathtt{0x67}$, `OP_ENDIF` $=\mathtt{0x68}$, `OP_IFDUP` $=\mathtt{0x73}$, `OP_DROP` $=\mathtt{0x75}$, `OP_DUP` $=\mathtt{0x76}$, `OP_SWAP` $=\mathtt{0x7c}$, `OP_SIZE` $=\mathtt{0x82}$, `OP_EQUAL` $=\mathtt{0x87}$, `OP_EQUALVERIFY` $=\mathtt{0x88}$, `OP_HASH160` $=\mathtt{0xa9}$, `OP_CHECKSIG` $=\mathtt{0xac}$, `OP_CHECKSIGVERIFY` $=\mathtt{0xad}$, `OP_CHECKMULTISIG` $=\mathtt{0xae}$, `OP_CHECKLOCKTIMEVERIFY` $=\mathtt{0xb1}$, `OP_CHECKSEQUENCEVERIFY` $=\mathtt{0xb2}$.

### The witness scripts (byte strings)

Writing $\langle d \rangle$ for $\mathrm{pushBytes}(d)$ and $[n]$ for $\mathrm{numBytes}(n)$:

* $\mathcal S_{\mathrm{toLocal}}(K) := $ `OP_IF` $\langle K.\mathrm{revPk}\rangle$ `OP_ELSE` $[K.\mathrm{toSelfDelay}]$ `OP_CHECKSEQUENCEVERIFY OP_DROP` $\langle K.\mathrm{localDelayedPk}\rangle$ `OP_ENDIF OP_CHECKSIG`.
* $\mathcal S_{\mathrm{off}}(K,h) := $ `OP_DUP OP_HASH160` $\langle K.\mathrm{revHash}\rangle$ `OP_EQUAL OP_IF OP_CHECKSIG OP_ELSE` $\langle K.\mathrm{remoteHtlcKey}\rangle$ `OP_SWAP OP_SIZE` $[32]$ `OP_EQUAL OP_NOTIF OP_DROP` $[2]$ `OP_SWAP` $\langle K.\mathrm{localHtlcKey}\rangle$ $[2]$ `OP_CHECKMULTISIG OP_ELSE OP_HASH160` $\langle h.\mathrm{payHash}\rangle$ `OP_EQUALVERIFY OP_CHECKSIG OP_ENDIF OP_ENDIF`.
* $\mathcal S_{\mathrm{rec}}(K,h) := $ `OP_DUP OP_HASH160` $\langle K.\mathrm{revHash}\rangle$ `OP_EQUAL OP_IF OP_CHECKSIG OP_ELSE` $\langle K.\mathrm{remoteHtlcKey}\rangle$ `OP_SWAP OP_SIZE` $[32]$ `OP_EQUAL OP_IF OP_HASH160` $\langle h.\mathrm{payHash}\rangle$ `OP_EQUALVERIFY` $[2]$ `OP_SWAP` $\langle K.\mathrm{localHtlcKey}\rangle$ $[2]$ `OP_CHECKMULTISIG OP_ELSE OP_DROP` $[h.\mathrm{expiry}]$ `OP_CHECKLOCKTIMEVERIFY OP_DROP OP_CHECKSIG OP_ENDIF OP_ENDIF`.
* $\mathcal S_{\mathrm{offA}}(K,h)$ (anchors): as $\mathcal S_{\mathrm{off}}(K,h)$ but with $[1]$ `OP_CHECKSEQUENCEVERIFY OP_DROP` inserted between the inner `OP_ENDIF` and the outer `OP_ENDIF`.
* $\mathcal S_{\mathrm{recA}}(K,h)$ (anchors): as $\mathcal S_{\mathrm{rec}}(K,h)$ with the same insertion.
* $\mathcal S_{\mathrm{toRemote}}(K) := \langle K.\mathrm{remoteKey}\rangle$ `OP_CHECKSIGVERIFY` $[1]$ `OP_CHECKSEQUENCEVERIFY`.
* $\mathcal S_{\mathrm{anchor}}(fk) := \langle fk\rangle$ `OP_CHECKSIG OP_IFDUP OP_NOTIF` $[16]$ `OP_CHECKSEQUENCEVERIFY OP_ENDIF`; $\mathcal S_{\mathrm{anchorLocal}}(K) := \mathcal S_{\mathrm{anchor}}(K.\mathrm{fundingKeyLocal})$, $\mathcal S_{\mathrm{anchorRemote}}(K) := \mathcal S_{\mathrm{anchor}}(K.\mathrm{fundingKeyRemote})$.

In the hash-and-key slots the scripts push whatever byte strings $K$ and $h$ hold; the file does not compute $K.\mathrm{revHash}$ or $h.\mathrm{payHash}$ from anything.

### `p2wshOf`

$\mathrm{p2wshOf}(\mathcal S) := \mathrm{witnessBytes}(0, \mathrm{sha256}(\mathcal S)) = \mathtt{0x00} \,\Vert\, \mathrm{pushBytes}(\mathrm{sha256}(\mathcal S)) = \mathtt{0x00}\,\mathtt{0x20}\,\Vert\,\mathrm{sha256}(\mathcal S)$, a 34-byte output script, where $\mathrm{sha256}$ is the concrete SHA-256 of the serialization file (a transcription of `crypto/sha256.cpp`).

### `oracleOf` — the concrete oracle

$o_{\mathcal S} := \mathrm{oracleOf}(c, \mathcal S) := \mathrm{legacyOracle}(\mathrm{sigFlagsOf}(c.\mathrm{flags}),\ c.tx,\ c.\mathrm{nIn},\ c.\mathrm{amount},\ \mathrm{witnessV0},\ \mathcal S)$. Its eight components are concrete:

* $o_{\mathcal S}.\mathrm{sha256}$, $o_{\mathcal S}.\mathrm{ripemd160}$, $o_{\mathcal S}.\mathrm{sha1}$, $o_{\mathcal S}.\mathrm{hash256} = \mathrm{sha256}\circ\mathrm{sha256}$ and $o_{\mathcal S}.\mathrm{hash160} = \mathrm{ripemd160}\circ\mathrm{sha256}$ are the transcribed hash functions of the serialization file (so "$o_{\mathcal S}.\mathrm{hash160}(x)$" is the concrete $\mathrm{RIPEMD160}(\mathrm{SHA256}(x))$, independent of $\mathcal S$ and $c$).
* $o_{\mathcal S}.\mathrm{checkSig}(sig, pk) := \mathrm{checkSigPreTapscript}(\mathrm{sigFlagsOf}(c.\mathrm{flags}), c.tx, c.\mathrm{nIn}, c.\mathrm{amount}, \mathrm{witnessV0}, \mathcal S, sig, pk) \in \{\mathrm{none}, \mathrm{some\ true}, \mathrm{some\ false}\}$, which is:
  - $\mathrm{none}$ (script failure) iff the encoding check fails. With the signature flags above (only $\mathrm{dersig}$ possibly on), the public-key encoding check always passes, and the signature encoding check fails exactly when $c.\mathrm{flags}.\mathrm{dersig} = \mathrm{true}$, $sig \ne []$ and $sig$ is not a strict-DER encoding (`IsValidSignatureEncoding`: length between 9 and 73, the `30 len 02 |r| r 02 |s| s hashtype` layout with the checks of that function). An empty $sig$ always passes the encoding check.
  - otherwise $\mathrm{some}(\mathrm{checkECDSASignature}(c.tx, c.\mathrm{nIn}, c.\mathrm{amount}, \mathrm{witnessV0}, sig, pk, \mathcal S))$, which is $\mathrm{true}$ iff: $pk$ is non-empty and its first byte announces its length (first byte $2$ or $3$ and $|pk| = 33$, or first byte $4$, $6$ or $7$ and $|pk| = 65$); $sig$ is non-empty, its last byte $ht$ being the hash type; $c.\mathrm{amount} \ge 0$; and `CPubKey::Verify` succeeds on $pk$, the BIP143 signature hash $\mathrm{sigHashWitnessV0}(\mathcal S, c.tx, c.\mathrm{nIn}, ht, c.\mathrm{amount})$ (a double-SHA256 of version, hashPrevouts, hashSequence, the outpoint of input $c.\mathrm{nIn}$ — the default empty input if $c.\mathrm{nIn}$ is out of range —, the length-prefixed $\mathcal S$, the amount, the input's sequence, hashOutputs, lock time and hash type) and $sig$ without its last byte: the key parses as a secp256k1 point, the signature parses under the lax DER parser, its $s$ is normalized to low-$s$, and the ECDSA verification equation holds with the message reduced modulo the group order. (No `FindAndDelete` is applied in the witness-v0 case.)
* $o_{\mathcal S}.\mathrm{checkLockTime}(L) := \mathrm{checkLockTime}(c.tx, c.\mathrm{nIn}, L)$ for $L \in \mathbb Z$: $\mathrm{true}$ iff $c.tx.\mathrm{nLockTime}$ and $L$ are on the same side of $500000000$ (both below, or both $\ge$), $L \le c.tx.\mathrm{nLockTime}$, and the sequence number of input $c.\mathrm{nIn}$ (see $\sigma$ below) is $\ne \mathtt{0xffffffff}$.
* $o_{\mathcal S}.\mathrm{checkSequence}(S) := \mathrm{checkSequence}(c.tx, c.\mathrm{nIn}, S)$ for $S \in \mathbb Z$: with $\sigma$ the sequence number of input $c.\mathrm{nIn}$, $\mathrm{true}$ iff $c.tx.\mathrm{version} \ge 2$, $\sigma \mathbin{\&} 2^{31} = 0$, and, with $m := 2^{22} \mathbin{|} \mathtt{0xffff}$, $\sigma_m := \sigma \mathbin{\&} m$ and $S_m := (\max(S,0)) \mathbin{\&} m$: $\sigma_m$ and $S_m$ are either both $< 2^{22}$ or both $\ge 2^{22}$, and $S_m \le \sigma_m$.

### `inputSequence`

$\sigma := \mathrm{inputSequence}(c.tx, c.\mathrm{nIn})$ is the $\mathrm{nSequence}$ field of the input at index $c.\mathrm{nIn}$ of $c.tx$; if $c.\mathrm{nIn} \ge |c.tx.\mathrm{vin}|$ it is the sequence of the default input, i.e. $\sigma = 0$. The same `getD` default is used inside $\mathrm{checkLockTime}$, $\mathrm{checkSequence}$ and the BIP143 hash.

### `CsvPasses` and `CltvPasses`

$$\mathrm{CsvPasses}(f, o, d) \iff f.\mathrm{csv} = \mathrm{false} \ \lor\ \bigl(0 \le d \ \land\ ((\max(d,0)) \mathbin{\&} 2^{31} \ne 0 \ \lor\ o.\mathrm{checkSequence}(d) = \mathrm{true})\bigr).$$

$$\mathrm{CltvPasses}(f, o, e) \iff f.\mathrm{cltv} = \mathrm{false} \ \lor\ \bigl(0 \le e \ \land\ o.\mathrm{checkLockTime}(e) = \mathrm{true}\bigr).$$

With $o = o_{\mathcal S}$ these are the concrete checks above on $c.tx$ and $c.\mathrm{nIn}$.

### `isFinalTx`

$\mathrm{isFinalTx}(tx, \mathrm{height}, \mathrm{blockTime})$ for $\mathrm{height} \in \mathbb N$, $\mathrm{blockTime} \in \mathbb Z$ is $\mathrm{true}$ iff: $tx.\mathrm{nLockTime} = 0$; or $tx.\mathrm{nLockTime} < \mathrm{height}$ when $tx.\mathrm{nLockTime} < 500000000$, resp. $tx.\mathrm{nLockTime} < \mathrm{blockTime}$ when $tx.\mathrm{nLockTime} \ge 500000000$; or every input of $tx$ has $\mathrm{nSequence} = \mathtt{0xffffffff}$ (vacuously true when $tx$ has no inputs).

### `verifyScript` on a P2WSH output with an empty scriptSig

For a witness script $\mathcal S$ and a witness list $w$ (in `CScriptWitness` order: the last element is on top of the stack), write
$$V(\mathcal S, w) :\iff \mathrm{verifyScript}(tap, c, [\,], \mathrm{p2wshOf}(\mathcal S), w) = \mathrm{true}.$$
Unfolding `verifyScript` with the empty scriptSig and the 34-byte output script $\mathtt{00}\,\mathtt{20}\,\Vert\,\mathrm{sha256}(\mathcal S)$:

1. The empty scriptSig evaluates to the empty stack; the output script evaluates (as a legacy script) to the one-element stack $[\mathrm{sha256}(\mathcal S)]$; the top must be true: **$\mathrm{castToBool}(\mathrm{sha256}(\mathcal S)) = \mathrm{true}$** is required.
2. If $c.\mathrm{flags}.\mathrm{witness} = \mathrm{true}$ (all theorems assume this), the output script is recognised as a witness program of version $0$ with program $\mathrm{sha256}(\mathcal S)$ (32 bytes); the scriptSig is empty as required; the P2SH flag and the P2SH branch are then irrelevant.
3. Version 0 with a 32-byte program: $w$ must be non-empty; its last element $\mathcal S'$ must satisfy $\mathrm{sha256}(\mathcal S') = \mathrm{sha256}(\mathcal S)$; then `executeWitnessScriptV0` runs on the stack $\mathrm{reverse}(w \text{ without its last element})$ and the script $\mathcal S'$. For $w = ws \mathbin{+\!\!+} [\mathcal S]$ this stack is $\mathrm{reverse}(ws)$ and the script is $\mathcal S$ itself.
4. `executeWitnessScriptV0`: every stack element has length $\le 520$; $|\mathcal S| \le 10000$; $\mathcal S$ parses instruction by instruction (`GetOp`); the Script-mission interpreter `evalScript` runs with flags $f = \mathrm{scriptFlagsOf}(c.\mathrm{flags})$ and oracle $o_{\mathcal S} = \mathrm{oracleOf}(c, \mathcal S)$ on that stack (with the usual limits: pushes $\le 520$ bytes, stack plus altstack $\le 1000$, at most $201$ counted opcodes, balanced conditionals, disabled opcodes rejected); it must succeed, leaving **exactly one** element, and $\mathrm{castToBool}$ of that element must be $\mathrm{true}$.

The Taproot handler $tap$ is not consulted on this path. So $V(\mathcal S, ws \mathbin{+\!\!+} [\mathcal S])$ is a decidable boolean fact about $c$, $K$, $h$ and $ws$ only.

### Interpreter facts used by the unfoldings

* `OP_CHECKSIG` pops $pk$ (top) and $sig$, calls $o.\mathrm{checkSig}(sig, pk)$: $\mathrm{none}$ fails the script; $\mathrm{some}\ b$ pushes $[\mathtt{0x01}]$ if $b$ else the empty string. `OP_CHECKSIGVERIFY` fails instead of pushing $\mathrm{false}$.
* `OP_CHECKSEQUENCEVERIFY` with $f.\mathrm{csv} = \mathrm{false}$ does nothing; otherwise it reads the top element as a script number of at most 5 bytes $n$ (without popping), fails if $n < 0$, passes if $n \mathbin{\&} 2^{31} \ne 0$, else fails unless $o.\mathrm{checkSequence}(n) = \mathrm{true}$. `OP_CHECKLOCKTIMEVERIFY` likewise with $f.\mathrm{cltv}$, no disable bit, and $o.\mathrm{checkLockTime}$.
* `OP_CHECKMULTISIG` with $[2]\ \langle k_1\rangle\ \langle k_2\rangle\ [2]$ uses the matching loop $\mathrm{multisigLoop}(o, [s_1, s_2], [k_1, k_2])$ and then pops one extra "dummy" element, failing if $f.\mathrm{nulldummy} = \mathrm{true}$ and the dummy is non-empty.
* $\mathrm{multisigLoop}(o, \mathrm{sigs}, \mathrm{keys})$: with no signatures left, $\mathrm{some\ true}$; with signatures but no keys, $\mathrm{some\ false}$; otherwise it checks the first signature against the first key: $\mathrm{none}$ propagates as $\mathrm{none}$; on $\mathrm{true}$ it drops both and continues (failing with $\mathrm{some\ false}$ if fewer keys than signatures remain); on $\mathrm{false}$ it drops only the key and continues (same count check). Instantiated on two signatures and two keys, $\mathrm{multisigLoop}(o, [s_1, s_2], [k_1, k_2]) = \mathrm{some\ true}$ iff $o.\mathrm{checkSig}(s_1, k_1) = \mathrm{some\ true}$ and $o.\mathrm{checkSig}(s_2, k_2) = \mathrm{some\ true}$.

### The two sides of the penalty (predicates on an oracle $o$ and $K$)

$$\mathrm{HoldsRevocation}(o, K) :\iff \bigl(\exists\, sig_R,\ |sig_R| \le 520 \ \land\ o.\mathrm{checkSig}(sig_R, K.\mathrm{revPk}) = \mathrm{some\ true}\bigr) \ \land\ o.\mathrm{hash160}(K.\mathrm{revPk}) = K.\mathrm{revHash}.$$

$$\mathrm{NoRevocationSig}(o, K) :\iff \forall\, sig,\ o.\mathrm{checkSig}(sig, K.\mathrm{revPk}) \ne \mathrm{some\ true}$$
(for every byte string $sig$ the oracle's answer is $\mathrm{none}$ or $\mathrm{some\ false}$).

$$\mathrm{NoRevHashPreimage}(o, K) :\iff \forall\, pk,\ o.\mathrm{hash160}(pk) = K.\mathrm{revHash} \Rightarrow pk = K.\mathrm{revPk}.$$

When $o = o_{\mathcal S} = \mathrm{oracleOf}(c, \mathcal S)$, $o.\mathrm{hash160}$ is the concrete $\mathrm{RIPEMD160}\circ\mathrm{SHA256}$ and $o.\mathrm{checkSig}$ is the concrete BIP143 ECDSA check on $c.tx$, $c.\mathrm{nIn}$, $c.\mathrm{amount}$ with script code $\mathcal S$ described above. So $\mathrm{NoRevHashPreimage}(o_{\mathcal S}, K)$ asserts that $K.\mathrm{revPk}$ is the **only** byte string in the whole of $\mathrm{Bytes}$ whose concrete hash160 is $K.\mathrm{revHash}$ (it does not by itself assert that $K.\mathrm{revPk}$ hashes to $K.\mathrm{revHash}$); and $\mathrm{NoRevocationSig}(o_{\mathcal S}, K)$ asserts that no byte string whatsoever passes the concrete signature check for $K.\mathrm{revPk}$ on this transaction, input, amount and script code.

### The penalty witnesses (`CScriptWitness` order, script last)

* $\mathrm{toLocalPenaltyWitness}(K, sig_R) := [\,sig_R,\ [\mathtt{0x01}],\ \mathcal S_{\mathrm{toLocal}}(K)\,]$; the executed stack (top first) is $[[\mathtt{0x01}], sig_R]$.
* $\mathrm{htlcPenaltyWitness}(K, sig_R, \mathcal S) := [\,sig_R,\ K.\mathrm{revPk},\ \mathcal S\,]$; the executed stack (top first) is $[K.\mathrm{revPk}, sig_R]$.

### The cheater-path predicates (on flags $f$, oracle $o$, keys $K$, HTLC $h$, and a top-first stack $st$)

$$\mathrm{DelayedSpend}(f, o, K, b, sig) :\iff \mathrm{castToBool}(b) = \mathrm{false} \ \land\ \mathrm{CsvPasses}(f, o, K.\mathrm{toSelfDelay}) \ \land\ o.\mathrm{checkSig}(sig, K.\mathrm{localDelayedPk}) = \mathrm{some\ true}.$$

$\mathrm{OfferedNonRevocation}(f, o, K, h, st)$ is the disjunction of:

* (preimage path) $\exists\, \mathrm{pre}, sig:\ st = [\mathrm{pre}, sig] \land o.\mathrm{hash160}(\mathrm{pre}) \ne K.\mathrm{revHash} \land |\mathrm{pre}| = 32 \land o.\mathrm{hash160}(\mathrm{pre}) = h.\mathrm{payHash} \land o.\mathrm{checkSig}(sig, K.\mathrm{remoteHtlcKey}) = \mathrm{some\ true}$;
* (timeout path) $\exists\, x, sig_L, sig_R', \mathrm{dummy}:\ st = [x, sig_L, sig_R', \mathrm{dummy}] \land o.\mathrm{hash160}(x) \ne K.\mathrm{revHash} \land |x| \ne 32 \land \mathrm{multisigLoop}(o, [sig_L, sig_R'], [K.\mathrm{localHtlcKey}, K.\mathrm{remoteHtlcKey}]) = \mathrm{some\ true} \land (f.\mathrm{nulldummy} = \mathrm{true} \Rightarrow \mathrm{dummy} = [\,])$.

$\mathrm{ReceivedNonRevocation}(f, o, K, h, st)$ is the disjunction of:

* (success path) $\exists\, \mathrm{pre}, sig_L, sig_R', \mathrm{dummy}:\ st = [\mathrm{pre}, sig_L, sig_R', \mathrm{dummy}] \land o.\mathrm{hash160}(\mathrm{pre}) \ne K.\mathrm{revHash} \land |\mathrm{pre}| = 32 \land o.\mathrm{hash160}(\mathrm{pre}) = h.\mathrm{payHash} \land \mathrm{multisigLoop}(o, [sig_L, sig_R'], [K.\mathrm{localHtlcKey}, K.\mathrm{remoteHtlcKey}]) = \mathrm{some\ true} \land (f.\mathrm{nulldummy} = \mathrm{true} \Rightarrow \mathrm{dummy} = [\,])$;
* (timeout path) $\exists\, x, sig:\ st = [x, sig] \land o.\mathrm{hash160}(x) \ne K.\mathrm{revHash} \land |x| \ne 32 \land \mathrm{CltvPasses}(f, o, h.\mathrm{expiry}) \land o.\mathrm{checkSig}(sig, K.\mathrm{remoteHtlcKey}) = \mathrm{some\ true}$.

$\mathrm{OfferedNonRevocationAnchors}(f, o, K, h, st) :\iff \mathrm{OfferedNonRevocation}(f, o, K, h, st) \land \mathrm{CsvPasses}(f, o, 1)$, and $\mathrm{ReceivedNonRevocationAnchors}(f, o, K, h, st) :\iff \mathrm{ReceivedNonRevocation}(f, o, K, h, st) \land \mathrm{CsvPasses}(f, o, 1)$.

In these predicates the stack $st$ is top-first; in the theorems it is instantiated with $\mathrm{reverse}(ws)$, i.e. the last element of the witness list $ws$ is the first element of $st$.
