# Read-back: `BitcoinHtlcLocks.received_spend_height`

**Declaration shape.** A theorem universally quantified over a Taproot handler, a verification context, four byte strings, an integer expiry, two further byte strings, a height and a block time, with eleven hypotheses; the conclusion is a disjunction of a "revocation spend" proposition and a strict integer inequality.

## Objects involved

**Byte strings.** A *byte* is an 8-bit vector; a *byte string* is a finite list of bytes. Lengths are natural numbers.

**Transactions.** A transaction $tx$ has a version $\in \mathbb{N}$, a list of inputs $\mathrm{vin}(tx)$, a list of outputs $\mathrm{vout}(tx)$ and a lock time $\mathrm{nLockTime}(tx) \in \mathbb{N}$. An input has a previous outpoint (byte string, index), a `scriptSig` byte string, a sequence number $\mathrm{nSequence} \in \mathbb{N}$ and a witness stack (list of byte strings). "The $k$-th input of $tx$ with default" is the zero-based $k$-th input when $k < |\mathrm{vin}(tx)|$, else the default input with outpoint (empty, $0$), empty `scriptSig`, $\mathrm{nSequence} = 0$, empty witness.

**Consensus flag set.** A record $F$ of seven Booleans: $F.\mathrm{p2sh}, F.\mathrm{witness}, F.\mathrm{taproot}, F.\mathrm{dersig}, F.\mathrm{cltv}, F.\mathrm{csv}, F.\mathrm{nulldummy}$. Two projections:

- interpreter flags $\mathrm{scriptFlagsOf}(F) = (F.\mathrm{cltv}, F.\mathrm{csv}, F.\mathrm{nulldummy})$;
- signature flags $\mathrm{sigFlagsOf}(F) = (\mathrm{dersig} = F.\mathrm{dersig},\ \mathrm{lowS} = \mathbf{false},\ \mathrm{strictenc} = \mathbf{false},\ \mathrm{witnessPubkeyType} = \mathbf{false})$.

**Verification context.** $c$ is a record $(c.\mathrm{flags}, c.\mathrm{tx}, c.\mathrm{nIn}, c.\mathrm{amount})$: a flag set, a transaction, an input index $\in \mathbb{N}$ and an amount $\in \mathbb{Z}$ (the statement places no sign constraint on the amount).

**Taproot handler.** $\mathit{tap}$ is an arbitrary function from (context, list of byte strings, byte string) to Booleans. It is unconstrained by any hypothesis.

**Constants.** $\mathrm{LOCKTIME\_THRESHOLD} = 500\,000\,000$; $\mathrm{SEQUENCE\_FINAL} = \mathtt{0xffffffff}$; $\mathrm{MAX\_SCRIPT\_ELEMENT\_SIZE} = 520$; $\mathrm{MAX\_SCRIPT\_SIZE} = 10\,000$.

**Hashes.** $\mathrm{sha256}$ is a concrete SHA-256 implementation on byte strings (32-byte output); $\mathrm{hash160}(m) = \mathrm{ripemd160}(\mathrm{sha256}(m))$ with a concrete RIPEMD-160.

## The received-HTLC script bytes $S$

Write $\mathrm{push}(d)$ for the canonical push of byte string $d$: if $|d| < 76$ it is the single length byte followed by $d$; if $|d| \le 255$ it is $\mathtt{0x4c}$, one length byte, $d$; if $|d| \le 65535$ it is $\mathtt{0x4d}$, two little-endian length bytes, $d$; otherwise $\mathtt{0x4e}$, four little-endian length bytes, $d$.

Write $\mathrm{num}(n)$ for $n \in \mathbb{Z}$: if $n = -1$ or $1 \le n \le 16$, the single byte $\mathtt{0x50} + n$ (so $\mathrm{num}(2) = [\mathtt{0x52}]$); otherwise $\mathrm{push}(\mathrm{ser}(n))$ where $\mathrm{ser}$ is the script-number encoding (empty for $0$; otherwise the minimal little-endian magnitude bytes, with an extra sign byte $\mathtt{0x80}$/$\mathtt{0x00}$ appended if the top bit of the last magnitude byte is set, else the sign folded into that top bit). In particular $\mathrm{num}(32) = [\mathtt{0x01}, \mathtt{0x20}]$.

Then, for byte strings $r$ (`revHash`), $K_r$ (`remoteKey`), $K_l$ (`localKey`), $p$ (`payHash`) and integer $e$ (`expiry`),

$$
\begin{aligned}
S = \mathrm{receivedBytes}(r, K_r, K_l, p, e) ={}& [\mathtt{0x76}, \mathtt{0xa9}] \mathbin{+\!\!+} \mathrm{push}(r) \mathbin{+\!\!+} [\mathtt{0x87}, \mathtt{0x63}, \mathtt{0xac}, \mathtt{0x67}] \mathbin{+\!\!+} \mathrm{push}(K_r) \mathbin{+\!\!+} [\mathtt{0x7c}, \mathtt{0x82}] \mathbin{+\!\!+} \mathrm{num}(32) \\
&\mathbin{+\!\!+} [\mathtt{0x87}, \mathtt{0x63}, \mathtt{0xa9}] \mathbin{+\!\!+} \mathrm{push}(p) \mathbin{+\!\!+} [\mathtt{0x88}] \mathbin{+\!\!+} \mathrm{num}(2) \mathbin{+\!\!+} [\mathtt{0x7c}] \mathbin{+\!\!+} \mathrm{push}(K_l) \mathbin{+\!\!+} \mathrm{num}(2) \\
&\mathbin{+\!\!+} [\mathtt{0xae}, \mathtt{0x67}, \mathtt{0x75}] \mathbin{+\!\!+} \mathrm{num}(e) \mathbin{+\!\!+} [\mathtt{0xb1}, \mathtt{0x75}, \mathtt{0xac}, \mathtt{0x68}, \mathtt{0x68}] .
\end{aligned}
$$

(The opcode bytes are: `0x76` DUP, `0xa9` HASH160, `0x87` EQUAL, `0x63` IF, `0xac` CHECKSIG, `0x67` ELSE, `0x7c` SWAP, `0x82` SIZE, `0x88` EQUALVERIFY, `0xae` CHECKMULTISIG, `0x75` DROP, `0xb1` CHECKLOCKTIMEVERIFY, `0x68` ENDIF.) The parsed-instruction form `receivedScript` is not used by this statement; only the byte form $S$ is.

## The output script and the witness

$\mathrm{witnessBytes}(0, P) = [\mathtt{0x00}] \mathbin{+\!\!+} \mathrm{push}(P)$. With $P = \mathrm{sha256}(S)$ (32 bytes) this is the 34-byte string $\mathtt{0x00}\ \mathtt{0x20}\ P$.

The witness list is $[\mathit{sig}, \mathit{pk}] \mathbin{+\!\!+} [S] = [\mathit{sig}, \mathit{pk}, S]$, in "last element on top" order.

## The verification predicate $\mathrm{verifyScript}(\mathit{tap}, c, \sigma, \pi, w)$

With scriptSig $\sigma$, scriptPubKey $\pi$ and witness list $w$, the Boolean is computed as follows. Let $\mathrm{evalBytes}(c, v, st, s)$ be: **failure** if $10\,000 < |s|$; **failure** if $s$ does not parse into instructions; otherwise the result of running the parsed script on top-first stack $st$ under interpreter flags $\mathrm{scriptFlagsOf}(c.\mathrm{flags})$ and the *legacy oracle* for signature version $v$ and script code $s$, which supplies the concrete hashes, $\mathrm{checkSig}(\mathit{sg}, \mathit{k}) = \mathrm{checkSigPreTapscript}(\mathrm{sigFlagsOf}(c.\mathrm{flags}), c.\mathrm{tx}, c.\mathrm{nIn}, c.\mathrm{amount}, v, s, \mathit{sg}, \mathit{k})$, $\mathrm{checkLockTime} = \mathrm{checkLockTime}(c.\mathrm{tx}, c.\mathrm{nIn}, \cdot)$ and $\mathrm{checkSequence} = \mathrm{checkSequence}(c.\mathrm{tx}, c.\mathrm{nIn}, \cdot)$. A stack's top is "true" ($\mathrm{topTrue}$) when the stack is non-empty and its top element is non-zero in the script sense: a byte string is true unless it is empty or every byte is $\mathtt{0x00}$ except possibly a final $\mathtt{0x80}$.

1. Run $\sigma$ (base version) on the empty stack; failure gives **false**; call the result $st_\sigma$.
2. Run $\pi$ (base version) on $st_\sigma$; failure gives **false**; if the top is not true, **false**.
3. If $c.\mathrm{flags}.\mathrm{witness}$ holds and $\pi$ is a *witness program* (length between 4 and 42, first byte either $\mathtt{0x00}$ or in $\mathtt{0x51}$..$\mathtt{0x60}$, and second byte $+ 2$ equal to the length; the version is $0$ for first byte $\mathtt{0x00}$ else first byte $- \mathtt{0x50}$, the program is the bytes after the second): if $\sigma \neq []$ the answer is **false**; otherwise the answer is $\mathrm{verifyWitnessProgram}(\mathit{tap}, c, w, \mathrm{version}, \mathrm{program}, \mathbf{false})$.
4. Otherwise (witness flag off, or $\pi$ not a witness program) a pay-to-script-hash branch is tried when $c.\mathrm{flags}.\mathrm{p2sh}$ holds and $\pi$ is the 23-byte pattern $\mathtt{0xa9}\ \mathtt{0x14}\ \langle 20 \text{ bytes}\rangle\ \mathtt{0x87}$; failing that, the answer is **false** if the witness flag is on and $w$ is non-empty, else **true**.

Here $\pi = \mathtt{0x00}\ \mathtt{0x20}\ P$ has length 34, first byte $\mathtt{0x00}$, second byte $32 = 34 - 2$, so step 3 applies with version $0$ and program $P$, and $\sigma = []$, so the hypothesis reduces to $\mathrm{verifyWitnessProgram}(\mathit{tap}, c, [\mathit{sig}, \mathit{pk}, S], 0, P, \mathbf{false}) = \mathbf{true}$ provided steps 1–2 pass (running the empty script, then running "push 32 bytes" and testing the pushed $P$ for truth).

$\mathrm{verifyWitnessProgram}$ with version $0$ and a 32-byte program: take the **last** witness element ($S$); if $\mathrm{sha256}$ of it differs from the program, **false** (here the program is $\mathrm{sha256}(S)$ itself); otherwise $\mathrm{executeWitnessScriptV0}(c, \text{reverse of the remaining elements}, S)$, i.e. with top-first stack $[\mathit{pk}, \mathit{sig}]$ ($\mathit{pk}$ on top). That is: **false** if some stack element exceeds $520$ bytes; else $\mathrm{evalBytes}(c, \mathrm{witnessV0}, [\mathit{pk}, \mathit{sig}], S)$ must succeed with a stack of exactly one element whose value is true. (So the 10 000-byte bound and the parsability of $S$, and the 520-byte bounds on $\mathit{pk}$ and $\mathit{sig}$, are enforced inside the hypothesis, not by separate hypotheses.) The Taproot handler $\mathit{tap}$ would only be consulted for version 1 programs and is not reached on this path.

**The lock-time checker used by CHECKLOCKTIMEVERIFY.** $\mathrm{checkLockTime}(tx, k, L)$ for $L \in \mathbb{Z}$ is **false** unless either ($\mathrm{nLockTime}(tx) < 500\,000\,000$ and $L < 500\,000\,000$) or ($500\,000\,000 \le \mathrm{nLockTime}(tx)$ and $500\,000\,000 \le L$); then **false** if $\mathrm{nLockTime}(tx) < L$ (integer comparison with the lock time cast); then **false** if the $k$-th input of $tx$ (with default) has $\mathrm{nSequence} = \mathtt{0xffffffff}$; else **true**. Whether the interpreter calls it at all is governed by the $\mathrm{cltv}$ interpreter flag, which hypothesis (hcltv) sets to true.

## The revocation-spend proposition

$\mathrm{RevocationSpend}(c, S, r, \mathit{pk}, \mathit{sig})$ is the conjunction

$$\mathrm{hash160}(\mathit{pk}) = r \;\wedge\; \mathrm{checkSigPreTapscript}\big(\mathrm{sigFlagsOf}(c.\mathrm{flags}),\ c.\mathrm{tx},\ c.\mathrm{nIn},\ c.\mathrm{amount},\ \mathrm{witnessV0},\ S,\ \mathit{sig},\ \mathit{pk}\big) = \mathrm{some}\ \mathbf{true} .$$

$\mathrm{checkSigPreTapscript}$ with version $\mathrm{witnessV0}$ uses the script code $S$ unchanged (no find-and-delete). It returns **no value** (hence not $\mathrm{some}\ \mathbf{true}$) if the signature-encoding check fails or the public-key-encoding check fails, and otherwise $\mathrm{some}$ of the ECDSA verdict. With signature flags $(F.\mathrm{dersig}, \mathbf{false}, \mathbf{false}, \mathbf{false})$: the signature-encoding check passes for an empty $\mathit{sig}$, fails when $F.\mathrm{dersig}$ holds and $\mathit{sig}$ is not a valid DER encoding, and passes otherwise; the public-key-encoding check always passes (both relevant flags are off). The ECDSA verdict $\mathrm{checkECDSASignature}(c.\mathrm{tx}, c.\mathrm{nIn}, c.\mathrm{amount}, \mathrm{witnessV0}, \mathit{sig}, \mathit{pk}, S)$ is **false** if $\mathit{pk}$ is not a valid public key; **false** if $\mathit{sig}$ is empty; otherwise, with the last byte of $\mathit{sig}$ as hash type and the rest as the raw signature, **false** if $c.\mathrm{amount} < 0$, else the outcome of verifying the raw signature with $\mathit{pk}$ against the witness-v0 signature hash of $(S, c.\mathrm{tx}, c.\mathrm{nIn}, \text{hash type}, c.\mathrm{amount})$.

## Statement

For every Taproot handler $\mathit{tap}$, every context $c$, every byte strings $r, K_r, K_l, p$, every integer $e$, every byte strings $\mathit{sig}, \mathit{pk}$, every $h \in \mathbb{N}$ (`height`) and $t \in \mathbb{Z}$ (`blockTime`), assuming

- (hf) $c.\mathrm{flags}.\mathrm{witness} = \mathbf{true}$;
- (hcltv) $c.\mathrm{flags}.\mathrm{cltv} = \mathbf{true}$;
- (hrev) $|r| \le 520$; (hrem) $|K_r| \le 520$; (hloc) $|K_l| \le 520$; (hpay) $|p| \le 520$;
- (hexp) $0 < e$ and $e < 500\,000\,000$ (integer comparisons; the constant is cast from $\mathbb{N}$);
- (hnIn) $c.\mathrm{nIn} < |\mathrm{vin}(c.\mathrm{tx})|$;
- (hv) $\mathrm{verifyScript}\big(\mathit{tap}, c, [],\ \mathrm{witnessBytes}(0, \mathrm{sha256}(S)),\ [\mathit{sig}, \mathit{pk}, S]\big) = \mathbf{true}$ with $S = \mathrm{receivedBytes}(r, K_r, K_l, p, e)$;
- (hfinal) $\mathrm{isFinalTx}(c.\mathrm{tx}, h, t) = \mathbf{true}$, where $\mathrm{isFinalTx}$ is: true if $\mathrm{nLockTime}(c.\mathrm{tx}) = 0$; else true if $\mathrm{nLockTime}(c.\mathrm{tx})$ (cast to $\mathbb{Z}$) is strictly less than $h$ (cast to $\mathbb{Z}$) when $\mathrm{nLockTime}(c.\mathrm{tx}) < 500\,000\,000$, or strictly less than $t$ otherwise; else true exactly when every input of $c.\mathrm{tx}$ has $\mathrm{nSequence} = \mathtt{0xffffffff}$;

the conclusion is

$$\mathrm{RevocationSpend}(c, S, r, \mathit{pk}, \mathit{sig}) \;\;\vee\;\; e < h ,$$

where the inequality compares the integer $e$ with the natural number $h$ cast to $\mathbb{Z}$.

## Edge cases made explicit

- No hypothesis fixes $|r|$ or $|p|$ to 20 bytes, or $|K_r|, |K_l|$ to 33 bytes; they are bounded only above by 520. No hypothesis bounds $|\mathit{sig}|$ or $|\mathit{pk}|$ directly; the 520-byte bound on them is enforced only inside (hv).
- $c.\mathrm{flags}.\mathrm{p2sh}$, $\mathrm{taproot}$, $\mathrm{dersig}$, $\mathrm{csv}$, $\mathrm{nulldummy}$ are unconstrained; $c.\mathrm{amount}$ may be negative (in which case the ECDSA verdict is false, so the first disjunct cannot hold through a verified signature).
- $\mathrm{nLockTime}(c.\mathrm{tx})$ is unconstrained by the hypotheses: it may be $0$ (then (hfinal) holds automatically), below the threshold (compared with $h$), or at/above it (compared with $t$, in which case $h$ is not consulted by (hfinal)). $t$ is otherwise unused.
- (hnIn) guarantees the $c.\mathrm{nIn}$-th input exists, so the default input never arises in $\mathrm{checkLockTime}$ or $\mathrm{checkSequence}$; the sequence number of that input is not constrained by any hypothesis.
- $h$ may be $0$. The disjunction is inclusive: both disjuncts may hold.
- (hexp) is on the integer $e$; the conclusion's $e < h$ is also an integer comparison. $\mathrm{num}(e)$ in $S$ is a one-byte opcode when $1 \le e \le 16$ and a script-number push otherwise.
