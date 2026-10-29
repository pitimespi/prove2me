# Read-back: `BitcoinHtlcLocks.presigned_timeout_height`

**Declaration shape.** This is a theorem with a universally quantified transaction, two natural numbers (an expiry and a height), an integer block time, an input index, and five hypotheses; the conclusion is a single strict inequality between natural numbers (one direction only, not a bi-implication).

**Objects involved.** A *transaction* $tx$ is a record with four fields: a version number $\mathrm{version}(tx) \in \mathbb{N}$, a finite list of inputs $\mathrm{vin}(tx)$, a finite list of outputs $\mathrm{vout}(tx)$, and a lock time $\mathrm{nLockTime}(tx) \in \mathbb{N}$ (a natural number, not bounded by the statement to 32 bits). An *input* is a record with a previous outpoint (a byte string together with a natural-number index), a byte string `scriptSig`, a sequence number $\mathrm{nSequence} \in \mathbb{N}$, and a witness stack (a list of byte strings). Two constants:

$$\mathrm{LOCKTIME\_THRESHOLD} = 500\,000\,000, \qquad \mathrm{SEQUENCE\_FINAL} = \mathtt{0xffffffff} = 4\,294\,967\,295 .$$

**The finality predicate.** For a transaction $tx$, a height $h \in \mathbb{N}$ and a block time $t \in \mathbb{Z}$, the Boolean $\mathrm{isFinalTx}(tx, h, t)$ is defined by three cases, tried in order:

1. if $\mathrm{nLockTime}(tx) = 0$, the value is **true**;
2. otherwise, let $L = \mathrm{nLockTime}(tx)$ cast to an integer, and let the comparison target be $h$ (cast to $\mathbb{Z}$) when $\mathrm{nLockTime}(tx) < 500\,000\,000$ (as natural numbers) and $t$ otherwise; if $L <$ target (as integers), the value is **true**;
3. otherwise the value is **true** exactly when every input of $\mathrm{vin}(tx)$ has $\mathrm{nSequence} = \mathtt{0xffffffff}$ (vacuously true for an empty input list), and **false** otherwise.

The block time $t$ is consulted only when the lock time is at or above $500\,000\,000$.

**The indexed-input access.** "The $i$-th input of $tx$ with default" is the zero-based $i$-th element of $\mathrm{vin}(tx)$ when $i < |\mathrm{vin}(tx)|$, and otherwise the default input with outpoint (empty byte string, $0$), empty `scriptSig`, $\mathrm{nSequence} = 0$ and empty witness. In this theorem the hypothesis $i < |\mathrm{vin}(tx)|$ is present, so the default is never selected.

**Statement.** For every transaction $tx$, every $\mathrm{expiry} \in \mathbb{N}$, every $h \in \mathbb{N}$ (`height`), every $t \in \mathbb{Z}$ (`blockTime`), assuming

- (hexp) $0 < \mathrm{expiry}$ and $\mathrm{expiry} < 500\,000\,000$ (both as natural numbers);
- (htx) $\mathrm{nLockTime}(tx) = \mathrm{expiry}$;
- for every $i \in \mathbb{N}$ with (hi) $i < |\mathrm{vin}(tx)|$;
- (hseq) the $i$-th input of $tx$ (with the default described above) has $\mathrm{nSequence} \neq \mathtt{0xffffffff}$;
- (hfinal) $\mathrm{isFinalTx}(tx, h, t) = \mathbf{true}$;

it follows that

$$\mathrm{expiry} < h ,$$

a strict inequality between natural numbers.

**Edge cases made explicit.**

- By (htx) and (hexp), $\mathrm{nLockTime}(tx) = \mathrm{expiry}$ is non-zero and strictly below the threshold, so case 1 of $\mathrm{isFinalTx}$ does not apply and in case 2 the comparison target is the height $h$; the block time $t$ is an unconstrained binder not used by the conclusion.
- (hi) forces $\mathrm{vin}(tx)$ to be non-empty, and (hseq) singles out one input whose sequence number is not $\mathtt{0xffffffff}$.
- Only one direction is asserted: from finality to $\mathrm{expiry} < h$. The converse is not part of this statement.
- No hypothesis constrains $h$ (it may be $0$, in which case the hypotheses would have to be jointly unsatisfiable for the conclusion to hold), $\mathrm{version}(tx)$, $\mathrm{vout}(tx)$, or the sequence numbers of inputs other than the $i$-th.
- The hypothesis (hexp) is stated on the natural number $\mathrm{expiry}$; the comparison inside $\mathrm{isFinalTx}$ is on integer casts of natural numbers.
