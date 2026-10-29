# Read-back: `BitcoinHtlcLocks.isFinalTx_height`

**Declaration shape.** This is a theorem with a universally quantified transaction, a height, a block time, an input index, and three hypotheses, whose conclusion is a bi-implication.

**Objects involved.** A *transaction* $tx$ is a record with four fields: a version number $\mathrm{version}(tx) \in \mathbb{N}$, a finite list of inputs $\mathrm{vin}(tx)$, a finite list of outputs $\mathrm{vout}(tx)$, and a lock time $\mathrm{nLockTime}(tx) \in \mathbb{N}$ (a natural number, not bounded by the statement to 32 bits). An *input* is a record with four fields: a previous outpoint (a byte string "hash" together with a natural-number index), a byte string `scriptSig`, a sequence number $\mathrm{nSequence} \in \mathbb{N}$, and a list of byte strings (the witness stack). Two constants are used:

$$\mathrm{LOCKTIME\_THRESHOLD} = 500\,000\,000, \qquad \mathrm{SEQUENCE\_FINAL} = \mathtt{0xffffffff} = 4\,294\,967\,295 .$$

**The finality predicate.** For a transaction $tx$, a height $h \in \mathbb{N}$ and a block time $t \in \mathbb{Z}$, the Boolean $\mathrm{isFinalTx}(tx, h, t)$ is defined by three cases, tried in order:

1. if $\mathrm{nLockTime}(tx) = 0$, the value is **true**;
2. otherwise, let $L = \mathrm{nLockTime}(tx)$ regarded as an integer, and let the comparison target be $h$ (cast from $\mathbb{N}$ to $\mathbb{Z}$) when $\mathrm{nLockTime}(tx) < 500\,000\,000$ (as natural numbers), and $t$ otherwise; if $L <$ target (as integers) the value is **true**;
3. otherwise the value is **true** exactly when *every* input in $\mathrm{vin}(tx)$ has $\mathrm{nSequence} = \mathtt{0xffffffff}$ (so, in particular, this case yields true when $\mathrm{vin}(tx)$ is empty), and **false** when at least one input has a different sequence number.

Note that in case 2 the block time $t$ is only consulted when the lock time is at or above $500\,000\,000$; for lock times strictly below the threshold the height is the only quantity compared.

**The "height-locked" predicate.** $\mathrm{HeightLocked}(tx)$ is the proposition

$$0 < \mathrm{nLockTime}(tx) \;\wedge\; \mathrm{nLockTime}(tx) < 500\,000\,000 ,$$

both comparisons on natural numbers.

**The indexed-input access.** For a natural number $i$, the expression "the $i$-th input of $tx$ with default" denotes the $i$-th element of $\mathrm{vin}(tx)$ (zero-based) when $i < |\mathrm{vin}(tx)|$, and otherwise the default input whose previous outpoint is (empty byte string, $0$), whose `scriptSig` is empty, whose $\mathrm{nSequence}$ is $0$, and whose witness stack is empty. In this theorem the hypothesis $i < |\mathrm{vin}(tx)|$ is present, so the default is never selected and the expression is the genuine $i$-th input.

**Statement.** For every transaction $tx$, every $h \in \mathbb{N}$ (`height`), every $t \in \mathbb{Z}$ (`blockTime`), assuming

- (hl) $\mathrm{HeightLocked}(tx)$, i.e. $0 < \mathrm{nLockTime}(tx) < 500\,000\,000$;
- for every $i \in \mathbb{N}$ with (hi) $i < |\mathrm{vin}(tx)|$ and
- (hseq) the $i$-th input of $tx$ (with the default described above) has $\mathrm{nSequence} \neq \mathtt{0xffffffff}$,

the following bi-implication holds:

$$\mathrm{isFinalTx}(tx, h, t) = \mathbf{true} \quad\Longleftrightarrow\quad \mathrm{nLockTime}(tx) < h ,$$

where the right-hand comparison is between natural numbers (no cast), while the comparison inside $\mathrm{isFinalTx}$ is between the integer casts of the same two natural numbers.

**Edge cases made explicit.**

- Under (hl), $\mathrm{nLockTime}(tx) \neq 0$, so case 1 of $\mathrm{isFinalTx}$ does not apply, and $\mathrm{nLockTime}(tx) < 500\,000\,000$, so in case 2 the comparison target is $h$ and the block time $t$ is never consulted; $t$ is an unconstrained binder that does not appear in the conclusion.
- Under (hi), $\mathrm{vin}(tx)$ is non-empty (it has at least $i+1$ elements), so the "all inputs final" case 3 is not vacuous; (hseq) names one specific input whose sequence number is not $\mathtt{0xffffffff}$.
- No hypothesis restricts $h$ (it may be $0$), $\mathrm{version}(tx)$, $\mathrm{vout}(tx)$, or the other inputs' sequence numbers.
- The statement is an "if and only if": it asserts both that finality implies $\mathrm{nLockTime}(tx) < h$ and that $\mathrm{nLockTime}(tx) < h$ implies finality, under the stated hypotheses.
