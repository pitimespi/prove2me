# Read-back: `BitcoinReorg.validate_equiv`

## Notions used

**Ledgers and coin lookup.** A *ledger* $u$ is a finite list of pairs $(p, c)$, where $p$ is an *outpoint* (a byte string $p.\mathrm{hash}$ and a natural number $p.n$) and $c$ is a *coin* (an output $c.\mathrm{out}$ consisting of an integer value $c.\mathrm{out}.\mathrm{nValue}$ and a byte-string script $c.\mathrm{out}.\mathrm{scriptPubKey}$; a natural-number creation height $c.\mathrm{height}$; and a Boolean coinbase flag $c.\mathrm{isCoinbase}$). The lookup $\mathrm{getCoin}(u, p)$ scans $u$ from the front and returns the coin of the *first* pair whose outpoint equals $p$ (as a value "some $c$"), or "none" if no pair has outpoint $p$; any later pair with the same outpoint is shadowed and never consulted. Two ledgers are *equivalent*, written $u \sim v$, when
$$\forall p,\quad \mathrm{getCoin}(u, p) = \mathrm{getCoin}(v, p),$$
the quantifier ranging over every outpoint (every byte string and every natural number). Equivalence says nothing about the order of the lists, about duplicate or shadowed entries, or about list length.

**Spending and adding coins.** $\mathrm{spendCoin}(u, p)$ is $u$ with *every* pair whose outpoint equals $p$ removed. A script byte string $s$ is *unspendable* when it is non-empty and its first byte is the opcode $\mathtt{OP\_RETURN}$, or when its length exceeds the constant $\mathrm{MAX\_SCRIPT\_SIZE}$. $\mathrm{addCoin}(u, p, c)$ is $u$ unchanged if $c.\mathrm{out}.\mathrm{scriptPubKey}$ is unspendable, and otherwise is the pair $(p, c)$ prepended to $\mathrm{spendCoin}(u, p)$.

**Transactions.** A transaction $tx$ has a natural-number version, a list of inputs $tx.\mathrm{vin}$ (each input $i$ has an outpoint $i.\mathrm{prevout}$, a script $i.\mathrm{scriptSig}$, a natural number $i.\mathrm{nSequence}$, and a witness stack, a list of byte strings), a list of outputs $tx.\mathrm{vout}$ (each an integer value and a script), and a natural number $tx.\mathrm{nLockTime}$. $tx$ *is a coinbase* exactly when $tx.\mathrm{vin}$ has exactly one input and that input's outpoint is the null outpoint (hash equal to 32 zero bytes and index $n = 2^{32} - 1$). $\mathrm{txid}(tx)$ is the double SHA-256 of the serialization of $tx$ with all witness data stripped.

**The ledger update $\mathrm{updateCoins}(u, tx, h)$**, for a ledger $u$, a transaction $tx$ and a natural number $h$: let $u_1 = u$ if $tx$ is a coinbase, and otherwise let $u_1$ be $u$ with $\mathrm{spendCoin}$ applied successively for the outpoint $i.\mathrm{prevout}$ of every input $i$ of $tx$ in order (no check is made that those outpoints are present). Then, for the outputs $o_0, o_1, \dots, o_{k-1}$ of $tx$ in order, apply successively
$$u_{j+1} = \mathrm{addCoin}\big(u_j,\ (\mathrm{txid}(tx), j),\ \langle o_j,\ h,\ \text{isCoinbase}(tx)\rangle\big),$$
and the result is $u_k$. Outputs with unspendable scripts are therefore not stored, and each stored output replaces (after removal of) any earlier entry with the same outpoint.

**Chain states.** A *chain state* $S$ is a pair of a list of headers $S.\mathrm{headers}$ and a ledger $S.\mathrm{utxo}$. A header has an integer version, byte strings $\mathrm{prevBlock}$ and $\mathrm{merkleRoot}$, and natural numbers $\mathrm{time}$, $\mathrm{bits}$, $\mathrm{nonce}$; $\mathrm{headerHash}(h)$ is the double SHA-256 of its 80-byte serialization. A block $b$ is a header $b.\mathrm{header}$ and a list of transactions $b.\mathrm{vtx}$. Derived quantities of a state $S$ with $n = |S.\mathrm{headers}|$:

- $\mathrm{tipHeight}(S) = n - 1$ with *truncated* natural-number subtraction, so it is $0$ both when $n = 1$ and when $n = 0$;
- $\mathrm{nextHeight}(S) = n$;
- $\mathrm{tip}(S)$ is the last header of the list, or the fixed genesis header if the list is empty; $\mathrm{tipHash}(S) = \mathrm{headerHash}(\mathrm{tip}(S))$;
- $\mathrm{mtp}(S)$ ("median time past"): take the times of the headers at indices $0, \dots, \mathrm{tipHeight}(S)$, list them most recent first, keep the first $11$, sort ascending, and take the element at index $\lfloor \ell / 2 \rfloor$ where $\ell$ is the length of that window ($0$ if the window is empty); $\mathrm{mtpNat}(S, h)$ is the same computation for the headers at indices $0..h$, converted to a natural number (negative values become $0$);
- $\mathrm{requiredBits}(S)$: let $f$ be the header at index $\mathrm{tipHeight}(S) - 2015$ (truncated subtraction; the genesis header if the index is out of range); if $(\mathrm{tipHeight}(S) + 1) \bmod 2016 \neq 0$ the result is the tip's $\mathrm{bits}$ field, otherwise it is the retargeted compact difficulty computed by the transcribed difficulty-adjustment routine from the tip's bits and time and $f$'s time.

The *initial state* is $\langle [\text{genesisHeader}],\ [\,]\rangle$: the single fixed genesis header and the empty ledger. $\mathrm{genesisHash}$ is a fixed 32-byte constant.

**State equivalence.** Two chain states are *equivalent*, written $S \approx T$ (the file's `StateEquiv`), when
$$S.\mathrm{headers} = T.\mathrm{headers} \quad\text{and}\quad S.\mathrm{utxo} \sim T.\mathrm{utxo},$$
i.e. the header lists are literally equal (same length, same headers in the same order) and the ledgers are equivalent in the sense above.

**The validation outcome $\mathrm{validate}(S, b, t)$**, for a chain state $S$, a block $b$ and an integer clock reading $t$, is one of four outcomes: $\mathrm{accept}(S', \mathit{undo})$ carrying a new state and undo data, $\mathrm{invalid}$, $\mathrm{futureTime}$, or $\mathrm{missingPrev}$. It is computed by the following sequence of tests, the first failing test deciding the outcome. Write $h = b.\mathrm{header}$.

*Header path.*
1. If the proof-of-work test fails — the header hash read as a little-endian 256-bit integer exceeds the target decoded from $h.\mathrm{bits}$, or $h.\mathrm{bits}$ decodes to a negative, zero, overflowing, or above-limit target — the outcome is $\mathrm{invalid}$.
2. Else if $h.\mathrm{prevBlock} \neq \mathrm{tipHash}(S)$, the outcome is $\mathrm{missingPrev}$.
3. Else if $h.\mathrm{bits} \neq \mathrm{requiredBits}(S)$ (as 32-bit words), the outcome is $\mathrm{invalid}$.
4. Else if $h.\mathrm{time} \le \mathrm{mtp}(S)$, the outcome is $\mathrm{invalid}$.
5. Else if $t + 7200 < h.\mathrm{time}$, the outcome is $\mathrm{futureTime}$.
6. Else if the version is outdated — $(h.\mathrm{version} < 2 \wedge 227931 \le \mathrm{tipHeight}(S) + 1) \vee (h.\mathrm{version} < 3 \wedge 363725 \le \mathrm{tipHeight}(S) + 1) \vee (h.\mathrm{version} < 4 \wedge 388381 \le \mathrm{tipHeight}(S) + 1)$ — the outcome is $\mathrm{invalid}$.

*Context-free block check* (`checkBlock`): the outcome is $\mathrm{invalid}$ unless all of the following hold: the proof-of-work test of step 1 again; the Merkle root computed from the txids of $b.\mathrm{vtx}$ equals $h.\mathrm{merkleRoot}$ and the Merkle computation does not report a duplicated-subtree mutation; $b.\mathrm{vtx}$ is non-empty; $4\,|b.\mathrm{vtx}| \le 4{,}000{,}000$; four times the length of the witness-stripped serialization of $b$ is at most $4{,}000{,}000$; the first transaction is a coinbase; every other transaction is not a coinbase; every transaction passes `checkTransaction` (non-empty inputs and outputs; four times its witness-stripped size at most $4{,}000{,}000$; every output value in $[0, 21\cdot 10^{14}]$ with the running total staying in that range; input outpoints pairwise distinct; for a coinbase the first input's scriptSig has length in $[2, 100]$, for a non-coinbase no input has the null outpoint); and four times the sum of the legacy signature-operation counts of all transactions is at most $80{,}000$.

*Contextual block check* (`contextualCheckBlock`), with height $H = \mathrm{nextHeight}(S)$ and cutoff $c = \mathrm{mtp}(S)$ if $419328 \le \mathrm{tipHeight}(S) + 1$ and $c = h.\mathrm{time}$ otherwise: the outcome is $\mathrm{invalid}$ unless every transaction $tx$ is final ($tx.\mathrm{nLockTime} = 0$, or $tx.\mathrm{nLockTime} < H$ when $tx.\mathrm{nLockTime} < 5\cdot 10^8$ and $tx.\mathrm{nLockTime} < c$ otherwise, or every input has $\mathrm{nSequence} = 2^{32}-1$); unless, when $227931 \le \mathrm{tipHeight}(S) + 1$, the canonical script push of $H$ is a prefix of the coinbase's first input scriptSig; unless the witness-commitment check passes with "expected" set to $481824 \le \mathrm{tipHeight}(S) + 1$ (when not expected: no transaction carries witness data; when expected: if no coinbase output is a commitment output then no transaction carries witness data, else the coinbase's first-input witness stack is a single 32-byte nonce and the double SHA-256 of the witness Merkle root concatenated with that nonce equals bytes 6–37 of the last commitment output's script); and unless the block weight (three times the witness-stripped serialized length plus the full serialized length) is at most $4{,}000{,}000$.

*Ledger connection.* Finally $\mathrm{connectBlock}(S, b)$ (expanded below) is computed; if it is "none" the outcome is $\mathrm{invalid}$, and if it is "some $(u, \mathit{undo})$" the outcome is
$$\mathrm{accept}\big(\langle S.\mathrm{headers} \mathbin{+\!\!+} [h],\ u\rangle,\ \mathit{undo}\big),$$
the header appended at the end of the list and the ledger replaced by $u$.

**The ledger connection $\mathrm{connectBlock}(S, b)$** returns either "none" or "some $(u, \mathit{undo})$" with $u$ a ledger and $\mathit{undo}$ a list of lists of coins. Let $\eta = \mathrm{headerHash}(b.\mathrm{header})$ and $H = \mathrm{nextHeight}(S)$.

- If $\eta = \mathrm{genesisHash}$, the result is "some $(S.\mathrm{utxo}, [\,])$": the ledger is unchanged and the undo data is the empty list, whatever $b.\mathrm{vtx}$ contains.
- Else, the BIP30 scan is *required* when $\big(\neg\mathrm{isBIP30Repeat}(H, \eta) \wedge \neg\beta\big) \vee 1983702 \le H$, where $\mathrm{isBIP30Repeat}$ holds only for $(H, \eta) \in \{(91842, \text{a fixed hash}), (91880, \text{a fixed hash})\}$ and $\beta$ holds when $S.\mathrm{headers}$ has an entry at index $227931$ whose hash is the fixed BIP34 hash. If the scan is required and some transaction $tx \in b.\mathrm{vtx}$ and some index $o < |tx.\mathrm{vout}|$ have $\mathrm{getCoin}(S.\mathrm{utxo}, (\mathrm{txid}(tx), o)) \neq \text{none}$, the result is "none".
- Else, with the script flags determined by $H$ and by whether $\eta$ is one of two fixed exception hashes, the transactions of $b.\mathrm{vtx}$ are processed in order starting from the accumulator $(\text{ledger } S.\mathrm{utxo},\ \text{fees } 0,\ \text{sigops } 0,\ \text{undo } [\,])$. For each $tx$ with current ledger $w$:
  - if $tx$ is a coinbase, fees and undo are unchanged;
  - otherwise `checkTxInputs` must succeed: every input outpoint has a coin in $w$; for each input coin $c$ in order, it is not the case that $c.\mathrm{isCoinbase}$ and $H - c.\mathrm{height} < 100$ (truncated subtraction, so a coinbase coin with $c.\mathrm{height} > H$ counts as immature), $c.\mathrm{out}.\mathrm{nValue}$ and the running input total are in $[0, 21\cdot 10^{14}]$; the input total is at least the output total of $tx$; and the fee (input total minus output total) is in $[0, 21\cdot 10^{14}]$; then the accumulated fees plus this fee must be in $[0, 21\cdot 10^{14}]$; the transcribed BIP68 sequence-lock check against $H$, the median-time-past function $\mathrm{mtpNat}(S, \cdot)$, the lock-time flags of $H$, and the heights of the spent coins must pass; and the list $\mathrm{txUndo}(w, tx)$ — for each input in order, the coin at its outpoint in $w$, or the dummy coin $\langle\langle -1, [\,]\rangle, 0, \mathrm{false}\rangle$ if absent — is appended to the undo list;
  - then the accumulated sigop cost is increased by the transaction's sigop cost (legacy count times 4, plus, for a non-coinbase, the P2SH count times 4 when the P2SH flag is set and the witness sigop count), and must not exceed $80{,}000$;
  - then, for a non-coinbase, every input's script must verify under the full transcribed script interpreter (with the spent outputs supplied);
  - the ledger becomes $\mathrm{updateCoins}(w, tx, H)$.
  Any failure yields "none".
- After the loop, if the output total of the first transaction of $b$ (the fixed genesis coinbase if $b.\mathrm{vtx}$ is empty) exceeds the accumulated fees plus the subsidy at height $H$ (namely $50 \cdot 10^8$ shifted right by $\lfloor H / 210000 \rfloor$, and $0$ once that quotient is at least $64$), the result is "none"; otherwise it is "some (final ledger, final undo list)".

When the result is "some $(u, \mathit{undo})$" and $\eta \neq \mathrm{genesisHash}$, $\mathit{undo}$ has exactly one entry per non-coinbase transaction of $b$, in block order.


## Statement

**Binders.** Chain states $S$ and $T$; a hypothesis $h : S \approx T$, i.e. $S.\mathrm{headers} = T.\mathrm{headers}$ and $S.\mathrm{utxo} \sim T.\mathrm{utxo}$; a block $b$; and an integer clock reading $t$. Nothing else is assumed: $S$ need not be reachable or well-formed, its header list may be empty or not start at the genesis header, and $b$ is arbitrary.

**Conclusion.** A four-way disjunction; the statement asserts that at least one of the following holds:

1. $\mathrm{validate}(S, b, t) = \mathrm{invalid}$ and $\mathrm{validate}(T, b, t) = \mathrm{invalid}$;
2. $\mathrm{validate}(S, b, t) = \mathrm{futureTime}$ and $\mathrm{validate}(T, b, t) = \mathrm{futureTime}$;
3. $\mathrm{validate}(S, b, t) = \mathrm{missingPrev}$ and $\mathrm{validate}(T, b, t) = \mathrm{missingPrev}$;
4. there exist chain states $S'$, $T'$ and undo data $\mathit{undo}$ with
$$\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo}),\qquad \mathrm{validate}(T, b, t) = \mathrm{accept}(T', \mathit{undo}),\qquad S' \approx T'.$$

In alternative 4 the undo data is the same list on both sides, and the accepted states are equivalent: by the definition of $\mathrm{validate}$ each has header list $S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}]$ (equal on both sides since the input header lists are equal), and their ledgers — the outputs of $\mathrm{connectBlock}$ — are asserted equivalent, not equal.

**Edge cases the statement includes.** Every test on the header path, the context-free block check and the contextual block check reads only the header list and $b$, so under the hypothesis they agree on $S$ and $T$ by construction; the content of the claim lies in $\mathrm{connectBlock}$, which reads the ledger. The ordering of the header tests is part of what is asserted: for instance, a block whose time exceeds $t + 7200$ but whose $\mathrm{bits}$ do not match the required bits yields $\mathrm{invalid}$, not $\mathrm{futureTime}$. When $\mathrm{headerHash}(b.\mathrm{header}) = \mathrm{genesisHash}$ and the header and block checks pass, alternative 4 holds with $S'$ and $T'$ carrying the unchanged ledgers of $S$ and $T$ and empty undo data.
