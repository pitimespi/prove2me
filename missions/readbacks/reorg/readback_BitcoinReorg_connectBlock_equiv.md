# Read-back: `BitcoinReorg.connectBlock_equiv`

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

**Binders.** A list of headers $\mathcal H$; two ledgers $u$ and $v$; a hypothesis $h : u \sim v$ ($\forall p,\ \mathrm{getCoin}(u, p) = \mathrm{getCoin}(v, p)$); and a block $b$. The two chain states considered are $\langle \mathcal H, u\rangle$ and $\langle \mathcal H, v\rangle$: the same header list with the two ledgers. No condition is placed on $\mathcal H$ (it may be empty, need not start with the genesis header), on $b$ (it need not pass any header or block check — only $\mathrm{connectBlock}$ is applied, not $\mathrm{validate}$), or on $u$, $v$ beyond equivalence.

**Conclusion.** Exactly one of the following two alternatives is asserted to hold (as a disjunction):

1. $\mathrm{connectBlock}(\langle \mathcal H, u\rangle, b) = \text{none}$ and $\mathrm{connectBlock}(\langle \mathcal H, v\rangle, b) = \text{none}$; or
2. there exist ledgers $u'$, $v'$ and undo data $\mathit{undo}$ (a list of lists of coins) such that
$$\mathrm{connectBlock}(\langle \mathcal H, u\rangle, b) = \text{some } (u', \mathit{undo}),\quad \mathrm{connectBlock}(\langle \mathcal H, v\rangle, b) = \text{some } (v', \mathit{undo}),\quad u' \sim v'.$$
In alternative 2 the undo data is literally the *same* list on both sides (so, since each undo entry is the list of coins read by first-match lookup at the inputs' outpoints — or the dummy coin $\langle\langle -1, [\,]\rangle, 0, \mathrm{false}\rangle$ where absent — those lookups agree), and the resulting ledgers are only asserted equivalent, not equal.

**Edge cases the statement includes.** If $\mathrm{headerHash}(b.\mathrm{header}) = \mathrm{genesisHash}$, $\mathrm{connectBlock}$ returns "some $(u, [\,])$" and "some $(v, [\,])$" respectively, and alternative 2 holds with $u' = u$, $v' = v$. If $b.\mathrm{vtx}$ is empty, the loop does nothing and the coinbase bound is checked against the fixed genesis coinbase's output value $5\cdot 10^9$ versus $0 + \text{subsidy}(|\mathcal H|)$. The height used throughout is $|\mathcal H|$ and the BIP30 ancestor test consults $\mathcal H$ at index $227931$; the median-time-past function used by the sequence-lock check is derived from $\mathcal H$ alone. The statement does not say *which* alternative holds for a given input, only that one does.
