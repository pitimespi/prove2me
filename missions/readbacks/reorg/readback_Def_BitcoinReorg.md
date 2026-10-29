# Read-back: `Def_BitcoinReorg.lean`

This file introduces six declarations in the namespace `BitcoinReorg`, building on the block-validation definitions it imports. The imported notions are expanded first so that each declaration's paragraph can be read on its own.

## Imported notions, expanded

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

**Reachability.** $\mathrm{Reachable}(S)$ is the least predicate such that the initial state $\langle [\text{genesisHeader}], [\,]\rangle$ is reachable, and whenever $\mathrm{Reachable}(S)$ and there exist a block $b$, an integer $t$, a state $S'$ and undo data $\mathit{undo}$ with $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$, then $\mathrm{Reachable}(S')$. The clock reading $t$ is unconstrained in each step and may differ from step to step.

**The block disconnection $\mathrm{disconnectBlock}(u, H, \eta, b, \mathit{undo})$**, for a ledger $u$, a natural number $H$, a byte string $\eta$, a block $b$ and undo data $\mathit{undo}$ (a list of lists of coins), returns "none" or "some $(u', \mathit{clean})$" with $\mathit{clean}$ a Boolean:

- If $|\mathit{undo}| + 1 \neq |b.\mathrm{vtx}|$, the result is "none".
- Otherwise let $e$ (the *exception* flag) hold exactly when $(H, \eta)$ is $(91722, \text{a fixed hash})$ or $(91812, \text{a fixed hash})$. Pair the transactions of $b$ with undo entries so that the first transaction gets "no undo" and the $j$-th transaction ($j \ge 1$) gets the $(j-1)$-th entry of $\mathit{undo}$, and process these pairs in *reverse* block order (last transaction first), threading the ledger and conjoining the flags. For one pair $(tx, \mathit{undo}_{tx})$ on ledger $w$, with $cb$ = "$tx$ is a coinbase":
  - *Outputs.* For each output $o_j$ of $tx$ at index $j$ in order: if $o_j$'s script is unspendable, nothing happens and the flag for this output is true; otherwise let $p = (\mathrm{txid}(tx), j)$, let $ok$ hold when $\mathrm{getCoin}(w, p)$ is some coin $c$ with $c.\mathrm{out} = o_j$, $c.\mathrm{height} = H$ and $c.\mathrm{isCoinbase} = cb$, replace $w$ by $\mathrm{spendCoin}(w, p)$, and the flag for this output is $ok \vee (cb \wedge e)$. The output phase's flag is the conjunction over outputs.
  - *Inputs.* If $\mathit{undo}_{tx}$ is "no undo", the pair yields $(w, \text{output flag})$. Otherwise, with $\mathit{undo}_{tx}$ a list of coins $c_1, \dots, c_m$: if $m \neq |tx.\mathrm{vin}|$ the whole result is "none"; else the inputs are restored *last input first*: for the input $i$ paired with coin $c$ and outpoint $q = i.\mathrm{prevout}$, let the per-input flag be "$\mathrm{getCoin}(w, q)$ is none"; if $c.\mathrm{height} = 0$ then look for the *first* entry of $w$ whose outpoint hash equals $q.\mathrm{hash}$ — if there is none the whole result is "none", and if there is one with coin $c^\ast$ then replace $c$ by $c$ with height and coinbase flag copied from $c^\ast$; then replace $w$ by $\mathrm{addCoin}(w, q, c)$ (so a coin with an unspendable script is not re-added). The input phase's flag is the conjunction of the per-input flags, and the pair's flag is the output flag and the input flag.
- The result is "some (final ledger, conjunction of all pairs' flags)".


## Declaration 1: `StateEquiv`

For chain states $S$ and $T$, $\mathrm{StateEquiv}(S, T)$ — written $S \approx T$ below — is the proposition
$$S.\mathrm{headers} = T.\mathrm{headers} \;\wedge\; \forall p,\ \mathrm{getCoin}(S.\mathrm{utxo}, p) = \mathrm{getCoin}(T.\mathrm{utxo}, p).$$
The first conjunct is literal equality of the two header lists (same length, same headers at every position). The second is ledger equivalence $S.\mathrm{utxo} \sim T.\mathrm{utxo}$: the first-match lookup agrees at every outpoint, with the quantifier ranging over all byte strings and all natural numbers. Two ledgers that differ only in the order of entries, in shadowed duplicate entries, or in the number of copies of an entry are equivalent; two ledgers of different lengths can be equivalent; and a ledger with entries whose scripts are unspendable is not excluded.

## Declaration 2: `connectChain`

$\mathrm{connectChain}$ takes a chain state $S$ and a list $bs$ of pairs $(b, t)$ of a block and an integer clock reading, and returns "none" or "some $(T, \mathit{undos})$" where $T$ is a chain state and $\mathit{undos}$ is a list of undo data (each undo datum being a list of lists of coins). It is defined by recursion on $bs$:

- $\mathrm{connectChain}(S, [\,]) = \text{some } (S, [\,])$;
- $\mathrm{connectChain}(S, (b, t) :: \mathit{rest})$: evaluate $\mathrm{validate}(S, b, t)$. If it is $\mathrm{accept}(S', \mathit{undo})$, then evaluate $\mathrm{connectChain}(S', \mathit{rest})$: if that is "none" the result is "none", and if it is "some $(T, \mathit{undos})$" the result is "some $(T, \mathit{undo} :: \mathit{undos})$". If $\mathrm{validate}(S, b, t)$ is $\mathrm{invalid}$, $\mathrm{futureTime}$ or $\mathrm{missingPrev}$, the result is "none".

Each block is validated against the state produced by its predecessors with its own clock reading $t$; the clock readings are independent integers with no monotonicity relation among them. On success the returned list has exactly one entry per block, in order. For the empty list the state is returned unchanged with an empty undo list, with no condition on $S$.

## Declaration 3: `disconnectTip`

$\mathrm{disconnectTip}(S, b, \mathit{undo})$, for a chain state $S$, a block $b$ and undo data $\mathit{undo}$, returns "none" or "some $(S', \mathit{clean})$" with $\mathit{clean}$ a Boolean. It evaluates
$$\mathrm{disconnectBlock}\big(S.\mathrm{utxo},\ \mathrm{tipHeight}(S),\ \mathrm{headerHash}(b.\mathrm{header}),\ b,\ \mathit{undo}\big),$$
where $\mathrm{tipHeight}(S) = |S.\mathrm{headers}| - 1$ with truncated subtraction (so $0$ for both one and zero headers). If that is "none" the result is "none"; if it is "some $(u, \mathit{clean})$" the result is "some $(\langle \mathrm{dropLast}(S.\mathrm{headers}),\ u\rangle,\ \mathit{clean})$ (where $\mathrm{dropLast}$ removes the last element of a list, and is the identity on the empty list)". The hash passed to $\mathrm{disconnectBlock}$ is the hash of the *given* block's header, and the header removed is whatever is last in $S.\mathrm{headers}$; nothing checks that these coincide. Removing the last element of an empty list yields the empty list, so $\mathrm{disconnectTip}$ on a state with no headers can still succeed. The Boolean returned is the flag of $\mathrm{disconnectBlock}$ (the conjunction of all per-output and per-input flags described above); the docstring names it "`DISCONNECT_OK` versus `DISCONNECT_UNCLEAN`".

## Declaration 4: `disconnectChain`

$\mathrm{disconnectChain}$ takes a chain state $S$ and a list of pairs $(b, \mathit{undo})$ of a block and undo data, and returns "none" or "some $(T, c)$" with $c$ a Boolean, by recursion on the list:

- $\mathrm{disconnectChain}(S, [\,]) = \text{some } (S, \mathrm{true})$;
- $\mathrm{disconnectChain}(S, (b, \mathit{undo}) :: \mathit{rest})$: if $\mathrm{disconnectTip}(S, b, \mathit{undo})$ is "none" the result is "none"; if it is "some $(S', \mathit{clean})$", then if $\mathrm{disconnectChain}(S', \mathit{rest})$ is "none" the result is "none", and if it is "some $(T, c)$" the result is "some $(T, \mathit{clean} \wedge c)$".

The pairs are consumed from the front, so the first pair of the list is disconnected first (the docstring: "the tip block first"), and each later pair is disconnected from the state the previous step produced; the final Boolean is the conjunction of every step's flag, and is $\mathrm{true}$ for the empty list.

## Declaration 5: `FreshChain`

$\mathrm{FreshChain}(S, bs)$ is a proposition on a chain state $S$ and a list $bs$ of block–clock pairs, defined by recursion on $bs$:

- $\mathrm{FreshChain}(S, [\,])$ is *true* (no condition on $S$);
- $\mathrm{FreshChain}(S, (b, t) :: \mathit{rest})$ is the conjunction of
  1. $[\mathrm{txid}(tx) : tx \in b.\mathrm{vtx}]$ has no duplicate entries (so no two transactions of $b$, including the coinbase, have the same txid);
  2. $\forall tx \in b.\mathrm{vtx},\ \forall o \in \mathbb{N},\ \mathrm{getCoin}(S.\mathrm{utxo}, (\mathrm{txid}(tx), o)) = \text{none}$ — the ledger of $S$ has no coin at *any* outpoint whose hash is a txid of $b$, the index $o$ ranging over all natural numbers, not only the indices of actual outputs;
  3. $\mathrm{headerHash}(b.\mathrm{header}) \neq \mathrm{genesisHash}$;
  4. $\forall S', \forall \mathit{undo},\ \mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo}) \rightarrow \mathrm{FreshChain}(S', \mathit{rest})$.

Conjunct 4 is vacuously satisfied whenever $\mathrm{validate}(S, b, t)$ is not an acceptance, so $\mathrm{FreshChain}(S, bs)$ does not by itself imply that any block of $bs$ is accepted; conjuncts 1–3 are only ever imposed on the blocks up to and including the first one that is not accepted. The docstring says that conjunct 2 is the BIP30 condition, "which `ConnectBlock` enforces only where its scan runs" — the scan inside $\mathrm{connectBlock}$ is conditional on the height and hash and tests only indices below the output count, whereas conjunct 2 is unconditional and over all indices.

## Declaration 6: `Consistent`

$\mathrm{Consistent}(S)$ is the proposition
$$\exists S_0,\ \mathrm{Reachable}(S_0) \wedge S \approx S_0,$$
i.e. there is some state reachable from the initial state by a sequence of accepted blocks (each with an arbitrary clock reading) whose header list equals that of $S$ and whose ledger is equivalent to that of $S$. In particular every reachable state is consistent (take $S_0 = S$), and consistency does not constrain the order, duplication or shadowing of entries in $S.\mathrm{utxo}$.
