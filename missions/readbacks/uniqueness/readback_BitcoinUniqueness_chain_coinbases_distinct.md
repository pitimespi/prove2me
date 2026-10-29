# Read-back: `BitcoinUniqueness.chain_coinbases_distinct`

**Statement.** For every chain state $S$, every finite list $\mathit{bs} = [(b_1, t_1), (b_2, t_2), \dots, (b_n, t_n)]$ of pairs (block, integer clock reading), every chain state $T$, and every list $\mathit{undos}$ of undo lists, if
- $\mathrm{Reachable}(S)$,
- $227{,}931 \le |S.\mathrm{headers}|$,
- $\mathrm{connectChain}(S, \mathit{bs}) = \mathrm{some}(T, \mathit{undos})$, and
- $|S.\mathrm{headers}| + n < 2^{31}$,

then the list $\big[\mathrm{coinbaseScriptSig}(b_1),\ \mathrm{coinbaseScriptSig}(b_2),\ \dots,\ \mathrm{coinbaseScriptSig}(b_n)\big]$ has no duplicates: for all positions $i \ne j$, $\mathrm{coinbaseScriptSig}(b_i) \ne \mathrm{coinbaseScriptSig}(b_j)$.

Formally, with $H := |S.\mathrm{headers}|$ and $n := |\mathit{bs}|$:
$$\forall S\, \mathit{bs}\, T\, \mathit{undos},\quad \mathrm{Reachable}(S) \wedge 227931 \le H \wedge \mathrm{connectChain}(S,\mathit{bs}) = \mathrm{some}(T,\mathit{undos}) \wedge H + n < 2^{31} \Longrightarrow \mathrm{Nodup}\big(\mathrm{map}\ (\mathrm{coinbaseScriptSig} \circ \pi_1)\ \mathit{bs}\big).$$

### What connectChain says

$\mathrm{connectChain}(S, \mathit{bs})$ is defined by recursion on the list: $\mathrm{connectChain}(S, [\,]) = \mathrm{some}(S, [\,])$; and $\mathrm{connectChain}(S, (b,t) :: \mathit{rest})$ is $\mathrm{some}(T, U :: \mathit{us})$ if $\mathrm{validate}(S, b, t) = \mathrm{accept}(S_1, U)$ and $\mathrm{connectChain}(S_1, \mathit{rest}) = \mathrm{some}(T, \mathit{us})$, and $\mathrm{none}$ if either $\mathrm{validate}(S,b,t)$ is not an acceptance or the recursive call is $\mathrm{none}$. So the hypothesis $\mathrm{connectChain}(S,\mathit{bs}) = \mathrm{some}(T,\mathit{undos})$ says: there are states $S = S_0, S_1, \dots, S_n = T$ and undo lists $U_1, \dots, U_n$ with $\mathrm{validate}(S_{i-1}, b_i, t_i) = \mathrm{accept}(S_i, U_i)$ for each $i = 1..n$ and $\mathit{undos} = [U_1, \dots, U_n]$. Each block is validated with its own clock reading $t_i$. Since each acceptance appends one header, $|S_i.\mathrm{headers}| = H + i$.

### What coinbaseScriptSig says

$\mathrm{coinbaseScriptSig}(b)$ is the scriptSig (a byte string) of the first input of the first transaction of $b.\mathrm{vtx}$, with two fallbacks: if $b.\mathrm{vtx}$ is empty, the fixed genesis coinbase transaction stands in for the first transaction (its scriptSig is a fixed 77-byte string); if that transaction has no inputs, a default input with empty scriptSig stands in, giving the empty string.
### What the acceptance hypothesis says

$\mathrm{validate}(S, b, t) = \mathrm{accept}(S', U)$ asserts that the four stages below all succeed and that $S'$ and $U$ are exactly the state and undo list they produce. Write $h := b.\mathrm{header}$, $H := |S.\mathrm{headers}|$ (the next height), $\mathrm{tip}$ for the last element of $S.\mathrm{headers}$ (the fixed genesis header if the list is empty), $\mathrm{tipHeight} := H \mathbin{\dot{-}} 1$ (truncated subtraction, so $0$ when $H = 0$), and $\mathrm{cb}$ for the first transaction of $b.\mathrm{vtx}$ (the fixed genesis coinbase transaction if $b.\mathrm{vtx}$ is empty). A transaction "is a coinbase" iff it has exactly one input and that input's previous outpoint is $(32\text{ zero bytes}, \mathtt{0xffffffff})$.

1. **Header stage.** $h$ passes the proof-of-work test of the imported proof-of-work development (its double-SHA-256 hash, read as a little-endian 256-bit number, against the 32-bit field $h.\mathrm{bits}$); $h.\mathrm{prevBlock}$ equals the header hash of $\mathrm{tip}$ (otherwise the outcome is "missing previous", not accept); the 32-bit value of $h.\mathrm{bits}$ equals the required work computed from $S$ by the imported difficulty rule; the median time past of $S$ at $\mathrm{tipHeight}$ is strictly less than $h.\mathrm{time}$; $h.\mathrm{time} \le t + 7200$ (otherwise the outcome is "future time", not accept); and it is not the case that ($h.\mathrm{version} < 2$ and $227931 \le \mathrm{tipHeight}+1$), nor ($h.\mathrm{version} < 3$ and $363725 \le \mathrm{tipHeight}+1$), nor ($h.\mathrm{version} < 4$ and $388381 \le \mathrm{tipHeight}+1$).

2. **Context-free block stage.** The proof-of-work test again; the Merkle root computed from the txids of $b.\mathrm{vtx}$ equals $h.\mathrm{merkleRoot}$ and the Merkle computation reports no mutation; $b.\mathrm{vtx}$ is non-empty; $4\cdot|b.\mathrm{vtx}| \le 4{,}000{,}000$ and $4\cdot(\text{length of the witness-stripped serialization of } b) \le 4{,}000{,}000$; $\mathrm{cb}$ is a coinbase and no other transaction of $b$ is; every transaction has non-empty inputs and outputs, witness-stripped size times 4 at most $4{,}000{,}000$, every output value in $[0, 2.1\times 10^{15}]$ with running totals in that range, pairwise distinct previous outpoints, and (for a coinbase) a first-input scriptSig of length between $2$ and $100$ inclusive, or (for a non-coinbase) no null previous outpoint; and $4\cdot\sum$ of the legacy signature-operation counts is at most $80{,}000$.

3. **Contextual stage.** Every transaction of $b$ is final at height $H$ against a cutoff (the median time past of $S$ if $419328 \le \mathrm{tipHeight}+1$, else $h.\mathrm{time}$); **if** $227931 \le \mathrm{tipHeight}+1$ **then** $\mathrm{heightScript}(H)$ is a prefix of the scriptSig of the first input of $\mathrm{cb}$ (the first input being the default input with empty scriptSig if $\mathrm{cb}$ has no inputs) — this byte string is literally the same expression as $\mathrm{coinbaseScriptSig}(b)$; the witness-malleation check passes with the expectation flag set iff $481824 \le \mathrm{tipHeight}+1$; and the block weight ($3\times$ stripped size $+$ full size) is at most $4{,}000{,}000$.

4. **Connect stage.** Let $\eta := \mathrm{headerHash}(h)$. If $\eta$ equals the fixed genesis block hash $G$ (32 bytes beginning $\mathtt{6f\,e2\,8c\,0a}$), the stage succeeds immediately with ledger $S.\mathrm{utxo}$ and empty undo list, performing no further check. Otherwise: if $\mathrm{bip30Checked}(S,H,\eta) = \mathtt{true}$ (see the ScanRuns unfolding) **and** it is not the case that for every $\mathrm{tx} \in b.\mathrm{vtx}$ and every $o < |\mathrm{tx}.\mathrm{vout}|$ the ledger $S.\mathrm{utxo}$ has no entry keyed $(\mathrm{txid}(\mathrm{tx}), o)$, the stage fails; otherwise the transactions are processed in order through the imported per-transaction loop (input lookup and maturity, fee range, sequence locks, sigop budget, full script verification, ledger update), which must succeed, and finally the output value of $\mathrm{cb}$ must be at most the accumulated fees plus the subsidy at height $H$.

On success, $S' = \big(S.\mathrm{headers} \mathbin{+\!\!+} [h],\ u\big)$ where $u$ is the ledger produced by stage 4, and $U$ is the undo list produced by stage 4. In particular $|S'.\mathrm{headers}| = H + 1$.

### What reachability says

$\mathrm{Reachable}(S)$ is the least predicate such that (i) the initial state $\big([\text{genesis header}],\ [\,]\big)$ (one header, empty ledger) is reachable, and (ii) whenever $S_0$ is reachable and $\mathrm{validate}(S_0, b_0, t_0) = \mathrm{accept}(S_1, U_0)$ for some block $b_0$, integer $t_0$ and undo list $U_0$, then $S_1$ is reachable. So $\mathrm{Reachable}(S)$ means $S$ arises from the initial state by a finite sequence of accepted validations, each with its own arbitrary clock reading.

### Edge cases and scope

- $n = 0$: $\mathit{bs}$ empty, $T = S$, $\mathit{undos} = [\,]$, and the conclusion ($\mathrm{Nodup}$ of the empty list) holds trivially.
- $n = 1$: the conclusion ($\mathrm{Nodup}$ of a one-element list) holds trivially.
- The conclusion concerns only the blocks in $\mathit{bs}$; it says nothing about the coinbase scriptSigs of blocks already in $S$ (those at heights below $H$), nor about any comparison between a block of $\mathit{bs}$ and a block of $S$.
- $\mathrm{Nodup}$ is pairwise inequality of the byte strings at distinct positions; it does not say anything about txids or about the coinbase transactions as a whole.
- $T$ and $\mathit{undos}$ appear only in the connection hypothesis; the clock readings $t_i$ are arbitrary and independent.
- The bound $H + n < 2^{31}$ constrains the height of every block in the sequence to be below $2^{31}$; the lower bound $227{,}931 \le H$ applies to the first block's height, and hence (by the header-append structure) to all of them.
- The fallbacks of $\mathrm{coinbaseScriptSig}$ (empty transaction list, inputless first transaction) are not exercised under the stage-2 requirements of each acceptance; the conclusion itself does not say so.
