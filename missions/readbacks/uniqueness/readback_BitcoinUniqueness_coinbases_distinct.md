# Read-back: `BitcoinUniqueness.coinbases_distinct`

**Statement.** For all chain states $S_1, S_2$, blocks $b_1, b_2$, integers $t_1, t_2$ (clock readings), chain states $S_1', S_2'$, and undo lists $U_1, U_2$, if
- $\mathrm{Reachable}(S_1)$ and $\mathrm{Reachable}(S_2)$,
- $\mathrm{validate}(S_1, b_1, t_1) = \mathrm{accept}(S_1', U_1)$ and $\mathrm{validate}(S_2, b_2, t_2) = \mathrm{accept}(S_2', U_2)$,
- $227{,}931 \le |S_1.\mathrm{headers}|$ and $227{,}931 \le |S_2.\mathrm{headers}|$,
- $|S_1.\mathrm{headers}| < 2^{31}$ and $|S_2.\mathrm{headers}| < 2^{31}$, and
- $|S_1.\mathrm{headers}| \ne |S_2.\mathrm{headers}|$,

then $\mathrm{coinbaseScriptSig}(b_1) \ne \mathrm{coinbaseScriptSig}(b_2)$ (the two byte strings are not equal).

Formally, with $H_i := |S_i.\mathrm{headers}|$:
$$\forall S_1 S_2\, b_1 b_2\, t_1 t_2\, S_1' S_2'\, U_1 U_2,\ \ \bigwedge_{i=1,2}\Big(\mathrm{Reachable}(S_i) \wedge \mathrm{validate}(S_i,b_i,t_i)=\mathrm{accept}(S_i',U_i) \wedge 227931 \le H_i < 2^{31}\Big) \wedge H_1 \ne H_2 \Longrightarrow \mathrm{coinbaseScriptSig}(b_1) \ne \mathrm{coinbaseScriptSig}(b_2).$$

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

- The two chain states are related by **no** hypothesis: they need not share any header, need not be on the same chain, and need not be each other's ancestor; the only link between the two halves is $H_1 \ne H_2$.
- The two clock readings $t_1, t_2$ are independent and arbitrary.
- The conclusion compares only the first-input scriptSig of the first transaction of each block (with the fallbacks of $\mathrm{coinbaseScriptSig}$, which the validation hypotheses' stage 2 prevents from being exercised). It says nothing about txids, about the rest of the coinbase transaction, or about blocks at the **same** height on different chains ($H_1 = H_2$ is excluded by hypothesis, so nothing is claimed about it).
- The heights are lengths of header lists of the pre-block states, bounded below by $227{,}931$ and strictly above by $2^{31}$.
- $S_1', S_2', U_1, U_2$ appear only in the acceptance hypotheses.
