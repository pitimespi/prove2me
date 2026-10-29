# Read-back: `BitcoinUniqueness.scan_freshness`

**Statement.** For every chain state $S$, block $b$, integer $t$ (the clock reading, named `now`), chain state $S'$, and undo list $U$ (a list of lists of coins), if
- $\mathrm{Reachable}(S)$,
- $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', U)$,
- $\mathrm{ScanRuns}(S, b)$, and
- $\mathrm{headerHash}(b.\mathrm{header}) \ne G$, where $G$ is the fixed 32-byte genesis block hash (beginning $\mathtt{6f\,e2\,8c\,0a}$),

then $\mathrm{FreshOutputs}(S.\mathrm{utxo}, b)$ holds.

Formally:
$$\forall S\, b\, t\, S'\, U,\quad \mathrm{Reachable}(S) \wedge \mathrm{validate}(S,b,t) = \mathrm{accept}(S',U) \wedge \mathrm{ScanRuns}(S,b) \wedge \mathrm{headerHash}(b.\mathrm{header}) \ne G \ \Longrightarrow\ \mathrm{FreshOutputs}(S.\mathrm{utxo}, b).$$

### What the conclusion says

$\mathrm{FreshOutputs}(u, b)$ for a ledger $u$ (association list of outpoint–coin pairs) is
$$\forall\, \mathrm{tx} \in b.\mathrm{vtx},\ \forall\, o \in \mathbb{N},\ o < |\mathrm{tx}.\mathrm{vout}| \Longrightarrow \mathrm{getCoin}\big(u, (\mathrm{txid}(\mathrm{tx}), o)\big) = \mathrm{none},$$
where $\mathrm{txid}(\mathrm{tx})$ is the double-SHA-256 of the witness-stripped serialization of $\mathrm{tx}$ and $\mathrm{getCoin}(u,p)$ returns the coin of the first pair of $u$ whose key equals $p$, or $\mathrm{none}$ if there is none. The ledger in the conclusion is that of $S$ (the state *before* the block), not of $S'$.

### What ScanRuns says

$\mathrm{ScanRuns}(S,b)$ is, by definition, $\mathrm{bip30Checked}(S, H, \eta) = \mathtt{true}$ with $H := |S.\mathrm{headers}|$ and $\eta := \mathrm{headerHash}(b.\mathrm{header})$ (double-SHA-256 of the serialized header), which unfolds to
$$\Big(\neg\,\mathrm{Rep}(H,\eta)\ \wedge\ \neg\,\mathrm{Anc}(S)\Big)\ \vee\ 1{,}983{,}702 \le H,$$
where $\mathrm{Rep}(H,\eta)$ holds iff $(H = 91842 \wedge \eta = C_{91842})$ or $(H = 91880 \wedge \eta = C_{91880})$ for two fixed 32-byte constants, and $\mathrm{Anc}(S)$ holds iff $S.\mathrm{headers}$ has an element at zero-based position $227{,}931$ (i.e. $H \ge 227{,}932$) whose header hash equals a fixed 32-byte constant $C_{34}$. The block $b$ enters only through $\eta$.
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

- The conclusion is vacuous for a block with no transactions or for transactions with no outputs; stage 2 of validation requires $b.\mathrm{vtx}$ non-empty and every transaction to have outputs, so under the hypotheses these do not occur, but the conclusion itself does not say so.
- $S'$, $U$ and $t$ appear only inside the acceptance hypothesis; the conclusion does not mention them.
- The hypothesis $\mathrm{headerHash}(b.\mathrm{header}) \ne G$ excludes exactly the case in which stage 4 of validation takes its genesis shortcut (which performs no ledger check at all).
- Under $\mathrm{ScanRuns}(S,b)$ and the non-genesis hypothesis, stage 4 of validation fails unless the Boolean form of the same quantified condition as the conclusion holds on $S.\mathrm{utxo}$; the read-back records this as the structure of the definitions, not as an assessment.
- The conclusion says nothing about duplicate txids *within* $b$, nor about the ledger $S'.\mathrm{utxo}$ after connection, nor about any outpoint that $b$ does not create.
