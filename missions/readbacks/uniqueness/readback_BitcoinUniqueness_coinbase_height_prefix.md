# Read-back: `BitcoinUniqueness.coinbase_height_prefix`

**Statement.** For every chain state $S$, block $b$, integer $t$ (clock reading), chain state $S'$, and undo list $U$, if
- $\mathrm{Reachable}(S)$,
- $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', U)$, and
- $227{,}931 \le |S.\mathrm{headers}|$ (the constant $\mathrm{BIP34Height}$ is at most the next height of $S$),

then the byte string $\mathrm{heightScript}(|S.\mathrm{headers}|)$ is a prefix (initial segment, possibly the whole string) of the byte string $\mathrm{coinbaseScriptSig}(b)$.

Formally, with $H := |S.\mathrm{headers}|$:
$$\forall S\, b\, t\, S'\, U,\quad \mathrm{Reachable}(S) \wedge \mathrm{validate}(S,b,t) = \mathrm{accept}(S',U) \wedge 227931 \le H \ \Longrightarrow\ \mathrm{heightScript}(H) \sqsubseteq \mathrm{coinbaseScriptSig}(b),$$
where $x \sqsubseteq y$ means $y = x \mathbin{+\!\!+} z$ for some byte string $z$.

### What coinbaseScriptSig says

$\mathrm{coinbaseScriptSig}(b)$ is the scriptSig (a byte string) of the first input of the first transaction of $b.\mathrm{vtx}$, with two fallbacks: if $b.\mathrm{vtx}$ is empty, the fixed genesis coinbase transaction stands in for the first transaction (its scriptSig is a fixed 77-byte string); if that transaction has no inputs, a default input with empty scriptSig stands in, giving the empty string.
### What heightScript says

For a natural number $n$, $\mathrm{heightScript}(n)$ is the byte string
$$\mathrm{heightScript}(n) = \begin{cases} [\mathtt{0x00}] & n = 0,\\ [\mathtt{0x50} + n] & 1 \le n \le 16 \ (\text{a single byte in } \mathtt{0x51}..\mathtt{0x60}),\\ \mathrm{pushBytes}(\mathrm{serialize}(n)) & n \ge 17,\end{cases}$$
where, for $n \ge 17$ (so $n$ is positive and $\mathrm{serialize}$ takes its non-negative branch): $\mathrm{serialize}(n)$ is the little-endian base-256 digit string of $n$ with no trailing zero byte (the "magnitude"), followed by an extra byte $\mathtt{0x00}$ if and only if the top bit ($\mathtt{0x80}$) of the magnitude's last byte is set; and $\mathrm{pushBytes}(d)$, for a byte string $d$, is $[\,|d|\,] \mathbin{+\!\!+} d$ (one length byte then the data) when $|d| < 76$, is $[\mathtt{0x4c}, |d|] \mathbin{+\!\!+} d$ when $76 \le |d| \le 255$, is $[\mathtt{0x4d}] \mathbin{+\!\!+} (\text{2 little-endian bytes of } |d|) \mathbin{+\!\!+} d$ when $256 \le |d| \le 65535$, and is $[\mathtt{0x4e}] \mathbin{+\!\!+} (\text{4 little-endian bytes of } |d| \bmod 2^{32}) \mathbin{+\!\!+} d$ otherwise. For $17 \le n < 2^{31}$ the magnitude has between 1 and 4 bytes, so $\mathrm{serialize}(n)$ has between 1 and 5 bytes and $\mathrm{heightScript}(n)$ is one length byte (value 1 to 5) followed by those bytes.
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

- The height in the conclusion is $|S.\mathrm{headers}|$, the length of the header list of the state *before* $b$ is connected; it is not read from $b$ and is not $|S'.\mathrm{headers}|$ (which is one larger).
- Under $227{,}931 \le H$ the header list is non-empty, so $\mathrm{tipHeight} + 1 = H$ and the conditional BIP34 clause of validation stage 3 is in force; that clause compares $\mathrm{heightScript}(H)$ against the very same byte-string expression that defines $\mathrm{coinbaseScriptSig}(b)$. The read-back records this as the structure of the definitions.
- Stage 2 of validation requires $b.\mathrm{vtx}$ to be non-empty with a coinbase first transaction (exactly one input), so under the hypotheses neither fallback of $\mathrm{coinbaseScriptSig}$ (genesis coinbase, default input) is exercised; the conclusion itself does not say so.
- No upper bound on $H$ is assumed here (unlike the sibling statements); $\mathrm{heightScript}$ is defined for every natural number.
- $S'$, $U$ and $t$ appear only in the acceptance hypothesis.
- The statement asserts a prefix relation only: the coinbase scriptSig may contain arbitrary further bytes after the height push, and nothing is claimed about its length beyond what stage 2 requires (between 2 and 100 bytes).
