# Read-back: `BitcoinSupply.block_supply`

## Statement

For every chain state $S$, every block $b$ (a header and a list of transactions), every integer $t$ ("now"), every chain state $S'$ and every undo datum $\mathit{undo}$ (a list of lists of coins), if

1. $\mathrm{Reachable}(S)$ holds (expanded below), and
2. $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$ (the validation procedure expanded below accepts $b$ on top of $S$ with clock $t$, producing exactly the state $S'$ and undo data $\mathit{undo}$),

then
$$\mathrm{totalValue}(S'.\mathrm{utxo}) \;\le\; \mathrm{totalValue}(S.\mathrm{utxo}) + \mathrm{coreSubsidy}(S.\mathrm{nextHeight}),$$
where $\mathrm{totalValue}(L) = \sum_{(k,c) \in L} c.\mathrm{out}.\mathrm{nValue}$ counts every list entry, $S.\mathrm{nextHeight}$ is the number of headers in $S$ (the height at which $b$ is connected), and $\mathrm{coreSubsidy}$ is the subsidy mission's function defined below, cast to an integer. The inequality is non-strict and compares integers.

The conclusion is stated with $\mathrm{coreSubsidy}$ directly, not with the file's $\mathrm{issued}$ or $\mathrm{genesisSubsidy}$ constants, and it bounds the total **after** the block in terms of the total **before** it plus the subsidy at the connecting height; the fees of the block do not appear in the conclusion.

## Chain states and what "reachable" means

A **chain state** $S$ is a pair: a list of block headers $S.\mathrm{headers}$ and a ledger $S.\mathrm{utxo}$. A **ledger** is a finite list of pairs $(k, c)$ with $k$ an *outpoint* (a byte list $k.\mathrm{hash}$ and a natural number $k.n$) and $c$ a *coin* $(c.\mathrm{out}, c.\mathrm{height}, c.\mathrm{isCoinbase})$, whose output $c.\mathrm{out}$ carries an integer value $c.\mathrm{out}.\mathrm{nValue}$ and a byte-list script. Nothing in the type forbids repeated keys in a ledger. $S.\mathrm{nextHeight}$ is the **length** of $S.\mathrm{headers}$; $S.\mathrm{tipHeight}$ is that length minus one (natural-number subtraction, so $0$ for an empty list); the *tip* is the last header (the fixed genesis header if the list is empty).

Other notation used below:

- $\mathrm{getCoin}(L, p)$: the coin of the first entry of ledger $L$ with key $p$, if any; $\mathrm{haveCoin}(L,p)$ is true iff one exists; $\mathrm{accessCoin}(L,p)$ is that coin, or a dummy coin of value $-1$ when absent.
- $\mathrm{isCoinBase}(tx)$: $tx$ has exactly one input and its outpoint is null (hash $=$ 32 zero bytes, index $= 2^{32}-1$).
- $\mathrm{valueOut}(tx) = \sum_{o \in tx.\mathrm{vout}} o.\mathrm{nValue}$ (integer sum).
- $\mathrm{txid}(tx)$: double SHA-256 of the witness-stripped serialization of $tx$. A script is *unspendable* iff it is non-empty with first byte $0x6a$, or longer than $10{,}000$ bytes.
- $\mathrm{updateCoins}(L, tx, h)$: if $tx$ is not a coinbase, first delete from $L$, for each input in order, every entry whose key equals that input's outpoint; then for each output $o_j$ of $tx$ (index $j = 0, 1, \dots$): if its script is unspendable, nothing; otherwise delete every entry with key $(\mathrm{txid}(tx), j)$ and prepend $\big((\mathrm{txid}(tx), j), (o_j, h, \mathrm{isCoinBase}(tx))\big)$.
- $\mathrm{MAX\_MONEY} = 2{,}100{,}000{,}000{,}000{,}000$ (integer). "$v$ is in money range" means $0 \le v \le \mathrm{MAX\_MONEY}$.
- $\mathrm{coreSubsidy}(h)$ for $h \in \mathbb{N}$, with $q = \lfloor h/210{,}000 \rfloor$: $0$ if $q \ge 64$, else $\lfloor 5{,}000{,}000{,}000 / 2^{q} \rfloor$ (already $0$ once $q \ge 33$).

$\mathrm{Reachable}$ is the least predicate on chain states such that

1. the **initial state** $S_0 = ([\mathrm{genesisHeader}],\ [\,])$ is reachable: its header list holds the single fixed mainnet genesis header and its ledger is **empty** (the genesis coinbase output is not in it);
2. if $S$ is reachable and there **exist** a block $b$ (a header plus a list of transactions $b.\mathrm{vtx}$), an integer $t$ (the "local clock", **unconstrained** — any integer may be chosen for each step), a state $S'$ and undo data $\mathit{undo}$ with $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$, then $S'$ is reachable.

$\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$ holds exactly when steps (a)–(d) below all succeed; then $S' = (S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}],\ u)$ with $u$ the ledger produced in step (d), so $S'.\mathrm{nextHeight} = S.\mathrm{nextHeight} + 1$.

**(a) Header acceptance.** The header's compact target $\mathrm{bits}$ decodes to a valid target $T$ and the header's double-SHA-256 hash, read as a little-endian number, is $\le T$; $b.\mathrm{header}.\mathrm{prevBlock}$ equals the hash of the tip of $S$; $\mathrm{bits}$ equals the difficulty $S$ requires (the PoW mission's next-work rule applied to the tip and the first header of its 2016-block period); $b.\mathrm{header}.\mathrm{time} > \mathrm{mtp}(S)$, the median-time-past of the tip computed from the header times of $S$; $b.\mathrm{header}.\mathrm{time} \le t + 7{,}200$; and the version is not outdated (not version $< 2$ once height $227{,}931$ is active after the tip height, nor $< 3$ for $363{,}725$, nor $< 4$ for $388{,}381$).

**(b) Context-free block check.** The same proof-of-work test; $b.\mathrm{vtx}$ is non-empty; the Merkle root over the txids equals the header's Merkle root and is not flagged mutated; $4 \cdot |b.\mathrm{vtx}| \le 4{,}000{,}000$ and $4 \cdot$ (witness-stripped serialized size of $b$) $\le 4{,}000{,}000$; the **first** transaction is a coinbase and **every later** transaction is not; every transaction $tx$ passes the transaction check: non-empty inputs and non-empty outputs; $4 \cdot$ (its witness-stripped size) $\le 4{,}000{,}000$; every output value lies in $[0, \mathrm{MAX\_MONEY}]$ and every prefix sum of the output values is in money range (hence $\mathrm{valueOut}(tx) \in [0, \mathrm{MAX\_MONEY}]$); the inputs' outpoints are pairwise distinct; a coinbase's first input scriptSig has length in $[2, 100]$, and a non-coinbase has no null input outpoint; finally $4 \cdot$ (the block's legacy sigop count) $\le 80{,}000$.

**(c) Contextual block check.** With $h = S.\mathrm{nextHeight}$: every transaction is final at height $h$ against a cutoff time (the tip's median time past if CSV is active after the tip height, else the header's time); if the BIP34 height-in-coinbase rule is active, the first transaction's first input scriptSig begins with the push of $h$; the witness-commitment/malleation test for the segwit activation status passes; the block weight is $\le 4{,}000{,}000$.

**(d) Connect.** Let $h = S.\mathrm{nextHeight}$ and let $H$ be the hash of $b.\mathrm{header}$.

- If $H$ equals the fixed mainnet **genesis hash**, the result is $(S.\mathrm{utxo}, [\,])$: the ledger is **unchanged** and the transactions of $b$ are not applied, although the header is still appended.
- Otherwise, if the BIP30 scan applies to $(S, h, H)$ (it applies unless $b$ is one of the two listed repeat blocks or the BIP34 activation header is present in $S$ with the expected hash, and always applies from height $1{,}983{,}702$), then for every transaction $tx$ of $b$ and every index $j < |tx.\mathrm{vout}|$, no entry of $S.\mathrm{utxo}$ has key $(\mathrm{txid}(tx), j)$. Then the transactions of $b$ are processed **in order** by a loop whose state is (ledger $L$, fees $F$, sigop cost, undo list), starting from $(S.\mathrm{utxo}, 0, 0, [\,])$:
  - if $tx$ is a coinbase, $F$ and the undo list are unchanged;
  - otherwise, on the current ledger $L$: every input outpoint must have an entry in $L$; scanning the inputs in order, the coin found for each must not be (flagged coinbase with $h \mathbin{\dot-} c.\mathrm{height} < 100$, natural-number subtraction truncated at $0$), its value must be in money range and the running sum of coin values must be in money range; the total input value $V_{in}$ must satisfy $V_{in} \ge \mathrm{valueOut}(tx)$ with $V_{in} - \mathrm{valueOut}(tx)$ in money range; then $F + (V_{in} - \mathrm{valueOut}(tx))$ must be in money range, the BIP68 sequence-lock rule must hold, the undo list gains the coins spent, and $F$ becomes $F + V_{in} - \mathrm{valueOut}(tx)$;
  - in either case the accumulated sigop cost (including this transaction's) must be $\le 80{,}000$, a non-coinbase must have every input script verify under the block's script flags, and the ledger becomes $\mathrm{updateCoins}(L, tx, h)$.
  
  After the loop, with final fees $F$ and ledger $u$, it is required that
  $$\mathrm{valueOut}(tx_0) \;\le\; F + \mathrm{coreSubsidy}(h),$$
  where $tx_0$ is the first transaction of $b$; the result is then $(u, \text{undo list})$.

## Edge cases the statement includes

- $\mathit{undo}$ appears only in hypothesis 2 (it is whatever the validation produced); the conclusion does not mention it.
- $t$ is any integer; hypothesis 2 fixes it only through the check $b.\mathrm{header}.\mathrm{time} \le t + 7{,}200$.
- If $b$'s header hashes to the genesis hash and the block passes (a)–(c), step (d) returns the unchanged ledger, so $S'.\mathrm{utxo} = S.\mathrm{utxo}$ and the claim reduces to $0 \le \mathrm{coreSubsidy}(S.\mathrm{nextHeight})$.
- For $S.\mathrm{nextHeight} \ge 33 \cdot 210{,}000$ the subsidy term is $0$ and the claim is $\mathrm{totalValue}(S'.\mathrm{utxo}) \le \mathrm{totalValue}(S.\mathrm{utxo})$.
- The theorem does not assert that $S'$ is reachable (though it is, by the step rule) and does not assert anything about individual values of $S'.\mathrm{utxo}$.
- Coinbase outputs with unspendable scripts count toward $\mathrm{valueOut}(tx_0)$ in the coinbase bound of step (d) but are never added to the ledger.
