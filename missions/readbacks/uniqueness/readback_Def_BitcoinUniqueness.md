# Read-back: `Def_BitcoinUniqueness.lean`

Three definitions, in file order. Throughout, a *byte* is an 8-bit word and a *byte string* is a finite list of bytes. A *transaction* $\mathrm{tx}$ is a record (version, list of inputs $\mathrm{vin}$, list of outputs $\mathrm{vout}$, lock time); an *input* is a record (previous outpoint, byte string $\mathrm{scriptSig}$, sequence number, witness stack); an *outpoint* is a pair (byte string $\mathrm{hash}$, natural number $n$); a *block* $b$ is a record (header, list of transactions $b.\mathrm{vtx}$); a *chain state* $S$ is a record (list of headers $S.\mathrm{headers}$, ledger $S.\mathrm{utxo}$), where a *ledger* is an association list of (outpoint, coin) pairs. The *next height* of $S$ is $S.\mathrm{nextHeight} := |S.\mathrm{headers}|$, the length of its header list.

## `coinbaseScriptSig` (a byte string attached to a block)

For a block $b$, $\mathrm{coinbaseScriptSig}(b)$ is the byte string obtained as follows. Let $\mathrm{tx}_0$ be the first transaction of $b.\mathrm{vtx}$ if that list is non-empty, and otherwise the fixed *genesis coinbase transaction* (version 1, one input with previous outpoint $(32\text{ zero bytes},\ \mathtt{0xffffffff})$, the fixed 77-byte genesis scriptSig beginning $\mathtt{04\,ff\,ff\,00\,1d\,01\,04\,45}$ "The Times 03/Jan/2009 …", sequence $\mathtt{0xffffffff}$, empty witness; one output of value $5{,}000{,}000{,}000$). Let $i_0$ be the first input of $\mathrm{tx}_0.\mathrm{vin}$ if that list is non-empty, and otherwise the default input (previous outpoint $([\,],0)$, empty scriptSig, sequence $0$, empty witness). Then
$$\mathrm{coinbaseScriptSig}(b) := i_0.\mathrm{scriptSig}.$$
Degenerate cases built into the definition: if $b$ has no transactions at all, the value is the genesis coinbase's 77-byte scriptSig (not the empty string); if the first transaction has no inputs, the value is the empty byte string. Nothing in the definition requires $\mathrm{tx}_0$ to be a coinbase transaction, or $b$ to be valid in any sense; the value is defined for every block.

## `ScanRuns` (a proposition about a chain state and a block)

For a chain state $S$ and a block $b$, write $H := |S.\mathrm{headers}|$ and let $\eta := \mathrm{headerHash}(b.\mathrm{header})$, the double-SHA-256 of the 80-byte serialization of $b$'s header (a 32-byte string in internal byte order). Then $\mathrm{ScanRuns}(S,b)$ is the proposition that the Boolean $\mathrm{bip30Checked}(S, H, \eta)$ equals $\mathtt{true}$, which unfolds to
$$\Big(\neg\,\mathrm{Rep}(H,\eta)\ \wedge\ \neg\,\mathrm{Anc}(S)\Big)\ \ \vee\ \ 1{,}983{,}702 \le H,$$
where

- $\mathrm{Rep}(H,\eta)$ (the "BIP30 repeat" test) holds iff $\big(H = 91842 \wedge \eta = C_{91842}\big)$ or $\big(H = 91880 \wedge \eta = C_{91880}\big)$, with $C_{91842}$ and $C_{91880}$ two fixed 32-byte constants (beginning $\mathtt{ec\,ca\,e0\,00}$ and $\mathtt{21\,d7\,7c\,cb}$ respectively);
- $\mathrm{Anc}(S)$ (the "BIP34 ancestor" test) holds iff the list $S.\mathrm{headers}$ has an element at position $227{,}931$ (zero-based; i.e. $H \ge 227{,}932$) and the header hash of that element equals a fixed 32-byte constant $C_{34}$ (beginning $\mathtt{b8\,08\,08\,9c}$). If $H \le 227{,}931$ the position does not exist and $\mathrm{Anc}(S)$ is false.

Observations about the definition as written: the only feature of $b$ it reads is the hash of its header; the height it uses is $|S.\mathrm{headers}|$, not any field of $b$; the second disjunct makes $\mathrm{ScanRuns}(S,b)$ true for every $b$ whenever $|S.\mathrm{headers}| \ge 1{,}983{,}702$, regardless of $\mathrm{Rep}$ and $\mathrm{Anc}$; and no validity or reachability of $S$ is assumed.

## `FreshOutputs` (a proposition about a ledger and a block)

For a ledger $u$ (an association list of outpoint–coin pairs) and a block $b$, $\mathrm{FreshOutputs}(u,b)$ is the proposition
$$\forall\, \mathrm{tx} \in b.\mathrm{vtx},\ \ \forall\, o \in \mathbb{N},\ \ o < |\mathrm{tx}.\mathrm{vout}| \ \Longrightarrow\ \mathrm{getCoin}\big(u, (\mathrm{txid}(\mathrm{tx}), o)\big) = \mathrm{none},$$
where $\mathrm{txid}(\mathrm{tx})$ is the double-SHA-256 of the witness-stripped serialization of $\mathrm{tx}$, and $\mathrm{getCoin}(u, p)$ scans the list $u$ from the front and returns the coin of the first pair whose outpoint equals $p$ (or $\mathrm{none}$ if no pair matches). So the statement says: for every transaction of the block and every output index below that transaction's output count, no entry of $u$ is keyed by that (txid, index) outpoint.

Degenerate cases: if $b.\mathrm{vtx}$ is empty, or if a transaction has no outputs, the corresponding quantification is vacuous. Membership "$\mathrm{tx} \in b.\mathrm{vtx}$" is list membership, so two positions holding the same transaction impose the same condition once. The definition constrains only the relationship between the block and the ledger $u$: it says nothing about two transactions *within* $b$ sharing a txid, nothing about the coinbase, and nothing about outpoints of $u$ that the block does not create. It is also indifferent to whether the outputs are spendable (the ledger-insertion function elsewhere skips unspendable outputs, but this predicate quantifies over all output indices).
