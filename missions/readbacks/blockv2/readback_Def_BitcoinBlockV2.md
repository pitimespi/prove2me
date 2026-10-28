# Read-back: `Def_BitcoinBlockV2.lean`

All declarations live in the namespace `BitcoinBlockV2`. Throughout, a *byte* is an 8-bit word, a *byte string* ("Bytes") is a finite list of bytes, and the imported transaction types are: an *outpoint* is a pair $(\mathit{hash}, n)$ of a byte string and a natural number; an *input* is a quadruple $(\mathit{prevout}, \mathit{scriptSig}, \mathit{nSequence}, \mathit{witness})$ of an outpoint, a byte string, a natural number and a list of byte strings; an *output* is a pair $(\mathit{nValue}, \mathit{scriptPubKey})$ of an integer and a byte string; a *transaction* $tx$ is a quadruple $(\mathit{version}, \mathit{vin}, \mathit{vout}, \mathit{nLockTime})$ of a natural number, a list of inputs, a list of outputs and a natural number; a *header* $h$ is a sextuple $(\mathit{version}, \mathit{prevBlock}, \mathit{merkleRoot}, \mathit{time}, \mathit{bits}, \mathit{nonce})$ with an integer version, two byte strings, and three natural numbers (no length or range constraints are built into these types); a *block* $b$ is a pair $(\mathit{header}, \mathit{vtx})$ of a header and a list of transactions. $\mathrm{hash256}$ is double SHA-256; $\mathrm{txid}(tx)$ is $\mathrm{hash256}$ of the witness-stripped serialization of $tx$; $\mathrm{wtxid}(tx)$ is $\mathrm{hash256}$ of the witness serialization when some input has a non-empty witness, else $\mathrm{txid}(tx)$; $\mathrm{headerHash}(h)$ is $\mathrm{hash256}$ of the 80-byte-style serialization of $h$ (version as 4 little-endian bytes of its value mod $2^{32}$, then $\mathit{prevBlock}$ and $\mathit{merkleRoot}$ as given — whatever their lengths — then time, bits and nonce each as 4 little-endian bytes of their value mod $2^{32}$). The file imports `Def_BitcoinUtxo`, but no declaration of that file is referenced anywhere below; all ledger notions are re-defined locally.

## Constants

**`MAX_BLOCK_WEIGHT`** — the natural number $4\,000\,000$.

**`MAX_BLOCK_SIGOPS_COST`** — the natural number $80\,000$.

**`WITNESS_SCALE_FACTOR`** — the natural number $4$.

**`LOCKTIME_THRESHOLD`** — the natural number $500\,000\,000$.

**`SEQUENCE_FINAL`** — the natural number $\mathtt{0xffffffff} = 2^{32}-1$.

**`MINIMUM_WITNESS_COMMITMENT`** — the natural number $38$.

**`BIP34_IMPLIES_BIP30_LIMIT`** — the natural number $1\,983\,702$.

**`MAX_FUTURE_BLOCK_TIME`** — the integer $2\cdot 60\cdot 60 = 7200$.

**`COINBASE_MATURITY`** — the natural number $100$.

**`MAX_MONEY`** — the integer $2\,100\,000\,000\,000\,000 = 21\cdot 10^{14}$.

**`moneyRange`** — for an integer $v$, the Boolean that is true exactly when $0 \le v \le \mathrm{MAX\_MONEY}$.

**`bip34Hash`** — a fixed 32-byte string (given as a literal list of 32 byte values beginning `b8 08 08 9c …` and ending in six zero bytes).

**`bip16ExceptionHash`** — a fixed 32-byte literal (beginning `22 9c 4f ac …`, ending in six zero bytes).

**`taprootExceptionHash`** — a fixed 32-byte literal (beginning `ad 95 e3 a1 …`, ending in nine zero bytes).

**`bip30Repeat91842`** — a fixed 32-byte literal (beginning `ec ca e0 00 …`, ending in five zero bytes).

**`bip30Repeat91880`** — a fixed 32-byte literal (beginning `21 d7 7c cb …`, ending in five zero bytes).

**`bip30Unspendable91722`** — a fixed 32-byte literal (beginning `8e d0 4d 57 …`, ending in five zero bytes).

**`bip30Unspendable91812`** — a fixed 32-byte literal (beginning `2f 6f 30 f9 …`, ending in five zero bytes).

**`isBIP30Repeat`** — for a natural number $\mathit{height}$ and a byte string $\mathit{hash}$, the Boolean that is true exactly when ($\mathit{height} = 91842$ and $\mathit{hash} = $ `bip30Repeat91842`) or ($\mathit{height} = 91880$ and $\mathit{hash} = $ `bip30Repeat91880`). The two heights and the two hashes are hard-coded.

**`isBIP30Unspendable`** — for a natural number $\mathit{height}$ and a byte string $\mathit{hash}$, the Boolean that is true exactly when ($\mathit{height} = 91722$ and $\mathit{hash} = $ `bip30Unspendable91722`) or ($\mathit{height} = 91812$ and $\mathit{hash} = $ `bip30Unspendable91812`).

**`scriptException`** — for a byte string $\mathit{hash}$: the exception tag `bip16Block` if $\mathit{hash} = $ `bip16ExceptionHash`; otherwise `taprootBlock` if $\mathit{hash} = $ `taprootExceptionHash`; otherwise `none`. (In the imported activation file, `bip16Block` yields the all-false base flag set, `taprootBlock` yields the base with p2sh and witness set and taproot unset, and `none` yields p2sh, witness and taproot set.)

## Transactions

**`outPointNull`** — for an outpoint $o$, the Boolean that is true exactly when $o.\mathit{hash}$ equals the list of 32 zero bytes and $o.n = \mathtt{0xffffffff}$.

**`isCoinBase`** — for a transaction $tx$: if $\mathit{vin}(tx)$ is a list of exactly one input $i$, the value of $\mathrm{outPointNull}(i.\mathit{prevout})$; for an empty input list or two or more inputs, false.

**`isUnspendable`** — for a byte string $s$, the Boolean that is true exactly when ($0 < |s|$ and the first byte of $s$ — read with default $0$ — equals `OP_RETURN` $= \mathtt{0x6a}$) or $10\,000 < |s|$ (the constant `MAX_SCRIPT_SIZE` of the verify file is $10\,000$).

**`sumValues`** — for a list of outputs, the integer sum of their $\mathit{nValue}$ fields, $0$ for the empty list.

**`valueOut`** — for a transaction $tx$, $\mathrm{sumValues}(\mathit{vout}(tx))$, i.e. $\sum_{o\in \mathit{vout}(tx)} o.\mathit{nValue}$, an integer that may be negative since output values are unconstrained integers.

**`outputsLoop`** — for a list of outputs and an integer accumulator $\mathit{acc}$: on the empty list it returns $\mathrm{some}(\mathit{acc})$; on $o :: \mathit{rest}$ it returns "none" (failure) if $o.\mathit{nValue} < 0$, else failure if $\mathrm{MAX\_MONEY} < o.\mathit{nValue}$, else failure if $\mathit{acc} + o.\mathit{nValue}$ is not in $[0, \mathrm{MAX\_MONEY}]$, else it continues on $\mathit{rest}$ with accumulator $\mathit{acc} + o.\mathit{nValue}$. The checks are performed in that order, output by output.

**`checkTransaction`** — for a transaction $tx$, the conjunction (evaluated left to right) of: $\mathit{vin}(tx)$ is non-empty; $\mathit{vout}(tx)$ is non-empty; $4\cdot|\mathrm{serTx}(\mathrm{false}, tx)| \le 4\,000\,000$ where $\mathrm{serTx}(\mathrm{false},\cdot)$ is the witness-stripped serialization; $\mathrm{outputsLoop}(\mathit{vout}(tx), 0)$ succeeds; the list of prevouts of the inputs has no duplicates; and finally, if $\mathrm{isCoinBase}(tx)$ then $2 \le |\mathit{scriptSig}(i_0)| \le 100$ where $i_0$ is the head of $\mathit{vin}(tx)$ with default input $((\,[\,],0), [\,], 0, [\,])$ (whose scriptSig is empty), else every input has a prevout that is not null in the sense of `outPointNull`.

**`isFinalTx`** — for a transaction $tx$, a natural number $\mathit{height}$ and an integer $\mathit{blockTime}$: true if $\mathit{nLockTime}(tx) = 0$; otherwise true if $\mathit{nLockTime}(tx)$ (as an integer) is strictly less than the threshold $T$, where $T = \mathit{height}$ if $\mathit{nLockTime}(tx) < 500\,000\,000$ and $T = \mathit{blockTime}$ otherwise; otherwise true exactly when every input $i$ of $tx$ has $i.\mathit{nSequence} = \mathtt{0xffffffff}$ (vacuously true for an empty input list).

## Signature-operation counting

**`sigOpCountAux`** — a function of a Boolean $\mathit{accurate}$, a fuel $f \in \mathbb{N}$, a byte string $s$, a natural number $\mathit{last}$ (the previous opcode) and a running count $n$. If $s$ is empty the result is $n$ (regardless of fuel); if the fuel is $0$ the result is $n$; otherwise parse one instruction from $s$ with `BitcoinSig.getOp` (which reads a push opcode $\le \mathtt{0x4e}$ with its data, failing if the data or length bytes are missing, or a single non-push opcode byte): if parsing fails the result is $n$; if the instruction is a push, recurse on the remainder with fuel $f-1$, $\mathit{last} := 0$ and count unchanged; if the instruction is the opcode $c$, let $n' = n+1$ if $c \in \{\mathtt{OP\_CHECKSIG}=\mathtt{0xac}, \mathtt{OP\_CHECKSIGVERIFY}=\mathtt{0xad}\}$; else if $c \in \{\mathtt{OP\_CHECKMULTISIG}=\mathtt{0xae}, \mathtt{OP\_CHECKMULTISIGVERIFY}=\mathtt{0xaf}\}$ then $n' = n + (\mathit{last} - \mathtt{0x50})$ when $\mathit{accurate}$ holds and $\mathtt{0x51} \le \mathit{last} \le \mathtt{0x60}$ (this is `decodeOpN last`, which is $0$ for $0$ and $b - \mathtt{0x50}$ otherwise), and $n' = n + 20$ otherwise (`MAX_PUBKEYS_PER_MULTISIG` $=20$); else $n' = n$; then recurse on the remainder with fuel $f-1$, $\mathit{last} := c$ (as a natural number) and count $n'$. Thus only `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` contribute; a multisig preceded by a push contributes $20$ even in accurate mode (because a push resets $\mathit{last}$ to $0$); a multisig as the very first instruction contributes $20$ (initial $\mathit{last} = \mathtt{0xff}$); a parse failure stops the count at the value so far.

**`getSigOpCount`** — for a Boolean $\mathit{accurate}$ and a byte string $s$: $\mathrm{sigOpCountAux}(\mathit{accurate}, |s|, s, \mathtt{0xff}, 0)$.

**`lastPushAux`** — a function of a fuel, a byte string $s$ and a byte string $d$ (the last datum): on empty $s$ returns $\mathrm{some}(d)$; with fuel $0$ returns none; otherwise parse one instruction: a parse failure gives none; a push of data $d'$ recurses with $d := d'$; a non-push opcode $c$ gives none if $\mathtt{OP\_16}=\mathtt{0x60} < c$ and otherwise recurses with $d := [\,]$ (the empty string, i.e. an `OP_0`/`OP_1`…`OP_16`/`OP_RESERVED`/`OP_1NEGATE` opcode makes the last datum empty).

**`lastPush`** — for a byte string $s$: $\mathrm{lastPushAux}(|s|, s, [\,])$; for the empty script this is $\mathrm{some}([\,])$.

**`p2shSigOpCount`** — for byte strings $\mathit{scriptPubKey}$ and $\mathit{scriptSig}$: $0$ unless $\mathit{scriptPubKey}$ is pay-to-script-hash (length exactly $23$, first byte $\mathtt{0xa9}$, second byte $\mathtt{0x14}$, byte $22$ equal to $\mathtt{0x87}$); if it is, then $0$ when $\mathrm{lastPush}(\mathit{scriptSig})$ is none, and otherwise $\mathrm{getSigOpCount}(\mathrm{true}, d)$ for the last-pushed datum $d$. This term does not itself check that the input's transaction is not a coinbase; that is done by the caller.

**`witnessSigOps`** — for a natural number $\mathit{version}$, a byte string $\mathit{program}$ and a witness stack (list of byte strings): if $\mathit{version} = 0$ then $1$ if $|\mathit{program}| = 20$; else $\mathrm{getSigOpCount}(\mathrm{true}, w)$ where $w$ is the last element of the witness stack, if $|\mathit{program}| = 32$ and the stack is non-empty; else $0$. For $\mathit{version} \ne 0$ the result is $0$.

**`countWitnessSigOps`** — for a flag record $f$, byte strings $\mathit{scriptSig}$, $\mathit{scriptPubKey}$ and a witness stack: $0$ if $f.\mathit{witness}$ is false. Otherwise, if $\mathit{scriptPubKey}$ is a witness program $(v, p)$ — meaning $4 \le |\mathit{scriptPubKey}| \le 42$, its first byte is $0$ or in $[\mathtt{0x51}, \mathtt{0x60}]$, and its second byte plus $2$ equals its length, with $v$ the decoded first byte and $p$ the bytes after the first two — the result is $\mathrm{witnessSigOps}(v, p, \mathit{witness})$. Otherwise, if $\mathit{scriptPubKey}$ is pay-to-script-hash and $\mathit{scriptSig}$ is push-only (every instruction parses and is a push or an opcode $\le \mathtt{0x60}$), then with $d = \mathrm{lastPush}(\mathit{scriptSig})$: $0$ if none; else if $d$ is a witness program $(v, p)$ then $\mathrm{witnessSigOps}(v, p, \mathit{witness})$, else $0$. In every other case $0$.

**`legacySigOpCount`** — for a transaction $tx$: $\sum_{i \in \mathit{vin}(tx)} \mathrm{getSigOpCount}(\mathrm{false}, i.\mathit{scriptSig}) + \sum_{o \in \mathit{vout}(tx)} \mathrm{getSigOpCount}(\mathrm{false}, o.\mathit{scriptPubKey})$ — inaccurate mode, so every multisig opcode counts $20$.

## The ledger

**`Coin`** — a structure with three fields: $\mathit{out}$ (an output), $\mathit{height}$ (a natural number) and $\mathit{isCoinbase}$ (a Boolean); it has decidable equality.

**`dummyCoin`** — the coin whose output is $(-1, [\,])$, whose height is $0$ and whose coinbase flag is false.

**`Ledger`** — an abbreviation for lists of pairs (outpoint, coin); no uniqueness of keys is built into the type.

**`getCoin`** — for a ledger $u$ and an outpoint $\mathit{op}$: none on the empty list; on $(k, c) :: \mathit{rest}$, $\mathrm{some}(c)$ if $k = \mathit{op}$ and otherwise the lookup in $\mathit{rest}$ (so the *first* matching entry wins).

**`haveCoin`** — for a ledger $u$ and outpoint $\mathit{op}$, the Boolean "$\mathrm{getCoin}(u, \mathit{op})$ is some".

**`accessCoin`** — for a ledger $u$ and outpoint $\mathit{op}$: the coin $\mathrm{getCoin}(u, \mathit{op})$ if present, else `dummyCoin` (value $-1$, empty script, height $0$, not coinbase).

**`spendCoin`** — for a ledger and outpoint $\mathit{op}$: the ledger with *every* entry whose key equals $\mathit{op}$ removed, order of the rest preserved.

**`addCoin`** — for a ledger $u$, outpoint $\mathit{op}$ and coin $c$: $u$ unchanged if $\mathrm{isUnspendable}(c.\mathit{out}.\mathit{scriptPubKey})$; otherwise the entry $(\mathit{op}, c)$ prepended to $\mathrm{spendCoin}(u, \mathit{op})$.

**`addCoinsFrom`** — for a byte string $\mathit{txid}$, a natural number $\mathit{height}$, a Boolean $\mathit{cb}$, a ledger $u$, an index $i$ and a list of outputs: on the empty list returns $u$; on $o :: \mathit{rest}$ recurses on $\mathit{rest}$ with index $i+1$ and ledger $\mathrm{addCoin}(u, (\mathit{txid}, i), (o, \mathit{height}, \mathit{cb}))$.

**`spendInputs`** — for a ledger $u$ and a list of inputs: successively $\mathrm{spendCoin}$ of each input's prevout, in list order.

**`updateCoins`** — for a ledger $u$, transaction $tx$ and natural number $\mathit{height}$: $\mathrm{addCoinsFrom}(\mathrm{txid}(tx), \mathit{height}, \mathrm{isCoinBase}(tx), u', 0, \mathit{vout}(tx))$ where $u' = u$ if $\mathrm{isCoinBase}(tx)$ and $u' = \mathrm{spendInputs}(u, \mathit{vin}(tx))$ otherwise. Outputs are added at indices $0, 1, \dots$ with the transaction's coinbase flag; unspendable outputs are not stored.

**`txUndo`** — for a ledger $u$ and transaction $tx$: the list, in input order, of $\mathrm{accessCoin}(u, i.\mathit{prevout})$ for each input $i$ (a missing coin yields `dummyCoin`).

**`BlockUndo`** — an abbreviation for lists of lists of coins.

**`Equiv`** — for ledgers $u, v$, the proposition $\forall \mathit{op},\ \mathrm{getCoin}(u, \mathit{op}) = \mathrm{getCoin}(v, \mathit{op})$.

**`keysNodup`** — for a ledger $u$, the proposition that the list of its keys (first components) has no duplicates.

## `CheckTxInputs` and the per-transaction checks

**`inputsLoop`** — for a ledger $u$, a natural number $\mathit{spendHeight}$, a list of inputs and an integer accumulator $\mathit{acc}$: on the empty list, $\mathrm{some}(\mathit{acc})$; on $i :: \mathit{rest}$: failure if $\mathrm{getCoin}(u, i.\mathit{prevout})$ is none; otherwise with that coin, failure if $\mathit{coin}.\mathit{isCoinbase}$ and $\mathit{spendHeight} \mathbin{\dot-} \mathit{coin}.\mathit{height} < 100$ (natural-number subtraction, truncated at $0$, so a coinbase coin whose height exceeds $\mathit{spendHeight}$ is always immature); otherwise with $\mathit{acc}' = \mathit{acc} + \mathit{coin}.\mathit{out}.\mathit{nValue}$, failure if $\mathit{coin}.\mathit{out}.\mathit{nValue} \notin [0, \mathrm{MAX\_MONEY}]$ or $\mathit{acc}' \notin [0, \mathrm{MAX\_MONEY}]$; otherwise continue on $\mathit{rest}$ with $\mathit{acc}'$.

**`checkTxInputs`** — for a ledger $u$, a transaction $tx$ and natural number $\mathit{spendHeight}$: none unless every input's prevout has a coin in $u$; then none if $\mathrm{inputsLoop}(u, \mathit{spendHeight}, \mathit{vin}(tx), 0)$ fails; otherwise with its value $V_{in}$: none if $V_{in} < \mathrm{valueOut}(tx)$; none if $V_{in} - \mathrm{valueOut}(tx) \notin [0, \mathrm{MAX\_MONEY}]$; otherwise $\mathrm{some}(V_{in} - \mathrm{valueOut}(tx))$. For an empty input list this is $\mathrm{some}(0 - \mathrm{valueOut}(tx))$ when $\mathrm{valueOut}(tx) \le 0$ and $-\mathrm{valueOut}(tx) \le \mathrm{MAX\_MONEY}$.

**`txSigOpCost`** — for flags $f$, ledger $u$ and transaction $tx$: $4 \cdot \mathrm{legacySigOpCount}(tx) + C$, where $C = 0$ if $\mathrm{isCoinBase}(tx)$ and otherwise
$$C = \Big(\text{if } f.\mathit{p2sh} \text{ then } 4\cdot\!\!\sum_{i\in\mathit{vin}(tx)}\!\! \mathrm{p2shSigOpCount}(\mathrm{accessCoin}(u, i.\mathit{prevout}).\mathit{out}.\mathit{scriptPubKey},\ i.\mathit{scriptSig}) \text{ else } 0\Big) + \sum_{i\in\mathit{vin}(tx)} \mathrm{countWitnessSigOps}(f, i.\mathit{scriptSig}, \mathrm{accessCoin}(u, i.\mathit{prevout}).\mathit{out}.\mathit{scriptPubKey}, i.\mathit{witness}).$$
Missing coins contribute via the dummy coin's empty script (which is neither P2SH nor a witness program, hence $0$). The witness term is not multiplied by $4$.

**`sequenceLocksOk`** — for a ledger $u$, natural numbers $\mathit{height}$ and $\mathit{lockTimeFlags}$, a function $\mathit{mtp} : \mathbb{N}\to\mathbb{N}$ and a transaction $tx$: the Boolean `BitcoinBIP68.sequenceLocks` applied to $\mathit{version}(tx)$ and $\mathit{lockTimeFlags}$ both reduced to 32-bit words, the context $(\mathit{height}, \mathit{mtp})$, and the list of pairs $(\mathit{nSequence}(i) \bmod 2^{32}, \mathrm{accessCoin}(u, i.\mathit{prevout}).\mathit{height})$ over the inputs (missing coins give height $0$). That imported function: if $2 \le \mathit{version}$ and bit $0$ of the flags is set, folds over the inputs starting from $(\mathit{minHeight}, \mathit{minTime}) = (-1, -1)$, skipping inputs whose sequence has bit $31$ set, and otherwise raising $\mathit{minTime}$ to $\mathit{mtp}(h_c \mathbin{\dot-} 1) + ((\mathit{seq} \mathbin{\&} \mathtt{0xffff}) \cdot 512) - 1$ when bit $22$ is set and raising $\mathit{minHeight}$ to $h_c + (\mathit{seq} \mathbin{\&} \mathtt{0xffff}) - 1$ otherwise; and finally returns true exactly when $\mathit{minHeight} < \mathit{height}$ and $\mathit{minTime} < \mathit{mtp}(\mathit{height} \mathbin{\dot-} 1)$. When not enabled, the accumulator stays at $(-1,-1)$ and the result is true provided $-1 < \mathit{height}$ and $-1 < \mathit{mtp}(\mathit{height}\mathbin{\dot-}1)$, which always holds for natural numbers.

**`inputScriptsOk`** — for flags $f$, ledger $u$ and transaction $tx$: let $\mathit{spent}$ be the list of outputs $\mathrm{accessCoin}(u, i.\mathit{prevout}).\mathit{out}$ over the inputs; the result is true exactly when for every index $n < |\mathit{vin}(tx)|$, with $i$ the $n$-th input (default input if out of range, which cannot occur) and $\mathit{coin} = \mathrm{accessCoin}(u, i.\mathit{prevout})$, the complete script verifier `BitcoinTaproot.verifyScriptFull` returns true on $\mathit{spent}$, the context $(f, tx, n, \mathit{coin}.\mathit{out}.\mathit{nValue})$, $i.\mathit{scriptSig}$, $\mathit{coin}.\mathit{out}.\mathit{scriptPubKey}$ and $i.\mathit{witness}$. (That verifier is the imported `VerifyScript` with P2SH, witness v0 and the Taproot branch; for a missing coin the amount is $-1$ and the script is empty.) Vacuously true for a transaction with no inputs.

**`LoopState`** — a structure with fields $\mathit{utxo}$ (a ledger), $\mathit{fees}$ (an integer), $\mathit{sigOps}$ (a natural number) and $\mathit{undo}$ (a block undo).

**`connectLoop`** — for flags $f$, a natural number $\mathit{height}$, $\mathit{mtp} : \mathbb{N}\to\mathbb{N}$, a natural number $\mathit{lockTimeFlags}$, a loop state $\mathit{st}$ and a list of transactions: on the empty list, $\mathrm{some}(\mathit{st})$. On $tx :: \mathit{rest}$, first compute $\mathit{step}$: if $\mathrm{isCoinBase}(tx)$ then $\mathrm{some}(\mathit{st}.\mathit{fees}, \mathit{st}.\mathit{undo})$; otherwise none if $\mathrm{checkTxInputs}(\mathit{st}.\mathit{utxo}, tx, \mathit{height})$ is none; else with its fee, none if $\mathit{st}.\mathit{fees} + \mathit{fee} \notin [0, \mathrm{MAX\_MONEY}]$; else none if $\mathrm{sequenceLocksOk}(\mathit{st}.\mathit{utxo}, \mathit{height}, \mathit{mtp}, \mathit{lockTimeFlags}, tx)$ is false; else $\mathrm{some}(\mathit{st}.\mathit{fees} + \mathit{fee},\ \mathit{st}.\mathit{undo} \mathbin{+\!\!+} [\mathrm{txUndo}(\mathit{st}.\mathit{utxo}, tx)])$. If $\mathit{step}$ is none the result is none. Otherwise with $(\mathit{fees}, \mathit{undo})$: let $\mathit{sigOps} = \mathit{st}.\mathit{sigOps} + \mathrm{txSigOpCost}(f, \mathit{st}.\mathit{utxo}, tx)$; none if $80\,000 < \mathit{sigOps}$; none if $tx$ is not a coinbase and $\mathrm{inputScriptsOk}(f, \mathit{st}.\mathit{utxo}, tx)$ is false; otherwise recurse on $\mathit{rest}$ with state $(\mathrm{updateCoins}(\mathit{st}.\mathit{utxo}, tx, \mathit{height}), \mathit{fees}, \mathit{sigOps}, \mathit{undo})$. A coinbase transaction anywhere in the list (not only first) is treated by the coinbase branch; a non-coinbase with an empty input list passes `checkTxInputs` with fee $-\mathrm{valueOut}(tx)$ when that is in range.

## Chain state

**`ChainState`** — a structure with fields $\mathit{headers}$ (a list of headers) and $\mathit{utxo}$ (a ledger).

**`initialState`** — the chain state whose header list is the single genesis header (the imported `genesisHeader`: version $1$, 32 zero bytes as previous hash, the txid of the genesis coinbase as merkle root, time $1231006505$, bits $\mathtt{0x1d00ffff}$, nonce $2083236893$) and whose ledger is empty.

**`ChainState.tipHeight`** — $|S.\mathit{headers}| \mathbin{\dot-} 1$ (natural-number subtraction: $0$ for an empty header list).

**`ChainState.tip`** — the last header of $S.\mathit{headers}$, or the genesis header if the list is empty.

**`ChainState.tipHash`** — $\mathrm{headerHash}(S.\mathit{tip})$.

**`ChainState.nextHeight`** — $|S.\mathit{headers}|$.

**`ChainState.timesTo`** — for a natural number $h$: the list of the $\mathit{time}$ fields (as integers) of the first $h+1$ headers of $S.\mathit{headers}$, reversed (so most recent first); shorter if the list has fewer than $h+1$ headers.

**`ChainState.mtpAt`** — for $h$: `BitcoinHeader.medianTimePast` of $S.\mathrm{timesTo}(h)$, i.e. take the first $11$ elements of that list, sort them ascending, and return the element at index $\lfloor \ell/2 \rfloor$ where $\ell$ is the length of the window, with default $0$ for an empty window.

**`ChainState.mtp`** — $S.\mathrm{mtpAt}(S.\mathrm{tipHeight})$.

**`ChainState.mtpNat`** — for $h$: $\max(S.\mathrm{mtpAt}(h), 0)$ as a natural number (integer-to-natural truncation).

**`ChainState.requiredBits`** — let $\mathit{first}$ be the header at index $S.\mathrm{tipHeight} \mathbin{\dot-} 2015$ of $S.\mathit{headers}$ (the imported `difficultyAdjustmentInterval` is $1209600/600 = 2016$; the index uses truncated subtraction, so it is $0$ when the tip height is below $2015$; the default when the index is out of range is the genesis header). The result is `BitcoinPow.nextWorkRequired` of $S.\mathrm{tipHeight}$, the tip's $\mathit{bits}$ reduced to a 32-bit word, the tip's time and $\mathit{first}$'s time: namely the tip's bits when $(S.\mathrm{tipHeight}+1) \bmod 2016 \ne 0$, and otherwise the retargeted compact word (decode the tip's bits, multiply by the timespan $\mathit{tip.time} - \mathit{first.time}$ clamped to $[302400, 4838400]$ modulo $2^{256}$, divide by $1209600$, cap at $2^{224}-1$, re-encode).

**`blockProof`** — for a natural number $\mathit{bits}$: with `BitcoinPow.deriveTarget` of $\mathit{bits} \bmod 2^{32}$ (none when the compact word is negative, decodes to $0$, overflows, or exceeds $2^{224}-1$): $0$ if none, else $\big\lfloor (2^{256} - 1 - t)/(t+1) \big\rfloor + 1$ for the target $t$.

**`ChainState.chainWork`** — $\sum_{h \in S.\mathit{headers}} \mathrm{blockProof}(h.\mathit{bits})$.

**`hashValue`** — for a header $h$: the little-endian integer value of the byte string $\mathrm{headerHash}(h)$ (first byte least significant).

## `CheckBlock`

**`merkleCombine`** — for byte strings $a, b$: $\mathrm{hash256}(a \mathbin{+\!\!+} b)$.

**`zeroHash`** — the list of 32 zero bytes.

**`blockMerkleRoot`** — for a block $b$: the pair (root, mutated-flag) produced by the imported `computeMerkleRoot` with combiner `merkleCombine`, empty-list value `zeroHash`, on the list of txids of $b.\mathit{vtx}$: repeatedly hash adjacent pairs (an odd trailing element is hashed with itself) until one element remains, setting the flag if at any level some aligned pair $(2k, 2k+1)$ consists of equal hashes; for an empty transaction list the root is `zeroHash` and the flag is false; for a single transaction the root is its txid.

**`blockWitnessMerkleRoot`** — for a block $b$: the root (first component) of the same computation on the list $\mathrm{zeroHash} :: [\mathrm{wtxid}(tx) \mid tx \in b.\mathit{vtx} \text{ after the first}]$; the mutation flag is discarded.

**`checkHeaderPow`** — for a header $h$: `BitcoinPow.checkProofOfWork` of $\mathrm{hashValue}(h)$ and $h.\mathit{bits} \bmod 2^{32}$: false if `deriveTarget` is none, else true exactly when $\mathrm{hashValue}(h) \le t$ for the derived target $t$ (the 256-bit-truncated `setCompact` value).

**`checkBlock`** — for a block $b$, the left-to-right conjunction of: $\mathrm{checkHeaderPow}(b.\mathit{header})$; $(\mathrm{blockMerkleRoot}\,b).1 = b.\mathit{header}.\mathit{merkleRoot}$; the mutation flag $(\mathrm{blockMerkleRoot}\,b).2$ is false; $b.\mathit{vtx}$ is non-empty; $4\cdot|b.\mathit{vtx}| \le 4\,000\,000$; $4 \cdot |\mathrm{serBlock}(\mathrm{false}, b)| \le 4\,000\,000$ (witness-stripped block serialization); $\mathrm{isCoinBase}$ of the first transaction (default: the genesis coinbase); every transaction after the first is not a coinbase; every transaction satisfies `checkTransaction`; and $4 \cdot \sum_{tx \in b.\mathit{vtx}} \mathrm{legacySigOpCount}(tx) \le 80\,000$.

## `ContextualCheckBlock`

**`heightScript`** — for a natural number $n$: the one-byte string $[\mathtt{0x00}]$ if $n = 0$; the one-byte string $[\mathtt{0x50} + n]$ if $1 \le n \le 16$; otherwise the canonical push (`pushBytes`: a length byte for data under $76$ bytes, else `OP_PUSHDATA1/2/4` prefixes) of the script-number encoding of $n$ (little-endian magnitude bytes with a sign byte appended when the top bit of the last byte is set).

**`isCommitmentOutput`** — for an output $o$: $38 \le |o.\mathit{scriptPubKey}|$ and the first six bytes of $o.\mathit{scriptPubKey}$ are `6a 24 aa 21 a9 ed`.

**`witnessCommitmentIndex`** — for a block $b$: none if $b.\mathit{vtx}$ is empty; otherwise, with $cb$ the first transaction, the *last* index $i < |\mathit{vout}(cb)|$ such that $\mathrm{isCommitmentOutput}(\mathit{vout}(cb)_i)$ (default output $(0, [\,])$ for an out-of-range index, which cannot occur), or none if there is no such index.

**`checkWitnessMalleation`** — for a block $b$ and Boolean $\mathit{expect}$: let $\mathit{noWitness}$ be "no transaction of $b$ has an input with a non-empty witness". If $\mathit{expect}$ is false the result is $\mathit{noWitness}$. If $\mathit{expect}$ is true: if $\mathrm{witnessCommitmentIndex}(b)$ is none the result is $\mathit{noWitness}$; otherwise with index $\mathit{pos}$, $cb$ the first transaction (default the genesis coinbase) and $\mathit{stack}$ the witness of the first input of $cb$ (default: empty), the result is false unless $\mathit{stack}$ is a one-element list $[\mathit{nonce}]$, in which case it is true exactly when $|\mathit{nonce}| = 32$ and $\mathrm{hash256}(\mathrm{blockWitnessMerkleRoot}(b) \mathbin{+\!\!+} \mathit{nonce})$ equals bytes $6$ through $37$ (drop $6$, take $32$) of the scriptPubKey of $\mathit{vout}(cb)_{\mathit{pos}}$.

**`contextualCheckBlock`** — for a chain state $S$ and block $b$: let $\mathit{height} = S.\mathrm{nextHeight}$ and $\mathit{cutoff} = S.\mathit{mtp}$ if CSV is active after the tip (i.e. $419328 \le S.\mathrm{tipHeight}+1$) and $\mathit{cutoff} = b.\mathit{header}.\mathit{time}$ otherwise. The result is the conjunction of: every $tx \in b.\mathit{vtx}$ satisfies $\mathrm{isFinalTx}(tx, \mathit{height}, \mathit{cutoff})$; either BIP34 is not active after the tip ($227931 > S.\mathrm{tipHeight}+1$) or $\mathrm{heightScript}(\mathit{height})$ is a prefix of the scriptSig of the first input of the first transaction (defaults: genesis coinbase, then an input with empty scriptSig); $\mathrm{checkWitnessMalleation}(b, e)$ where $e$ is "SegWit active after the tip", i.e. $481824 \le S.\mathrm{tipHeight}+1$; and $\mathrm{blockWeight}(b) \le 4\,000\,000$ where $\mathrm{blockWeight}(b) = 3\cdot|\mathrm{serBlock}(\mathrm{false}, b)| + |\mathrm{serBlock}(\mathrm{true}, b)|$.

## `ConnectBlock`

**`bip30Checked`** — for a chain state $S$, natural number $\mathit{height}$ and byte string $\mathit{hash}$: let $\mathit{bip34Ancestor}$ be true exactly when $S.\mathit{headers}$ has an element at index $227931$ and its header hash equals `bip34Hash`. The result is $\big(\lnot \mathrm{isBIP30Repeat}(\mathit{height}, \mathit{hash}) \land \lnot \mathit{bip34Ancestor}\big) \lor 1\,983\,702 \le \mathit{height}$.

**`bip30Ok`** — for a ledger $u$ and block $b$: true exactly when for every $tx \in b.\mathit{vtx}$ and every index $o < |\mathit{vout}(tx)|$, $u$ has no coin at outpoint $(\mathrm{txid}(tx), o)$.

**`connectBlock`** — for a chain state $S$ and block $b$: let $\mathit{hash} = \mathrm{headerHash}(b.\mathit{header})$ and $\mathit{height} = S.\mathrm{nextHeight}$. If $\mathit{hash}$ equals the imported `genesisHash` (a fixed 32-byte literal), return $\mathrm{some}(S.\mathit{utxo}, [\,])$ without any further check. Else if $\mathrm{bip30Checked}(S, \mathit{height}, \mathit{hash})$ and $\lnot\mathrm{bip30Ok}(S.\mathit{utxo}, b)$, return none. Else let $\mathit{flags}$ be `blockScriptFlags`$(\mathit{height}, \mathrm{scriptException}(\mathit{hash}))$ (the exception base, with dersig/cltv/csv/nulldummy added when $363725 / 388381 / 419328 / 481824 \le \mathit{height}$ respectively) and run $\mathrm{connectLoop}(\mathit{flags}, \mathit{height}, S.\mathrm{mtpNat}, \mathrm{lockTimeFlags}(\mathit{height}), (S.\mathit{utxo}, 0, 0, [\,]), b.\mathit{vtx})$ where $\mathrm{lockTimeFlags}(\mathit{height}) = 1$ if $419328 \le \mathit{height}$ and $0$ otherwise. If it fails, none; otherwise with final state $\mathit{st}$, none if $\mathrm{valueOut}(tx_0) > \mathit{st}.\mathit{fees} + \mathrm{coreSubsidy}(\mathit{height})$ where $tx_0$ is the first transaction (default genesis coinbase) and $\mathrm{coreSubsidy}(\mathit{height})$ is $0$ when $\lfloor \mathit{height}/210000 \rfloor \ge 64$ and $5\cdot 10^9$ shifted right by $\lfloor \mathit{height}/210000\rfloor$ otherwise; else $\mathrm{some}(\mathit{st}.\mathit{utxo}, \mathit{st}.\mathit{undo})$.

## The complete validation path

**`Outcome`** — an inductive type with four constructors: $\mathrm{accept}(S', \mathit{undo})$ carrying a chain state and a block undo; $\mathrm{invalid}$; $\mathrm{futureTime}$; $\mathrm{missingPrev}$.

**`acceptHeader`** — for a chain state $S$, header $h$ and integer $\mathit{now}$, the first applicable case of: $\mathrm{invalid}$ if $\lnot\mathrm{checkHeaderPow}(h)$; $\mathrm{missingPrev}$ if $h.\mathit{prevBlock} \ne S.\mathrm{tipHash}$; $\mathrm{invalid}$ if $h.\mathit{bits} \bmod 2^{32} \ne S.\mathrm{requiredBits}$; $\mathrm{invalid}$ if $h.\mathit{time} \le S.\mathit{mtp}$; $\mathrm{futureTime}$ if $\mathit{now} + 7200 < h.\mathit{time}$; $\mathrm{invalid}$ if `versionOutdated`$(h.\mathit{version}, S.\mathrm{tipHeight})$, i.e. $(h.\mathit{version} < 2 \land 227931 \le S.\mathrm{tipHeight}+1) \lor (h.\mathit{version} < 3 \land 363725 \le S.\mathrm{tipHeight}+1) \lor (h.\mathit{version} < 4 \land 388381 \le S.\mathrm{tipHeight}+1)$; otherwise $\mathrm{accept}(S, [\,])$ — the *unchanged* state with empty undo.

**`validate`** — for $S$, block $b$ and integer $\mathit{now}$: if $\mathrm{acceptHeader}(S, b.\mathit{header}, \mathit{now})$ is $\mathrm{accept}(\_, \_)$ (its payload ignored), then $\mathrm{invalid}$ if $\lnot\mathrm{checkBlock}(b)$; else $\mathrm{invalid}$ if $\lnot\mathrm{contextualCheckBlock}(S, b)$; else $\mathrm{invalid}$ if $\mathrm{connectBlock}(S, b)$ is none; else $\mathrm{accept}\big((S.\mathit{headers} \mathbin{+\!\!+} [b.\mathit{header}],\ u),\ \mathit{undo}\big)$ for the returned $(u, \mathit{undo})$. If $\mathrm{acceptHeader}$ returns any other outcome $o$, the result is that same $o$.

**`accepts`** — the proposition $\exists S'\, \mathit{undo},\ \mathrm{validate}(S, b, \mathit{now}) = \mathrm{accept}(S', \mathit{undo})$.

**`Reachable`** — an inductively defined predicate on chain states: `initialState` is reachable; and if $S$ is reachable and $\mathrm{validate}(S, b, \mathit{now}) = \mathrm{accept}(S', \mathit{undo})$ for some block $b$, integer $\mathit{now}$ and undo, then $S'$ is reachable. Nothing else is reachable.

## `DisconnectBlock`

**`applyTxInUndo`** — for a ledger $u$, a coin $\mathit{undo}$ and an outpoint $\mathit{out}$: let $\mathit{clean} = \lnot\mathrm{haveCoin}(u, \mathit{out})$. If $\mathit{undo}.\mathit{height} = 0$, search $u$ for the first entry whose key has the same $\mathit{hash}$ as $\mathit{out}$ (any index): if found with coin $\mathit{alt}$, use the coin $\mathit{undo}$ with height and coinbase flag replaced by those of $\mathit{alt}$; if not found, return none. If $\mathit{undo}.\mathit{height} \ne 0$ use $\mathit{undo}$ itself. Return $\mathrm{some}(\mathrm{addCoin}(u, \mathit{out}, c), \mathit{clean})$ for the chosen coin $c$ (so an unspendable restored coin is silently not added).

**`restoreInputs`** — for a ledger $u$ and a list of (input, coin) pairs: on the empty list, $\mathrm{some}(u, \mathrm{true})$; on $(i, c) :: \mathit{rest}$, first restore $\mathit{rest}$ (so the list is processed from its end), failing if that fails, then $\mathrm{applyTxInUndo}(u', c, i.\mathit{prevout})$ on the resulting ledger, failing if that fails, and return the final ledger with the conjunction of the two clean flags.

**`spendOutputs`** — for a ledger $u$, byte string $\mathit{txid}$, natural number $\mathit{height}$, Booleans $\mathit{cb}$ and $\mathit{exception}$, a list of outputs and an index $i$: on the empty list, $(u, \mathrm{true})$; on $o :: \mathit{rest}$: if $\mathrm{isUnspendable}(o.\mathit{scriptPubKey})$ the ledger is unchanged and this output is clean; otherwise with $\mathit{op} = (\mathit{txid}, i)$, let $\mathit{ok}$ be "there is a coin at $\mathit{op}$ in $u$ whose output equals $o$, whose height equals $\mathit{height}$ and whose coinbase flag equals $\mathit{cb}$", the ledger becomes $\mathrm{spendCoin}(u, \mathit{op})$ and the flag is $\mathit{ok} \lor \mathit{exception}$; then continue on $\mathit{rest}$ with index $i+1$, and the overall flag is the conjunction. This never fails (it always returns a pair).

**`disconnectTx`** — for a ledger $u$, height, Boolean $\mathit{exception}$, transaction $tx$ and optional coin list $\mathit{undo}$: let $\mathit{cb} = \mathrm{isCoinBase}(tx)$ and $(u', \mathit{clean}) = \mathrm{spendOutputs}(u, \mathrm{txid}(tx), \mathit{height}, \mathit{cb}, \mathit{cb} \land \mathit{exception}, \mathit{vout}(tx), 0)$. If $\mathit{undo}$ is none, return $\mathrm{some}(u', \mathit{clean})$. If it is $\mathrm{some}(\mathit{coins})$: none if $|\mathit{coins}| \ne |\mathit{vin}(tx)|$; else $\mathrm{restoreInputs}(u', \mathrm{zip}(\mathit{vin}(tx), \mathit{coins}))$, propagating none, and returning the conjunction of the clean flags. Note the inputs are restored whenever an undo list is supplied, regardless of $\mathit{cb}$.

**`disconnectTxs`** — for height, exception flag, a ledger and a list of (transaction, optional coin list) pairs: process the pairs in list order with `disconnectTx`, threading the ledger, propagating none, and conjoining the clean flags; the empty list gives $\mathrm{some}(u, \mathrm{true})$.

**`disconnectBlock`** — for a ledger $u$, natural number $\mathit{height}$, byte string $\mathit{hash}$, block $b$ and block undo $\mathit{undo}$: none if $|\mathit{undo}| + 1 \ne |b.\mathit{vtx}|$; otherwise $\mathrm{disconnectTxs}(\mathit{height}, \mathrm{isBIP30Unspendable}(\mathit{height}, \mathit{hash}), u, L)$ where $L$ is the *reverse* of the pairing of $b.\mathit{vtx}$ with the list $\mathrm{none} :: [\mathrm{some}(c) \mid c \in \mathit{undo}]$ (so the first transaction gets no undo list and is processed last).

## The declarative specification and `ApplySpec`

**`TxSpec`** — for a transaction $tx$, the proposition: $\mathit{vin}(tx) \ne [\,]$, and $\mathit{vout}(tx) \ne [\,]$, and $4\cdot|\mathrm{serTx}(\mathrm{false}, tx)| \le 4\,000\,000$, and every output $o$ has $0 \le o.\mathit{nValue} \le \mathrm{MAX\_MONEY}$, and $\mathrm{valueOut}(tx) \le \mathrm{MAX\_MONEY}$, and the prevouts of the inputs are pairwise distinct, and (if $\mathrm{isCoinBase}(tx)$ then every input $i$ has $2 \le |i.\mathit{scriptSig}| \le 100$), and (if $\lnot\mathrm{isCoinBase}(tx)$ then every input has a prevout that is not null).

**`valueIn`** — for a ledger $u$ and a list of inputs: $\sum_i \mathrm{accessCoin}(u, i.\mathit{prevout}).\mathit{out}.\mathit{nValue}$, with a missing coin contributing $-1$; $0$ for the empty list.

**`feeOf`** — $\mathrm{valueIn}(u, \mathit{vin}(tx)) - \mathrm{valueOut}(tx)$, an integer.

**`TxInputsSpec`** — for flags $f$, ledger $u$, natural numbers $\mathit{height}$ and $\mathit{lockTimeFlags}$, $\mathit{mtp} : \mathbb{N}\to\mathbb{N}$ and transaction $tx$, the proposition:
$$\begin{aligned} &\forall i \in \mathit{vin}(tx),\ \exists c,\ \mathrm{getCoin}(u, i.\mathit{prevout}) = \mathrm{some}(c) \land (c.\mathit{isCoinbase} \to c.\mathit{height} + 100 \le \mathit{height}) \land 0 \le c.\mathit{out}.\mathit{nValue} \le \mathrm{MAX\_MONEY};\\ &\mathrm{valueIn}(u, \mathit{vin}(tx)) \le \mathrm{MAX\_MONEY};\quad \mathrm{valueOut}(tx) \le \mathrm{valueIn}(u, \mathit{vin}(tx));\\ &\text{`BitcoinBIP68.satisfiesBIP68`}(\mathit{version}(tx) \bmod 2^{32},\ \mathit{lockTimeFlags} \bmod 2^{32},\ (\mathit{height}, \mathit{mtp}),\ [(\mathit{nSequence}(i) \bmod 2^{32}, \mathrm{accessCoin}(u, i.\mathit{prevout}).\mathit{height})]_i);\\ &\forall n < |\mathit{vin}(tx)|,\ \text{`verifyScriptFull`}(\mathit{spent}, (f, tx, n, \mathit{coin}_n.\mathit{out}.\mathit{nValue}), i_n.\mathit{scriptSig}, \mathit{coin}_n.\mathit{out}.\mathit{scriptPubKey}, i_n.\mathit{witness}) = \mathrm{true}, \end{aligned}$$
where $\mathit{spent}$ is the list of $\mathrm{accessCoin}(u, j.\mathit{prevout}).\mathit{out}$ over all inputs $j$ and $\mathit{coin}_n = \mathrm{accessCoin}(u, i_n.\mathit{prevout})$. The imported `satisfiesBIP68` is: either not enabled ($\mathit{version} < 2$ or the flags word is even), or every listed input is disabled (sequence $\ge 2^{31}$) or satisfied: when bit 22 of the sequence is set, $\mathit{mtp}(h_c \mathbin{\dot-} 1) + 512\cdot(\mathit{seq} \bmod 2^{16}) \le \mathit{mtp}(\mathit{height} \mathbin{\dot-} 1)$, else $h_c + (\mathit{seq} \bmod 2^{16}) \le \mathit{height}$.

**`TxsSpec`** — for flags $f$, $\mathit{height}$, $\mathit{mtp}$, $\mathit{lockTimeFlags}$, a ledger $u$, integer $\mathit{fees}$, natural number $\mathit{sigOps}$ and a list of transactions: true for the empty list; for $tx :: \mathit{rest}$, the conjunction of $\big(\mathrm{isCoinBase}(tx) = \mathrm{false} \to \mathrm{TxInputsSpec}(f, u, \mathit{height}, \mathit{mtp}, \mathit{lockTimeFlags}, tx) \land \mathit{fees} + \mathrm{feeOf}(u, tx) \le \mathrm{MAX\_MONEY}\big)$, $\mathit{sigOps} + \mathrm{txSigOpCost}(f, u, tx) \le 80\,000$, and $\mathrm{TxsSpec}$ on $\mathit{rest}$ with ledger $\mathrm{updateCoins}(u, tx, \mathit{height})$, fees $\mathit{fees}$ if coinbase else $\mathit{fees} + \mathrm{feeOf}(u, tx)$, and sigops $\mathit{sigOps} + \mathrm{txSigOpCost}(f, u, tx)$. No lower bound on the fee total is stated.

**`applyTxs`** — for a height, a ledger and a list of transactions: the left fold of $\mathrm{updateCoins}(\cdot, tx, \mathit{height})$ over the list.

**`totalFees`** — for a height, ledger $u$ and list: $0$ for the empty list; for $tx :: \mathit{rest}$, $(0$ if coinbase else $\mathrm{feeOf}(u, tx)) + \mathrm{totalFees}(\mathit{height}, \mathrm{updateCoins}(u, tx, \mathit{height}), \mathit{rest})$.

**`applySpec`** — for $S$ and $b$: if $\mathrm{headerHash}(b.\mathit{header}) = $ `genesisHash` then $(S.\mathit{headers} \mathbin{+\!\!+} [b.\mathit{header}],\ S.\mathit{utxo})$, else $(S.\mathit{headers} \mathbin{+\!\!+} [b.\mathit{header}],\ \mathrm{applyTxs}(S.\mathrm{nextHeight}, S.\mathit{utxo}, b.\mathit{vtx}))$.

**`HeaderSpec`** — for $S$, header $h$ and integer $\mathit{now}$, with $c = h.\mathit{bits} \bmod 2^{32}$ as a 32-bit word, the conjunction of: (`compactNegative`$(c)$ is false, i.e. not (mantissa $c \mathbin{\&} \mathtt{0x7fffff} \ne 0$ and bit $\mathtt{0x800000}$ set); `compactOverflow`$(c)$ is false; $0 < \mathrm{specTarget}(c)$; $\mathrm{specTarget}(c) \le 2^{224} - 1$; $\mathrm{hashValue}(h) \le \mathrm{specTarget}(c)$), where $\mathrm{specTarget}(c) = \lfloor m / 256^{3-e} \rfloor$ if $e \le 3$ and $m \cdot 256^{e-3}$ otherwise, with $e = c \gg 24$ and $m = c \mathbin{\&} \mathtt{0x7fffff}$ (exact arithmetic, no $2^{256}$ truncation); and $h.\mathit{prevBlock} = S.\mathrm{tipHash}$; and $c = S.\mathrm{requiredBits}$; and $S.\mathit{mtp} < h.\mathit{time}$; and $h.\mathit{time} \le \mathit{now} + 7200$; and $\lnot\big((h.\mathit{version} < 2 \land 227931 \le S.\mathrm{tipHeight}+1) \lor (h.\mathit{version} < 3 \land 363725 \le S.\mathrm{tipHeight}+1) \lor (h.\mathit{version} < 4 \land 388381 \le S.\mathrm{tipHeight}+1)\big)$.

**`BlockSpec`** — for a block $b$: $b.\mathit{vtx} \ne [\,]$; $(\mathrm{blockMerkleRoot}\,b).1 = b.\mathit{header}.\mathit{merkleRoot}$; $(\mathrm{blockMerkleRoot}\,b).2 = \mathrm{false}$; $4\cdot|b.\mathit{vtx}| \le 4\,000\,000$; $4\cdot|\mathrm{serBlock}(\mathrm{false}, b)| \le 4\,000\,000$; every transaction among the first one (i.e. the first, if any) is a coinbase; every transaction after the first is not a coinbase; every transaction satisfies `TxSpec`; $4\cdot\sum \mathrm{legacySigOpCount} \le 80\,000$.

**`ContextSpec`** — for $S$ and $b$, with $\mathit{height}$ and $\mathit{cutoff}$ as in `contextualCheckBlock`: every $tx \in b.\mathit{vtx}$ has $\mathrm{isFinalTx}(tx, \mathit{height}, \mathit{cutoff}) = \mathrm{true}$; if BIP34 is active after the tip then for every $cb$ among the first transaction and every $i$ among the first input of $cb$, $\mathrm{heightScript}(\mathit{height})$ is a prefix of $i.\mathit{scriptSig}$ (vacuous when there is no transaction or no input); $\mathrm{checkWitnessMalleation}(b, \text{SegWit active after tip}) = \mathrm{true}$; $\mathrm{blockWeight}(b) \le 4\,000\,000$.

**`LedgerSpec`** — for $S$ and $b$, with $\mathit{hash}$, $\mathit{height}$ and $\mathit{flags}$ as in `connectBlock`: $\mathit{hash} = $ `genesisHash`, or all of: ($\mathrm{bip30Checked}(S, \mathit{height}, \mathit{hash}) = \mathrm{true} \to \forall tx \in b.\mathit{vtx},\ \forall o < |\mathit{vout}(tx)|,\ \mathrm{getCoin}(S.\mathit{utxo}, (\mathrm{txid}(tx), o)) = \mathrm{none}$); $\mathrm{TxsSpec}(\mathit{flags}, \mathit{height}, S.\mathrm{mtpNat}, \mathrm{lockTimeFlags}(\mathit{height}), S.\mathit{utxo}, 0, 0, b.\mathit{vtx})$; and for every $cb$ among the first transaction, $\mathrm{valueOut}(cb) \le \mathrm{totalFees}(\mathit{height}, S.\mathit{utxo}, b.\mathit{vtx}) + \mathrm{specSubsidy}(\mathit{height})$ where $\mathrm{specSubsidy}(\mathit{height}) = \lfloor 5\cdot 10^{9} / 2^{\lfloor \mathit{height}/210000\rfloor} \rfloor$ (this is the imported declarative subsidy, not `coreSubsidy` used by `connectBlock`; the two agree in value for every height since $5\cdot10^9 < 2^{33}$).

**`Valid`** — $\mathrm{HeaderSpec}(S, b.\mathit{header}, \mathit{now}) \land \mathrm{BlockSpec}(b) \land \mathrm{ContextSpec}(S, b) \land \mathrm{LedgerSpec}(S, b)$.

**`LedgerOk`** — for a ledger $u$: $\mathrm{keysNodup}(u)$ and every entry $e$ has $e.2.\mathit{height} \ne 0$ and $\mathrm{isUnspendable}(e.2.\mathit{out}.\mathit{scriptPubKey}) = \mathrm{false}$. (Not referenced by any later declaration in this file.)

**`WellFormed`** — for a chain state $S$: the first element of $S.\mathit{headers}$ exists and is the genesis header; $\mathrm{keysNodup}(S.\mathit{utxo})$; and every entry $e$ of $S.\mathit{utxo}$ has $1 \le e.2.\mathit{height} \le S.\mathrm{tipHeight}$ and $\mathrm{isUnspendable}(e.2.\mathit{out}.\mathit{scriptPubKey}) = \mathrm{false}$.

**Degenerate and edge cases silently included:** empty header lists (tip defaults to the genesis header, tip height $0$ by truncated subtraction, median time past $0$); empty transaction lists and empty input/output lists (coinbase defaults to the genesis coinbase, first input defaults to an input with empty scriptSig and empty witness, `valueOut` of no outputs is $0$, `inputsLoop`/`checkTxInputs` on no inputs succeed); missing coins read through `accessCoin` as value $-1$ at height $0$; `spendHeight − coin.height` and `tipHeight − 2015` and `height − 1` in BIP68 are truncated natural subtractions; `mtpNat` clamps negative medians to $0$; `bits`, `version`, `nSequence` and `lockTimeFlags` are reduced modulo $2^{32}$ only where a 32-bit word is formed, elsewhere unbounded naturals; `acceptHeader` returns the unchanged state; `connectBlock` short-circuits on the genesis hash regardless of the block's contents; `getCoin` returns the first of possibly several entries with the same key; `applyTxInUndo` searches by hash only when the undo coin's height is $0$; `LedgerOk` is unused.
