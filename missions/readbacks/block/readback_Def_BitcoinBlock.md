# Read-back: `Def_BitcoinBlock.lean` (namespace `BitcoinBlock`)

This file imports the serialization, script, signature, verification, Taproot, activation, header, proof-of-work, subsidy, merkle, BIP68 and UTXO developments. Of these, the UTXO development (`Def_BitcoinUtxo`) is imported but no declaration of this file refers to it; the file defines its own ledger notions. Throughout, "byte list" means a list of 8-bit words; "transaction", "input", "output", "outpoint", "header" and "block" are the serialization development's records: an outpoint is $\langle \mathrm{hash} : \text{byte list}, n \in \mathbb{N}\rangle$; an input has a prevout, a scriptSig (byte list), a sequence $\in \mathbb{N}$ and a witness (list of byte lists); an output has a value $\in \mathbb{Z}$ and a scriptPubKey (byte list); a transaction has a version $\in \mathbb{N}$, inputs, outputs and a lock time $\in \mathbb{N}$; a header has version $\in \mathbb{Z}$, prevBlock and merkleRoot (byte lists), time, bits and nonce $\in \mathbb{N}$; a block is a header with a transaction list. No field is bounded by its type. The "default input" used by several defaults below is $\langle\langle [\,], 0\rangle, [\,], 0, [\,]\rangle$ (empty prevout hash, index $0$, empty scriptSig, sequence $0$, no witness) and the "default output" is $\langle 0, [\,]\rangle$. $M$ denotes $2\,100\,000\,000\,000\,000$.

## Constants

**`MAX_BLOCK_WEIGHT`** is the natural number $4\,000\,000$.

**`MAX_BLOCK_SIGOPS_COST`** is the natural number $80\,000$.

**`WITNESS_SCALE_FACTOR`** is the natural number $4$.

**`LOCKTIME_THRESHOLD`** is the natural number $500\,000\,000$.

**`SEQUENCE_FINAL`** is the natural number $0xffffffff = 4294967295$.

**`MINIMUM_WITNESS_COMMITMENT`** is the natural number $38$.

**`BIP34_IMPLIES_BIP30_LIMIT`** is the natural number $1\,983\,702$.

**`MAX_FUTURE_BLOCK_TIME`** is the integer $2\cdot 60\cdot 60 = 7200$. (A constant of the same name and value exists separately in the header development.)

**`COINBASE_MATURITY`** is the natural number $100$.

**`MAX_MONEY`** is the integer $2\,100\,000\,000\,000\,000 = M$.

**`moneyRange`** $(v \in \mathbb{Z})$ is the Boolean $0 \le v \wedge v \le M$.

**`bip34Hash`** is a fixed 32-byte list beginning $b8\,08\,08\,9c\,75\,6a\,dd\,15$ and ending with six zero bytes (the BIP34 block hash in internal byte order).

**`bip16ExceptionHash`** is a fixed 32-byte list beginning $22\,9c\,4f\,ac\,88\,ba\,b1\,94$ and ending with six zero bytes.

**`taprootExceptionHash`** is a fixed 32-byte list beginning $ad\,95\,e3\,a1\,5e\,e5\,ff\,d5$ and ending with nine zero bytes.

**`bip30Repeat91842`** is a fixed 32-byte list beginning $ec\,ca\,e0\,00\,e3\,c8\,e4\,e0$ and ending with five zero bytes.

**`bip30Repeat91880`** is a fixed 32-byte list beginning $21\,d7\,7c\,cb\,4c\,08\,38\,6a$ and ending with five zero bytes.

**`bip30Unspendable91722`** is a fixed 32-byte list beginning $8e\,d0\,4d\,57\,f2\,f3\,cd\,c6$ and ending with five zero bytes.

**`bip30Unspendable91812`** is a fixed 32-byte list beginning $2f\,6f\,30\,f9\,d6\,83\,de\,b8$ and ending with five zero bytes.

**`isBIP30Repeat`** $(\mathit{height} \in \mathbb{N}, \mathit{hash})$ is the Boolean $(\mathit{height} = 91842 \wedge \mathit{hash} = \mathrm{bip30Repeat91842}) \vee (\mathit{height} = 91880 \wedge \mathit{hash} = \mathrm{bip30Repeat91880})$, with byte-list equality.

**`isBIP30Unspendable`** $(\mathit{height}, \mathit{hash})$ is the Boolean $(\mathit{height} = 91722 \wedge \mathit{hash} = \mathrm{bip30Unspendable91722}) \vee (\mathit{height} = 91812 \wedge \mathit{hash} = \mathrm{bip30Unspendable91812})$.

**`scriptException`** $(\mathit{hash})$ returns the activation development's exception tag: `bip16Block` if $\mathit{hash} = \mathrm{bip16ExceptionHash}$, else `taprootBlock` if $\mathit{hash} = \mathrm{taprootExceptionHash}$, else `none`. (Downstream, `bip16Block` yields no script flags at all as base, `taprootBlock` yields P2SH and witness only, `none` yields P2SH, witness and Taproot.)

## Transactions

**`outPointNull`** $(o)$ is the Boolean: $o.\mathrm{hash}$ equals the list of $32$ zero bytes and $o.n = 4294967295$.

**`isCoinBase`** $(tx)$ is true iff $tx.\mathrm{vin}$ is a list of exactly one input and that input's prevout is null in the above sense; for zero or two-or-more inputs it is false.

**`isUnspendable`** $(s : \text{byte list})$ is the Boolean: ($|s| > 0$ and the byte at index $0$ (default $0$) equals `OP_RETURN` $= 0x6a$) or $|s| > 10\,000$ (`MAX_SCRIPT_SIZE` from the verification development).

**`sumValues`** maps a list of outputs to the integer sum of their values ($0$ for the empty list), computed by prepending: $\mathrm{sumValues}(o :: r) = o.\mathrm{nValue} + \mathrm{sumValues}(r)$.

**`valueOut`** $(tx) = \mathrm{sumValues}(tx.\mathrm{vout})$.

**`outputsLoop`** $(\text{outputs}, \mathit{acc} \in \mathbb{Z})$ returns an optional integer: on the empty list, $\mathrm{some}\,\mathit{acc}$; on $o :: r$: none if $o.\mathrm{nValue} < 0$; else none if $M < o.\mathrm{nValue}$; else none if $\mathit{acc} + o.\mathrm{nValue} \notin [0, M]$; else recurse on $r$ with $\mathit{acc} + o.\mathrm{nValue}$.

**`checkTransaction`** $(tx)$ is the Boolean conjunction, in order: $tx.\mathrm{vin}$ non-empty; $tx.\mathrm{vout}$ non-empty; $4\cdot|\mathrm{serTx}(\mathrm{false},tx)| \le 4\,000\,000$ (witness-free serialization length); $\mathrm{outputsLoop}(tx.\mathrm{vout}, 0)$ is some value; the list of prevouts of $tx.\mathrm{vin}$ has no duplicates; and, if $\mathrm{isCoinBase}(tx)$, then the scriptSig length $\ell$ of the head of $tx.\mathrm{vin}$ (default input if empty) satisfies $2 \le \ell \wedge \ell \le 100$, otherwise every input of $tx$ has a non-null prevout.

**`isFinalTx`** $(tx, \mathit{height} \in \mathbb{N}, \mathit{blockTime} \in \mathbb{Z})$: true if $tx.\mathrm{nLockTime} = 0$; otherwise let the threshold be $\mathit{height}$ (as an integer) if $tx.\mathrm{nLockTime} < 500\,000\,000$ and $\mathit{blockTime}$ otherwise; true if $tx.\mathrm{nLockTime} <$ threshold; otherwise true iff every input of $tx$ has $\mathrm{nSequence} = 4294967295$ (vacuously true with no inputs).

## Signature-operation counting

**`sigOpCountAux`** $(\mathit{accurate} : \text{Bool})$ takes $(\mathit{fuel} \in \mathbb{N}, s : \text{byte list}, \mathit{last} \in \mathbb{N}, n \in \mathbb{N})$ and returns a natural number: if $s$ is empty, $n$; else if $\mathit{fuel} = 0$, $n$; otherwise parse one instruction from $s$ with the signature development's `getOp` (a byte $\le 0x4e$ is a push of the indicated data, with the PUSHDATA1/2/4 length forms; a byte $> 0x4e$ is an opcode; a truncated push yields a parse failure): on failure, $n$; on a push with remainder $r$, recurse with $\mathit{fuel}-1$, $r$, $\mathit{last} := 0$ and $n$ unchanged; on an opcode $c$ with remainder $r$: $n' = n+1$ if $c$ is `OP_CHECKSIG` ($0xac$) or `OP_CHECKSIGVERIFY` ($0xad$); $n' = n + (\mathit{last} - 0x50)$ if $c$ is `OP_CHECKMULTISIG` ($0xae$) or `OP_CHECKMULTISIGVERIFY` ($0xaf$) and $\mathit{accurate}$ and $0x51 \le \mathit{last} \le 0x60$ (via `decodeOpN`, which maps $0$ to $0$ and $b$ to $b - 0x50$); $n' = n + 20$ for those two opcodes otherwise; $n' = n$ for any other opcode; then recurse with $\mathit{fuel}-1$, $r$, $\mathit{last} := c$ and $n'$.

**`getSigOpCount`** $(\mathit{accurate}, s) = \mathrm{sigOpCountAux}(\mathit{accurate}, |s|, s, 0xff, 0)$: fuel is the byte length, the initial "last opcode" is $0xff$, the initial count $0$.

**`lastPushAux`** $(\mathit{fuel}, s, d)$ returns an optional byte list: if $s$ is empty, $\mathrm{some}\,d$; else if $\mathit{fuel} = 0$, none; else parse one instruction: failure gives none; a push of data $d'$ recurses with $d := d'$; an opcode $c$ gives none if $c > $ `OP_16` $= 0x60$, otherwise recurses with $d := [\,]$.

**`lastPush`** $(s) = \mathrm{lastPushAux}(|s|, s, [\,])$: the data of the last push instruction of a script all of whose instructions are pushes or opcodes $\le 0x60$ (an opcode $\le 0x60$ resets the result to the empty list), or none if some instruction fails to parse or is an opcode above $0x60$; the empty script gives $\mathrm{some}\,[\,]$.

**`p2shSigOpCount`** $(\mathit{scriptPubKey}, \mathit{scriptSig})$: if $\mathit{scriptPubKey}$ is not pay-to-script-hash (exactly $23$ bytes with byte $0 = 0xa9$, byte $1 = 0x14$, byte $22 = 0x87$), then $\mathrm{getSigOpCount}(\mathrm{true}, \mathit{scriptPubKey})$; otherwise $0$ if $\mathrm{lastPush}(\mathit{scriptSig})$ is none, else $\mathrm{getSigOpCount}(\mathrm{true}, d)$ for the last pushed data $d$.

**`witnessSigOps`** $(\mathit{version} \in \mathbb{N}, \mathit{program}, \mathit{witness})$: if $\mathit{version} = 0$: $1$ when $|\mathit{program}| = 20$; $\mathrm{getSigOpCount}(\mathrm{true}, \text{last witness element})$ when $|\mathit{program}| = 32$ and the witness is non-empty (the last element defaults to $[\,]$ if absent, but that branch requires non-emptiness); otherwise $0$. For any other version, $0$.

**`countWitnessSigOps`** $(f, \mathit{scriptSig}, \mathit{scriptPubKey}, \mathit{witness})$: $0$ if $f.\mathrm{witness}$ is false; else if $\mathit{scriptPubKey}$ is a witness program (length in $[4,42]$, first byte $0$ or in $[0x51,0x60]$, second byte equal to the length minus $2$) with version $v$ and program $p$, then $\mathrm{witnessSigOps}(v, p, \mathit{witness})$; else if $\mathit{scriptPubKey}$ is pay-to-script-hash and $\mathit{scriptSig}$ is push-only (every instruction parses and is a push or an opcode $\le 0x60$), then: $0$ if $\mathrm{lastPush}(\mathit{scriptSig})$ is none; else, with the last push $d$, $\mathrm{witnessSigOps}(v,p,\mathit{witness})$ if $d$ is a witness program $(v,p)$ and $0$ otherwise; else $0$.

**`legacySigOpCount`** $(tx)$ is $\sum_{i \in tx.\mathrm{vin}} \mathrm{getSigOpCount}(\mathrm{false}, i.\mathrm{scriptSig}) + \sum_{o \in tx.\mathrm{vout}} \mathrm{getSigOpCount}(\mathrm{false}, o.\mathrm{scriptPubKey})$.

## The ledger

**`Coin`** is a record $\langle \mathrm{out} : \text{output}, \mathrm{height} \in \mathbb{N}, \mathrm{isCoinbase} : \text{Bool}\rangle$ with decidable equality.

**`dummyCoin`** is the coin $\langle\langle -1, [\,]\rangle, 0, \mathrm{false}\rangle$: value $-1$, empty script, height $0$, not coinbase.

**`Ledger`** is an abbreviation for lists of pairs (outpoint, coin). Nothing enforces distinct keys.

**`getCoin`** $(u, \mathit{op})$ scans $u$ from the front and returns $\mathrm{some}\,c$ for the first pair $(k,c)$ with $k = \mathit{op}$, or none.

**`haveCoin`** $(u, \mathit{op})$ is the Boolean "$\mathrm{getCoin}(u,\mathit{op})$ is some".

**`accessCoin`** $(u, \mathit{op})$ is $\mathrm{getCoin}(u, \mathit{op})$ if present, otherwise $\mathrm{dummyCoin}$.

**`spendCoin`** $(u, \mathit{op})$ returns $u$ with **every** pair whose key equals $\mathit{op}$ removed, order otherwise preserved.

**`addCoin`** $(u, \mathit{op}, c)$: if $c.\mathrm{out.scriptPubKey}$ is unspendable (starts with $0x6a$ or exceeds $10\,000$ bytes), $u$ unchanged; otherwise $(\mathit{op}, c)$ prepended to $\mathrm{spendCoin}(u, \mathit{op})$.

**`addCoinsFrom`** $(\mathit{txid}, \mathit{height}, cb)$ takes $(u, i \in \mathbb{N}, \text{outputs})$ and folds: for the empty list, $u$; for $o :: r$, recurse on $r$ with index $i+1$ from $\mathrm{addCoin}(u, \langle\mathit{txid}, i\rangle, \langle o, \mathit{height}, cb\rangle)$.

**`spendInputs`** $(u, \text{inputs})$ folds $\mathrm{spendCoin}$ over the inputs' prevouts in order.

**`updateCoins`** $(u, tx, \mathit{height})$ is $\mathrm{addCoinsFrom}(\mathrm{txid}(tx), \mathit{height}, \mathrm{isCoinBase}(tx))$ applied to (if $\mathrm{isCoinBase}(tx)$ then $u$ else $\mathrm{spendInputs}(u, tx.\mathrm{vin})$), starting index $0$, over $tx.\mathrm{vout}$. Here $\mathrm{txid}(tx)$ is the double-SHA256 of the witness-free serialization.

**`txUndo`** $(u, tx)$ is the list $[\mathrm{accessCoin}(u, i.\mathrm{prevout}) \mid i \in tx.\mathrm{vin}]$ (dummy coins for missing entries).

**`BlockUndo`** abbreviates lists of lists of coins.

**`Equiv`** $(u, v)$ is the proposition $\forall \mathit{op},\ \mathrm{getCoin}(u,\mathit{op}) = \mathrm{getCoin}(v,\mathit{op})$.

**`keysNodup`** $(u)$ is the proposition that the list of first components of $u$ has no duplicates.

## `CheckTxInputs` and the per-transaction checks

**`inputsLoop`** $(u, \mathit{spendHeight})$ takes $(\text{inputs}, \mathit{acc} \in \mathbb{Z})$: on the empty list, $\mathrm{some}\,\mathit{acc}$; on $i :: r$: if $\mathrm{getCoin}(u, i.\mathrm{prevout})$ is none, none; else with coin $c$: none if $c.\mathrm{isCoinbase}$ and $\mathit{spendHeight} - c.\mathrm{height} < 100$ (natural subtraction, so this fires whenever $c.\mathrm{height} + 100 > \mathit{spendHeight}$, including $c.\mathrm{height} > \mathit{spendHeight}$); else let $\mathit{acc}' = \mathit{acc} + c.\mathrm{out.nValue}$; none if $c.\mathrm{out.nValue} \notin [0,M]$ or $\mathit{acc}' \notin [0,M]$; else recurse with $\mathit{acc}'$.

**`checkTxInputs`** $(u, tx, \mathit{spendHeight})$ returns an optional integer fee: none if some input's prevout has no coin in $u$; else none if $\mathrm{inputsLoop}(u, \mathit{spendHeight}, tx.\mathrm{vin}, 0)$ is none; else with $\mathit{valueIn}$ its value: none if $\mathit{valueIn} < \mathrm{valueOut}(tx)$; none if $\mathit{valueIn} - \mathrm{valueOut}(tx) \notin [0,M]$; else $\mathrm{some}(\mathit{valueIn} - \mathrm{valueOut}(tx))$.

**`txSigOpCost`** $(f, u, tx) = 4\cdot\mathrm{legacySigOpCount}(tx) + X$ where $X = 0$ if $\mathrm{isCoinBase}(tx)$, and otherwise $X = \big(4\cdot\sum_{i} \mathrm{p2shSigOpCount}(\mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out.scriptPubKey}, i.\mathrm{scriptSig})$ if $f.\mathrm{p2sh}$, else $0\big) + \sum_i \mathrm{countWitnessSigOps}(f, i.\mathrm{scriptSig}, \mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out.scriptPubKey}, i.\mathrm{witness})$, sums over $i \in tx.\mathrm{vin}$ (missing coins contribute the dummy's empty script).

**`sequenceLocksOk`** $(u, \mathit{height}, \mathit{mtp} : \mathbb{N}\to\mathbb{N}, \mathit{lockTimeFlags} \in \mathbb{N}, tx)$ is the BIP68 core development's `sequenceLocks` applied to version $tx.\mathrm{version} \bmod 2^{32}$, flags $\mathit{lockTimeFlags} \bmod 2^{32}$, context $\langle\mathit{height}, \mathit{mtp}\rangle$ and the input list $[\langle i.\mathrm{nSequence} \bmod 2^{32}, \mathrm{accessCoin}(u,i.\mathrm{prevout}).\mathrm{height}\rangle \mid i \in tx.\mathrm{vin}]$: with BIP68 enabled (version $\ge 2$ and flag bit $0$ set), fold the inputs into integer minima $\mathit{minHeight}, \mathit{minTime}$ starting at $-1$ — an input with bit $31$ set contributes nothing; with bit $22$ set it raises $\mathit{minTime}$ to $\mathit{mtp}(c-1) + 512\cdot(s \bmod 2^{16}) - 1$; otherwise it raises $\mathit{minHeight}$ to $c + (s \bmod 2^{16}) - 1$ — and return $\mathit{minHeight} < \mathit{height} \wedge \mathit{minTime} < \mathit{mtp}(\mathit{height}-1)$; with BIP68 not enabled, the minima stay $-1$ and the result is true.

**`inputScriptsOk`** $(f, u, tx)$: let $\mathit{spent} = [\mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out} \mid i \in tx.\mathrm{vin}]$; for every index $n < |tx.\mathrm{vin}|$, with $i$ the $n$-th input (default input if out of range, which cannot happen) and $c = \mathrm{accessCoin}(u, i.\mathrm{prevout})$, the Taproot development's `verifyScriptFull` holds on $\mathit{spent}$, context $\langle f, tx, n, c.\mathrm{out.nValue}\rangle$, $i.\mathrm{scriptSig}$, $c.\mathrm{out.scriptPubKey}$ and $i.\mathrm{witness}$ — the complete `VerifyScript`: evaluate scriptSig then scriptPubKey on the stack, require a true top, then the native witness-program branch (when $f.\mathrm{witness}$; scriptSig must be empty), the P2SH branch (when $f.\mathrm{p2sh}$; push-only scriptSig, redeem script evaluation, nested witness program requiring the scriptSig to be exactly the canonical push of the redeem script), and the rule that a non-empty witness with no witness program fails; Taproot spends are dispatched to the Taproot handler with the spent-outputs list.

**`LoopState`** is a record $\langle \mathrm{utxo} : \text{Ledger}, \mathrm{fees} \in \mathbb{Z}, \mathrm{sigOps} \in \mathbb{N}, \mathrm{undo} : \text{BlockUndo}\rangle$.

**`connectLoop`** $(f, \mathit{height}, \mathit{mtp}, \mathit{lockTimeFlags})$ takes $(\mathit{st}, \text{transactions})$ and returns an optional loop state: on the empty list, $\mathrm{some}\,\mathit{st}$; on $tx :: r$: compute an optional (fees, undo) "step": if $\mathrm{isCoinBase}(tx)$, $\mathrm{some}(\mathit{st}.\mathrm{fees}, \mathit{st}.\mathrm{undo})$; else none if $\mathrm{checkTxInputs}(\mathit{st}.\mathrm{utxo}, tx, \mathit{height})$ is none, else with fee $\varphi$: none if $\mathit{st}.\mathrm{fees} + \varphi \notin [0, M]$; none if $\mathrm{sequenceLocksOk}(\mathit{st}.\mathrm{utxo}, \mathit{height}, \mathit{mtp}, \mathit{lockTimeFlags}, tx)$ is false; else $\mathrm{some}(\mathit{st}.\mathrm{fees} + \varphi,\ \mathit{st}.\mathrm{undo} \mathbin{+\!\!+} [\mathrm{txUndo}(\mathit{st}.\mathrm{utxo}, tx)])$. If the step is none, none. Otherwise let $\sigma = \mathit{st}.\mathrm{sigOps} + \mathrm{txSigOpCost}(f, \mathit{st}.\mathrm{utxo}, tx)$: none if $80\,000 < \sigma$; none if $tx$ is not a coinbase and $\mathrm{inputScriptsOk}(f, \mathit{st}.\mathrm{utxo}, tx)$ is false; else recurse on $r$ from $\langle \mathrm{updateCoins}(\mathit{st}.\mathrm{utxo}, tx, \mathit{height}), \text{fees}, \sigma, \text{undo}\rangle$. The coinbase test is positional-agnostic: any coinbase-shaped transaction anywhere skips the input checks and the undo record.

## Chain state

**`ChainState`** is a record $\langle \mathrm{headers} : \text{list of headers}, \mathrm{utxo} : \text{Ledger}\rangle$.

**`initialState`** is $\langle [\mathrm{genesisHeader}], [\,]\rangle$: the mainnet genesis header alone and an empty ledger (the genesis coinbase output is not present).

**`ChainState.tipHeight`** $(S) = |S.\mathrm{headers}| - 1$ with natural subtraction ($0$ for an empty list).

**`ChainState.tip`** $(S)$ is the last header of $S.\mathrm{headers}$, or $\mathrm{genesisHeader}$ if the list is empty.

**`ChainState.tipHash`** $(S) = \mathrm{headerHash}(\mathrm{tip}(S))$, the double-SHA256 of the 80-byte serialization (version as 4 little-endian bytes modulo $2^{32}$, prevBlock bytes, merkleRoot bytes, time, bits, nonce each as 4 little-endian bytes modulo $2^{32}$).

**`ChainState.nextHeight`** $(S) = |S.\mathrm{headers}|$.

**`ChainState.timesTo`** $(S, h)$ is the list of the times (cast to $\mathbb{Z}$) of the first $h+1$ headers of $S$, reversed (so most recent first); fewer if the list is shorter.

**`ChainState.mtpAt`** $(S, h)$ is the header development's `medianTimePast` of $\mathrm{timesTo}(S,h)$: take the first $11$ elements, sort ascending, return the element at index $\lfloor \text{window length}/2\rfloor$, with default $0$ for an empty window.

**`ChainState.mtp`** $(S) = \mathrm{mtpAt}(S, \mathrm{tipHeight}(S))$.

**`ChainState.mtpNat`** $(S, h) = \max(0, \mathrm{mtpAt}(S,h))$ as a natural number (negative medians become $0$).

**`ChainState.requiredBits`** $(S)$: let $\mathit{first}$ be the header at index $\mathrm{tipHeight}(S) - (2016 - 1)$ (natural subtraction; $2016 = \lfloor 14\cdot24\cdot60\cdot60 / 600\rfloor$), defaulting to $\mathrm{genesisHeader}$ when out of range; the result is the proof-of-work development's `nextWorkRequired` with last height $\mathrm{tipHeight}(S)$, last bits $\mathrm{tip}(S).\mathrm{bits} \bmod 2^{32}$, last time $\mathrm{tip}(S).\mathrm{time}$ and first time $\mathit{first}.\mathrm{time}$ (both cast to $\mathbb{Z}$): the last bits unchanged if $(\mathrm{tipHeight}+1) \bmod 2016 \ne 0$, otherwise the retarget (decode the last target, multiply by the actual timespan clamped to $[\text{timespan}/4, 4\cdot\text{timespan}]$ modulo $2^{256}$, divide by $1\,209\,600$, cap at $2^{224}-1$, re-encode as a compact word).

**`blockProof`** $(\mathit{bits} \in \mathbb{N})$: with `deriveTarget` of $\mathit{bits} \bmod 2^{32}$ — none if the compact word is negative, decodes to $0$, overflows, or exceeds $2^{224}-1$ — the result is $0$ on none, and $\lfloor (2^{256} - 1 - t)/(t+1)\rfloor + 1$ on $\mathrm{some}\,t$ (natural subtraction and floor division).

**`ChainState.chainWork`** $(S) = \sum_{h \in S.\mathrm{headers}} \mathrm{blockProof}(h.\mathrm{bits})$.

**`hashValue`** $(h)$ is the little-endian numeric value of $\mathrm{headerHash}(h)$ (byte $k$ weighted by $256^k$).

## `CheckBlock`

**`merkleCombine`** $(a, b) = \mathrm{hash256}(a \mathbin{+\!\!+} b)$, double-SHA256 of the concatenation.

**`zeroHash`** is the list of $32$ zero bytes.

**`blockMerkleRoot`** $(b)$ is the merkle development's `computeMerkleRoot` with combiner $\mathrm{merkleCombine}$ and empty-root $\mathrm{zeroHash}$ on $[\mathrm{txid}(tx) \mid tx \in b.\mathrm{vtx}]$: a pair (root, mutated). The loop: while more than one hash remains, set mutated if some aligned pair (positions $2k$, $2k+1$, both present) is equal, then replace the level by the combiner applied to aligned pairs, the odd last element combined with itself; the root is the remaining element, or $\mathrm{zeroHash}$ for an empty list; mutated starts false.

**`blockWitnessMerkleRoot`** $(b)$ is the root component of the same computation on $\mathrm{zeroHash} :: [\mathrm{wtxid}(tx) \mid tx \in \mathrm{drop}_1(b.\mathrm{vtx})]$, where $\mathrm{wtxid}$ is the double-SHA256 of the witness serialization when the transaction has a witness, else the txid.

**`checkHeaderPow`** $(h)$ is the proof-of-work development's `checkProofOfWork` on $\mathrm{hashValue}(h)$ and $h.\mathrm{bits} \bmod 2^{32}$: false if `deriveTarget` is none, else $\mathrm{hashValue}(h) \le t$.

**`checkBlock`** $(b)$ is the Boolean conjunction, in order: $\mathrm{checkHeaderPow}(b.\mathrm{header})$; $(\mathrm{blockMerkleRoot}\,b).1 = b.\mathrm{header.merkleRoot}$; $\neg(\mathrm{blockMerkleRoot}\,b).2$; $b.\mathrm{vtx}$ non-empty; $4\cdot|b.\mathrm{vtx}| \le 4\,000\,000$; $4\cdot|\mathrm{serBlock}(\mathrm{false}, b)| \le 4\,000\,000$; $\mathrm{isCoinBase}$ of the head of $b.\mathrm{vtx}$ (default $\mathrm{genesisCoinbase}$); every element of $\mathrm{drop}_1(b.\mathrm{vtx})$ is not a coinbase; every element of $b.\mathrm{vtx}$ passes $\mathrm{checkTransaction}$; $4\cdot\sum_{tx\in b.\mathrm{vtx}}\mathrm{legacySigOpCount}(tx) \le 80\,000$.

## `ContextualCheckBlock`

**`heightScript`** $(n \in \mathbb{N})$: $[0]$ if $n = 0$; $[0x50 + n]$ (one byte) if $1 \le n \le 16$; otherwise the signature development's canonical push (`pushBytes`: a length byte for data shorter than $0x4c$ bytes, else a PUSHDATA1/2/4 prefix) of the script development's `serialize` of $n$ (the little-endian magnitude bytes with a $0x00$ sign byte appended when the top bit of the last byte is set).

**`isCommitmentOutput`** $(o)$ is the Boolean $38 \le |o.\mathrm{scriptPubKey}|$ and the first six bytes of $o.\mathrm{scriptPubKey}$ are $6a\,24\,aa\,21\,a9\,ed$.

**`witnessCommitmentIndex`** $(b)$: none if $b.\mathrm{vtx}$ is empty; otherwise, with $cb$ the first transaction, the **last** index $i < |cb.\mathrm{vout}|$ such that the $i$-th output (default output if out of range) satisfies $\mathrm{isCommitmentOutput}$, or none if there is no such index.

**`checkWitnessMalleation`** $(b, \mathit{expect} : \text{Bool})$: let $\mathit{noWitness}$ be "every transaction of $b$ has no input with a non-empty witness". If $\mathit{expect}$ is false, return $\mathit{noWitness}$. If true: if $\mathrm{witnessCommitmentIndex}(b)$ is none, return $\mathit{noWitness}$; else with position $p$, let $cb$ be the head of $b.\mathrm{vtx}$ (default $\mathrm{genesisCoinbase}$) and $\mathit{stack}$ the witness of the head of $cb.\mathrm{vin}$ (default input): if $\mathit{stack}$ is exactly $[\mathit{nonce}]$, return $|\mathit{nonce}| = 32$ and $\mathrm{hash256}(\mathrm{blockWitnessMerkleRoot}(b) \mathbin{+\!\!+} \mathit{nonce})$ equals the $32$ bytes of the $p$-th output's scriptPubKey (default output) after dropping $6$ bytes; for a stack of any other length (including empty), return false.

**`contextualCheckBlock`** $(S, b)$: let $\mathit{height} = \mathrm{nextHeight}(S)$ and $\mathit{cutoff} = \mathrm{mtp}(S)$ if the activation development's `activeAfter`$(\mathrm{tipHeight}(S), \mathrm{csv})$ (i.e. $419328 \le \mathrm{tipHeight}(S)+1$) else $b.\mathrm{header.time}$ as an integer. The Boolean conjunction of: every transaction satisfies $\mathrm{isFinalTx}(tx, \mathit{height}, \mathit{cutoff})$; not `activeAfter`$(\mathrm{tipHeight}(S), \mathrm{heightInCB})$ ($227931 \le \mathrm{tipHeight}+1$) or $\mathrm{heightScript}(\mathit{height})$ is a prefix of the scriptSig of the head input (default input) of the head transaction (default $\mathrm{genesisCoinbase}$); $\mathrm{checkWitnessMalleation}(b, \text{`activeAfter`}(\mathrm{tipHeight}(S), \mathrm{segwit}))$ ($481824 \le \mathrm{tipHeight}+1$); and $\mathrm{blockWeight}(b) \le 4\,000\,000$ where $\mathrm{blockWeight}(b) = 3\cdot|\mathrm{serBlock}(\mathrm{false},b)| + |\mathrm{serBlock}(\mathrm{true},b)|$.

## `ConnectBlock`

**`bip30Checked`** $(S, \mathit{height}, \mathit{hash})$: let $\mathit{bip34Ancestor}$ be: if $S.\mathrm{headers}$ has an element $h$ at index $227931$ then $\mathrm{headerHash}(h) = \mathrm{bip34Hash}$ else false. Result: $(\neg\,\mathrm{isBIP30Repeat}(\mathit{height},\mathit{hash}) \wedge \neg\,\mathit{bip34Ancestor}) \vee 1983702 \le \mathit{height}$.

**`bip30Ok`** $(u, b)$: for every transaction $tx$ of $b$ and every index $o < |tx.\mathrm{vout}|$, $\langle\mathrm{txid}(tx), o\rangle$ is not a key of $u$ (all outputs counted, including unspendable ones).

**`connectBlock`** $(S, b)$ returns an optional (ledger, undo): let $\mathit{hash} = \mathrm{headerHash}(b.\mathrm{header})$ and $\mathit{height} = \mathrm{nextHeight}(S)$. If $\mathit{hash} = \mathrm{genesisHash}$ (the fixed 32-byte constant beginning $6f\,e2\,8c\,0a$), return $\mathrm{some}(S.\mathrm{utxo}, [\,])$ without any further check. Else if $\mathrm{bip30Checked}(S,\mathit{height},\mathit{hash})$ and not $\mathrm{bip30Ok}(S.\mathrm{utxo}, b)$, none. Else let $\mathit{flags}$ be the activation development's `blockScriptFlags`$(\mathit{height}, \mathrm{scriptException}(\mathit{hash}))$ (base per the exception, then DERSIG when $\mathit{height}\ge 363725$, CLTV when $\ge 388381$, CSV when $\ge 419328$, NULLDUMMY when $\ge 481824$), and run $\mathrm{connectLoop}(\mathit{flags}, \mathit{height}, \mathrm{mtpNat}(S), \text{`lockTimeFlags`}(\mathit{height}), \langle S.\mathrm{utxo}, 0, 0, [\,]\rangle, b.\mathrm{vtx})$ where `lockTimeFlags` is $1$ if $\mathit{height} \ge 419328$ else $0$: none on failure; else with final state $\mathit{st}$: none if $\mathrm{valueOut}(\text{head of } b.\mathrm{vtx}, \text{default } \mathrm{genesisCoinbase}) > \mathit{st}.\mathrm{fees} + \mathrm{coreSubsidy}(\mathit{height})$, where $\mathrm{coreSubsidy}(h) = 0$ if $\lfloor h/210000\rfloor \ge 64$ and $5\,000\,000\,000 \gg \lfloor h/210000\rfloor$ otherwise; else $\mathrm{some}(\mathit{st}.\mathrm{utxo}, \mathit{st}.\mathrm{undo})$.

## The complete validation path

**`Outcome`** is an inductive type with four constructors: `accept` carrying a chain state $S'$ and a block undo; `invalid`; `futureTime`; `missingPrev`.

**`acceptHeader`** $(S, h, \mathit{now} \in \mathbb{Z})$: `invalid` if $\neg\,\mathrm{checkHeaderPow}(h)$; else `missingPrev` if $h.\mathrm{prevBlock} \ne \mathrm{tipHash}(S)$; else `invalid` if $h.\mathrm{bits} \bmod 2^{32} \ne \mathrm{requiredBits}(S)$; else `invalid` if $h.\mathrm{time} \le \mathrm{mtp}(S)$; else `futureTime` if $\mathit{now} + 7200 < h.\mathrm{time}$; else `invalid` if the header development's `versionOutdated`$(h.\mathrm{version}, \mathrm{tipHeight}(S))$ ($h.\mathrm{version} < 2$ and $227931 \le \mathrm{tipHeight}+1$, or $<3$ and $363725 \le \mathrm{tipHeight}+1$, or $<4$ and $388381 \le \mathrm{tipHeight}+1$); else `accept` $S$ $[\,]$ (the unchanged state and the empty undo).

**`validate`** $(S, b, \mathit{now})$: match $\mathrm{acceptHeader}(S, b.\mathrm{header}, \mathit{now})$: on `accept` (payload ignored): `invalid` if $\neg\,\mathrm{checkBlock}(b)$; else `invalid` if $\neg\,\mathrm{contextualCheckBlock}(S,b)$; else on $\mathrm{connectBlock}(S,b)$: `invalid` if none, and `accept` $\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], u\rangle$ $\mathit{undo}$ if $\mathrm{some}(u, \mathit{undo})$; on any other header outcome, that outcome.

**`accepts`** $(S, b, \mathit{now})$ is the proposition $\exists S'\,\exists\mathit{undo},\ \mathrm{validate}(S,b,\mathit{now}) = \text{`accept`}\ S'\ \mathit{undo}$.

**`Reachable`** is the inductive predicate on chain states generated by: `genesis`: $\mathrm{Reachable}(\mathrm{initialState})$; `step`: for implicit $S, b, \mathit{now}, S', \mathit{undo}$, from $\mathrm{Reachable}(S)$ and $\mathrm{validate}(S,b,\mathit{now}) = \text{`accept`}\ S'\ \mathit{undo}$ conclude $\mathrm{Reachable}(S')$.

## `DisconnectBlock`

**`applyTxInUndo`** $(u, \mathit{undo} : \text{Coin}, \mathit{out} : \text{outpoint})$ returns an optional (ledger, Bool): let $\mathit{clean} = \neg\,\mathrm{haveCoin}(u, \mathit{out})$. If $\mathit{undo}.\mathrm{height} = 0$: search $u$ for the first entry whose key **hash** equals $\mathit{out}.\mathrm{hash}$ (index ignored); if found with coin $\mathit{alt}$, the coin to restore is $\mathit{undo}$ with height and coinbase flag replaced by $\mathit{alt}$'s; if not found, return none. If $\mathit{undo}.\mathrm{height} \ne 0$, the coin to restore is $\mathit{undo}$ itself. Return $\mathrm{some}(\mathrm{addCoin}(u, \mathit{out}, c), \mathit{clean})$ (so an unspendable coin is silently not added).

**`restoreInputs`** $(u, \text{list of (input, coin) pairs})$: on the empty list, $\mathrm{some}(u, \mathrm{true})$; on $(i,c) :: r$: first $\mathrm{restoreInputs}(u, r)$ (so the tail, i.e. later inputs, is restored first); none propagates; then $\mathrm{applyTxInUndo}(u', c, i.\mathrm{prevout})$; none propagates; result is the new ledger with the conjunction of the two clean flags.

**`spendOutputs`** $(u, \mathit{txid}, \mathit{height}, cb, \mathit{exception})$ takes $(\text{outputs}, i \in \mathbb{N})$ and returns a (ledger, Bool) pair — never none: on the empty list, $(u, \mathrm{true})$; on $o :: r$: if $o.\mathrm{scriptPubKey}$ is unspendable, $(u, \mathrm{true})$ for this output; otherwise with $\mathit{op} = \langle\mathit{txid}, i\rangle$, let $\mathit{ok}$ be false if $\mathit{op}$ is not a key of $u$ and otherwise "the stored coin equals $\langle o, \mathit{height}, cb\rangle$ componentwise"; this output yields $(\mathrm{spendCoin}(u,\mathit{op}), \mathit{ok} \vee \mathit{exception})$; then recurse on $r$ with $i+1$ from that ledger and and the flags.

**`disconnectTx`** $(u, \mathit{height}, \mathit{exception}, tx, \mathit{undo} : \text{optional list of coins})$: let $cb = \mathrm{isCoinBase}(tx)$ and $(u', \mathit{clean}) = \mathrm{spendOutputs}(u, \mathrm{txid}(tx), \mathit{height}, cb, cb \wedge \mathit{exception}, tx.\mathrm{vout}, 0)$. If $\mathit{undo}$ is none, $\mathrm{some}(u', \mathit{clean})$. If $\mathrm{some}\,\mathit{coins}$: none if $|\mathit{coins}| \ne |tx.\mathrm{vin}|$; else $\mathrm{restoreInputs}(u', \mathrm{zip}(tx.\mathrm{vin}, \mathit{coins}))$, none propagating, with the clean flags and-ed.

**`disconnectTxs`** $(\mathit{height}, \mathit{exception})$ takes $(u, \text{list of (transaction, optional coins)})$: on the empty list, $\mathrm{some}(u, \mathrm{true})$; else apply $\mathrm{disconnectTx}$ to the head, none propagating, then recurse on the tail from the resulting ledger, none propagating, and-ing the flags.

**`disconnectBlock`** $(u, \mathit{height}, \mathit{hash}, b, \mathit{undo} : \text{BlockUndo})$: none if $|\mathit{undo}| + 1 \ne |b.\mathrm{vtx}|$; otherwise $\mathrm{disconnectTxs}(\mathit{height}, \mathrm{isBIP30Unspendable}(\mathit{height}, \mathit{hash}), u, L)$ where $L$ is the reverse of $\mathrm{zip}(b.\mathrm{vtx}, \mathrm{none} :: [\mathrm{some}\,c \mid c \in \mathit{undo}])$: the first transaction is paired with no undo record, the $(k+1)$-th with the $k$-th undo entry, and the pairs are processed last-to-first.

## The declarative specification and `ApplySpec`

**`TxSpec`** $(tx)$ is the proposition: $tx.\mathrm{vin} \ne [\,]$; $tx.\mathrm{vout} \ne [\,]$; $4\cdot|\mathrm{serTx}(\mathrm{false},tx)| \le 4\,000\,000$; every output value $v$ has $0 \le v \le M$; $\mathrm{valueOut}(tx) \le M$; prevouts pairwise distinct; $\mathrm{isCoinBase}(tx) = \mathrm{true} \Rightarrow$ every input's scriptSig length lies in $[2,100]$; $\mathrm{isCoinBase}(tx) = \mathrm{false} \Rightarrow$ every input has $\mathrm{outPointNull} = \mathrm{false}$.

**`valueIn`** $(u, \text{inputs})$ is $\sum_i \mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out.nValue}$ over $\mathbb{Z}$, computed by prepending; a missing coin contributes $-1$.

**`feeOf`** $(u, tx) = \mathrm{valueIn}(u, tx.\mathrm{vin}) - \mathrm{valueOut}(tx)$.

**`TxInputsSpec`** $(f, u, \mathit{height}, \mathit{mtp}, \mathit{lockTimeFlags}, tx)$ is the conjunction: for every input $i$ there is a coin $c$ with $\mathrm{getCoin}(u, i.\mathrm{prevout}) = \mathrm{some}\,c$, $(c.\mathrm{isCoinbase} = \mathrm{true} \Rightarrow c.\mathrm{height} + 100 \le \mathit{height})$, $0 \le c.\mathrm{out.nValue}$ and $c.\mathrm{out.nValue} \le M$; $\mathrm{valueIn}(u, tx.\mathrm{vin}) \le M$; $\mathrm{valueOut}(tx) \le \mathrm{valueIn}(u, tx.\mathrm{vin})$; the BIP68 model's `satisfiesBIP68` on version $tx.\mathrm{version} \bmod 2^{32}$, flags $\mathit{lockTimeFlags} \bmod 2^{32}$, context $\langle\mathit{height},\mathit{mtp}\rangle$ and inputs $\langle i.\mathrm{nSequence} \bmod 2^{32}, \mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{height}\rangle$ (BIP68 not enabled, or every input disabled (bit 31) or satisfying $\mathit{mtp}(c-1) + 512\cdot(s \bmod 2^{16}) \le \mathit{mtp}(\mathit{height}-1)$ when bit 22 is set and $c + (s \bmod 2^{16}) \le \mathit{height}$ otherwise); and for every $n < |tx.\mathrm{vin}|$, with $i$ the $n$-th input (default input) and $c = \mathrm{accessCoin}(u, i.\mathrm{prevout})$, `verifyScriptFull` on the spent list $[\mathrm{accessCoin}(u, j.\mathrm{prevout}).\mathrm{out} \mid j \in tx.\mathrm{vin}]$, context $\langle f, tx, n, c.\mathrm{out.nValue}\rangle$, $i.\mathrm{scriptSig}$, $c.\mathrm{out.scriptPubKey}$, $i.\mathrm{witness}$ equals true.

**`TxsSpec`** $(f, \mathit{height}, \mathit{mtp}, \mathit{lockTimeFlags})$ on $(u, \mathit{fees} \in \mathbb{Z}, \mathit{sigOps} \in \mathbb{N}, \text{transactions})$: true for the empty list; for $tx :: r$: $(\mathrm{isCoinBase}(tx) = \mathrm{false} \Rightarrow \mathrm{TxInputsSpec}(f,u,\mathit{height},\mathit{mtp},\mathit{lockTimeFlags},tx) \wedge \mathit{fees} + \mathrm{feeOf}(u,tx) \le M)$, and $\mathit{sigOps} + \mathrm{txSigOpCost}(f,u,tx) \le 80\,000$, and $\mathrm{TxsSpec}$ on $r$ from $\mathrm{updateCoins}(u,tx,\mathit{height})$, fees $\mathit{fees}$ if coinbase else $\mathit{fees} + \mathrm{feeOf}(u,tx)$, and sigops $\mathit{sigOps} + \mathrm{txSigOpCost}(f,u,tx)$. No lower bound on the fee total is stated.

**`applyTxs`** $(\mathit{height})$ on $(u, \text{transactions})$: the left fold of $\mathrm{updateCoins}(\cdot, tx, \mathit{height})$ over the list.

**`totalFees`** $(\mathit{height})$ on $(u, \text{transactions})$: $0$ for the empty list; for $tx :: r$, ($0$ if $\mathrm{isCoinBase}(tx)$ else $\mathrm{feeOf}(u,tx)$) plus $\mathrm{totalFees}$ on $r$ from $\mathrm{updateCoins}(u,tx,\mathit{height})$.

**`applySpec`** $(S, b)$: if $\mathrm{headerHash}(b.\mathrm{header}) = \mathrm{genesisHash}$ then $\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], S.\mathrm{utxo}\rangle$, else $\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], \mathrm{applyTxs}(\mathrm{nextHeight}(S), S.\mathrm{utxo}, b.\mathrm{vtx})\rangle$.

**`HeaderSpec`** $(S, h, \mathit{now})$ is the conjunction: [the proof-of-work development's `compactNegative` of $h.\mathrm{bits} \bmod 2^{32}$ is false, `compactOverflow` is false, $0 < \text{`specTarget`}$, `specTarget` $\le 2^{224}-1$, and $\mathrm{hashValue}(h) \le$ `specTarget`], where `specTarget` is the exact value mantissa $\cdot 256^{\text{exponent}-3}$ (floor-divided when the exponent is $\le 3$) with no $2^{256}$ truncation; $h.\mathrm{prevBlock} = \mathrm{tipHash}(S)$; $h.\mathrm{bits} \bmod 2^{32} = \mathrm{requiredBits}(S)$; $\mathrm{mtp}(S) < h.\mathrm{time}$ and $h.\mathrm{time} \le \mathit{now} + 7200$; and $\neg\big((h.\mathrm{version} < 2 \wedge 227931 \le \mathrm{tipHeight}(S)+1) \vee (h.\mathrm{version} < 3 \wedge 363725 \le \mathrm{tipHeight}(S)+1) \vee (h.\mathrm{version} < 4 \wedge 388381 \le \mathrm{tipHeight}(S)+1)\big)$.

**`BlockSpec`** $(b)$ is the conjunction: $b.\mathrm{vtx} \ne [\,]$; $(\mathrm{blockMerkleRoot}\,b).1 = b.\mathrm{header.merkleRoot}$ and $(\mathrm{blockMerkleRoot}\,b).2 = \mathrm{false}$; $4\cdot|b.\mathrm{vtx}| \le 4\,000\,000$; $4\cdot|\mathrm{serBlock}(\mathrm{false},b)| \le 4\,000\,000$; every $tx \in \mathrm{take}_1(b.\mathrm{vtx})$ has $\mathrm{isCoinBase} = \mathrm{true}$ and every $tx \in \mathrm{drop}_1(b.\mathrm{vtx})$ has $\mathrm{isCoinBase} = \mathrm{false}$; every $tx \in b.\mathrm{vtx}$ satisfies $\mathrm{TxSpec}$; $4\cdot\sum_{tx}\mathrm{legacySigOpCount}(tx) \le 80\,000$.

**`ContextSpec`** $(S, b)$: with $\mathit{height}$ and $\mathit{cutoff}$ as in $\mathrm{contextualCheckBlock}$: every $tx \in b.\mathrm{vtx}$ has $\mathrm{isFinalTx}(tx,\mathit{height},\mathit{cutoff}) = \mathrm{true}$; `activeAfter`$(\mathrm{tipHeight}(S), \mathrm{heightInCB}) = \mathrm{true} \Rightarrow \forall cb \in \mathrm{take}_1(b.\mathrm{vtx}),\ \forall i \in \mathrm{take}_1(cb.\mathrm{vin}),\ \mathrm{heightScript}(\mathit{height})$ is a prefix of $i.\mathrm{scriptSig}$ (vacuous with no transactions or no inputs); $\mathrm{checkWitnessMalleation}(b, \text{`activeAfter`}(\mathrm{tipHeight}(S), \mathrm{segwit})) = \mathrm{true}$; $\mathrm{blockWeight}(b) \le 4\,000\,000$.

**`LedgerSpec`** $(S, b)$: with $\mathit{hash} = \mathrm{headerHash}(b.\mathrm{header})$, $\mathit{height} = \mathrm{nextHeight}(S)$ and $\mathit{flags} = $ `blockScriptFlags`$(\mathit{height}, \mathrm{scriptException}(\mathit{hash}))$: $\mathit{hash} = \mathrm{genesisHash}$, **or** [$(\mathrm{bip30Checked}(S,\mathit{height},\mathit{hash}) = \mathrm{true} \Rightarrow \forall tx \in b.\mathrm{vtx},\ \forall o < |tx.\mathrm{vout}|,\ \mathrm{getCoin}(S.\mathrm{utxo}, \langle\mathrm{txid}(tx), o\rangle) = \mathrm{none})$ and $\mathrm{TxsSpec}(\mathit{flags}, \mathit{height}, \mathrm{mtpNat}(S), \text{`lockTimeFlags`}(\mathit{height}), S.\mathrm{utxo}, 0, 0, b.\mathrm{vtx})$ and $\forall cb \in \mathrm{take}_1(b.\mathrm{vtx}),\ \mathrm{valueOut}(cb) \le \mathrm{totalFees}(\mathit{height}, S.\mathrm{utxo}, b.\mathrm{vtx}) + \mathrm{specSubsidy}(\mathit{height})$], where $\mathrm{specSubsidy}(h) = \lfloor 5\,000\,000\,000 / 2^{\lfloor h/210000\rfloor}\rfloor$ (the subsidy development's declarative schedule, distinct from `coreSubsidy` used by $\mathrm{connectBlock}$).

**`Valid`** $(S, b, \mathit{now})$ is $\mathrm{HeaderSpec}(S, b.\mathrm{header}, \mathit{now}) \wedge \mathrm{BlockSpec}(b) \wedge \mathrm{ContextSpec}(S,b) \wedge \mathrm{LedgerSpec}(S,b)$.

**`LedgerOk`** $(u)$ is $\mathrm{keysNodup}(u)$ and every entry $e$ of $u$ has $e.2.\mathrm{height} \ne 0$ and $\mathrm{isUnspendable}(e.2.\mathrm{out.scriptPubKey}) = \mathrm{false}$. (Not referenced by any of the nineteen theorem statements.)

**`WellFormed`** $(S)$ is: the head of $S.\mathrm{headers}$ is $\mathrm{some}\,\mathrm{genesisHeader}$; $\mathrm{keysNodup}(S.\mathrm{utxo})$; and every entry $e$ of $S.\mathrm{utxo}$ has $1 \le e.2.\mathrm{height}$, $e.2.\mathrm{height} \le \mathrm{tipHeight}(S)$, and $\mathrm{isUnspendable}(e.2.\mathrm{out.scriptPubKey}) = \mathrm{false}$.

## Edge cases and defaults the file silently includes

Empty header lists ($\mathrm{tipHeight} = 0$, tip and retarget-anchor default to the genesis header, median $0$); empty transaction lists (head defaults to the genesis coinbase in `checkBlock`, `checkWitnessMalleation`, `contextualCheckBlock`, `connectBlock`'s coinbase bound); empty input lists (default input with empty scriptSig and witness); `getD`/`headD`/`getLastD` defaults throughout; natural subtraction in `tipHeight`, the retarget index, coinbase maturity, $\mathit{height}-1$ and $c-1$ in BIP68, and `blockProof`; modulo-$2^{32}$ reductions of bits, version, sequence and flags; `accessCoin`'s dummy coin (value $-1$, height $0$) feeding `valueIn`, `feeOf`, `txUndo`, `txSigOpCost`, `sequenceLocksOk` and `inputScriptsOk` when a prevout is missing; ledgers with duplicate keys (first match wins on lookup, all matches removed on spend); coinbase-shaped transactions in non-first positions treated as coinbases by the loop, `updateCoins` and the specifications; the genesis-hash shortcut in `connectBlock`, `applySpec` and `LedgerSpec`; `fuel`-bounded script scans that stop silently at the byte length.
