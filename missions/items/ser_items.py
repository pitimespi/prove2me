SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: WriteCompactSize/ReadCompactSize and vector serialization, src/serialize.h: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h; "
       "SerializeTransaction/UnserializeTransaction, COutPoint, CTxIn, CTxOut, ComputeHash, ComputeWitnessHash, src/primitives/transaction.h and transaction.cpp; "
       "CBlockHeader, CBlock, GetHash, src/primitives/block.h and block.cpp; Hash, Hash160, src/hash.h; "
       "CSHA256, src/crypto/sha256.cpp; CRIPEMD160, src/crypto/ripemd160.cpp; CSHA1, src/crypto/sha1.cpp; "
       "GetTransactionWeight/GetBlockWeight, src/consensus/validation.h; WITNESS_SCALE_FACTOR, MAX_BLOCK_WEIGHT, src/consensus/consensus.h; "
       "CreateGenesisBlock and hashGenesisBlock, src/kernel/chainparams.cpp")
TAGS = ["bitcoin", "consensus", "serialization", "sha256", "merkle", "genesis", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinSer",
    "definition_title": "Serialization (CompactSize, transactions, headers, blocks), SHA-256d, Hash160, weights, and the genesis block",
    "natural_language_statement": r"""**Integers.** $\mathrm{leBytes}(k, n)$ is the $k$-byte little-endian encoding of $n$ modulo $2^{8k}$; $\mathrm{leVal}$ reads a byte list little-endian; $\mathrm{readLE}(k)$ consumes $k$ bytes (`none` if fewer remain). `ser8/16/32/64` are the fixed-width writers; signed 64/32-bit values are written two's-complement and read back with the sign restored. $\mathrm{MAX\_SIZE} = 2^{25}$.

**CompactSize.** $\mathrm{writeCompactSize}$ is `WriteCompactSize`: one byte below $253$, else a marker $253/254/255$ followed by $2/4/8$ little-endian bytes. $\mathrm{readCompactSize}(\text{rangeCheck})$ is `ReadCompactSize`: `none` on a short read, on a non-canonical encoding (a $2$-byte value below $253$, a $4$-byte value below $2^{16}$, an $8$-byte value below $2^{32}$), or, when range-checked, on a value above $\mathrm{MAX\_SIZE}$.

**Vectors and byte strings.** A vector is its CompactSize length followed by its elements; a byte string (`CScript`, witness element) is its length then its bytes; `uint256` is 32 raw bytes. Readers use the range-checked CompactSize, as the source's vector reader does.

**Transactions.** `OutPoint` (32-byte hash, `n`), `TxIn` (prevout, scriptSig, nSequence, witness stack), `TxOut` (`nValue : Int`, scriptPubKey), `Tx` (`version`, `vin`, `vout`, `nLockTime`). $\mathrm{serTx}(\text{allowWitness})$ is `SerializeTransaction`: the basic format `version vin vout nLockTime`, or, when witnesses are allowed and present (`hasWitness`), the BIP144 extended format with the dummy empty `vin` and flag byte $1$ before the real `vin`, and one witness stack per input before `nLockTime`. $\mathrm{readTx}(\text{allowWitness})$ is `UnserializeTransaction` with its exact control flow: an empty `vin` with witnesses allowed is reinterpreted as the dummy, a flag byte is read, flag bit $1$ reads the witnesses and rejects an all-empty witness record, any remaining flag bit rejects. $\mathrm{stripWitness}$ clears every witness stack.

**Headers and blocks.** `Header` is the 80-byte `CBlockHeader` (`int32 nVersion`, two 32-byte hashes, `nTime`, `nBits`, `nNonce`); `Block` is a header and a transaction vector; `serBlock`/`readBlock` take the same witness flag. The `wf` predicates state the field ranges under which serialization is faithful: 32-bit fields below $2^{32}$, hashes of 32 bytes, amounts in $[-2^{63}, 2^{63})$, lengths at most $\mathrm{MAX\_SIZE}$, and for a block every transaction has an input or a witness.

**Hashes.** $\mathrm{sha256}$, $\mathrm{ripemd160}$ and $\mathrm{sha1}$ are the full compression-function algorithms of `crypto/` (Merkle–Damgård padding, 64-byte chunks, 32-bit word arithmetic); $\mathrm{hash256} = \mathrm{sha256} \circ \mathrm{sha256}$ is `Hash`, $\mathrm{hash160} = \mathrm{ripemd160} \circ \mathrm{sha256}$ is `Hash160`; `txid` is `hash256` of the witness-stripped serialization, `wtxid` of the full one (equal to `txid` without witness), `headerHash` is `CBlockHeader::GetHash`.

**Weights and genesis.** `txWeight`/`blockWeight` are `GetTransactionWeight`/`GetBlockWeight` ($3 \cdot |\text{stripped}| + |\text{full}|$); `MAX_BLOCK_WEIGHT` $= 4{,}000{,}000$. `genesisCoinbase`, `genesisHeader`, `genesisBlock` transcribe `CreateGenesisBlock(1231006505, 2083236893, 0x1d00ffff, 1, 50 COIN)` with the literal scriptSig and output script; `genesisHash` and `genesisMerkleRoot` are the hashes recorded in `chainparams.cpp` in serialized byte order.

**Formalization Note.** Byte lists and natural numbers replace streams and fixed-width C++ types; truncation modulo $2^{8k}$ models the writers on out-of-range values, which the `wf` predicates exclude. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinSer.leBytes_length": dict(title="A fixed-width encoding has its width",
    nl=r"""For all $k, n$: $|\mathrm{leBytes}(k, n)| = k$.""",
    ms=("Fixed-width integers — length", "Induction on the width.")),
"BitcoinSer.readLE_leBytes": dict(title="Fixed-width integers round-trip",
    nl=r"""For all $k$, $n < 2^{8k}$ and remainder $r$: $\mathrm{readLE}(k, \mathrm{leBytes}(k,n) ++ r) = \mathrm{some}(n, r)$.""",
    ms=("Fixed-width integers — round-trip", "Little-endian value of the little-endian encoding below the width bound.")),
"BitcoinSer.compactSize_roundtrip": dict(title="CompactSize round-trips",
    nl=r"""For all $n < 2^{64}$ and $r$: $\mathrm{readCompactSize}(\mathtt{false}, \mathrm{writeCompactSize}(n) ++ r) = \mathrm{some}(n, r)$ — the unchecked reader accepts every encoding the writer produces, in all four width classes.""",
    ms=("CompactSize — round-trip", "Four cases on the width class; each passes the canonicality test.")),
"BitcoinSer.compactSize_canonical": dict(title="ReadCompactSize accepts only canonical encodings",
    nl=r"""For every mode, byte list $b$, value $n$ and remainder $r$: if $\mathrm{readCompactSize}(b) = \mathrm{some}(n, r)$ then $b = \mathrm{writeCompactSize}(n) ++ r$. The reader is injective on encodings: a value has exactly one accepted encoding, so a CompactSize can never be padded to a longer form.""",
    ms=("CompactSize — canonicality", "Invert each width class; the non-canonical rejections are exactly what forces the shortest form.")),
"BitcoinSer.compactSize_range": dict(title="A read CompactSize is bounded",
    nl=r"""Every value a successful $\mathrm{readCompactSize}$ returns is below $2^{64}$, and below or equal to $\mathrm{MAX\_SIZE} = 2^{25}$ when the range check is on.""",
    ms=("CompactSize — range", "Width bound of the read bytes, and the explicit range test.")),
"BitcoinSer.serHeader_length": dict(title="A block header serializes to 80 bytes",
    nl=r"""For every well-formed header $h$: $|\mathrm{serHeader}(h)| = 80$.""",
    ms=("Headers — 80 bytes", "4 + 32 + 32 + 4 + 4 + 4.")),
"BitcoinSer.header_roundtrip": dict(title="Block headers round-trip",
    nl=r"""For every well-formed header $h$ and remainder $r$: $\mathrm{readHeader}(\mathrm{serHeader}(h) ++ r) = \mathrm{some}(h, r)$, including the signed `nVersion`.""",
    ms=("Headers — round-trip", "Compose the field round-trips.")),
"BitcoinSer.tx_roundtrip": dict(title="Transactions round-trip in both formats",
    nl=r"""For every well-formed transaction $tx$, witness mode $aw$ with ($aw$ ⇒ `vin` non-empty), and remainder $r$:
$$\mathrm{readTx}(aw, \mathrm{serTx}(aw, tx) ++ r) = \mathrm{some}(\text{if } aw \text{ then } tx \text{ else } \mathrm{stripWitness}(tx),\ r).$$
With witnesses allowed the extended format (dummy, flag byte, witness stacks) is parsed back exactly; without, the basic format returns the transaction with cleared witnesses. The non-empty-`vin` side condition is genuine: `UnserializeTransaction` reads an empty `vin` as the BIP144 dummy, so a witness-less, input-less transaction does not round-trip through the witness-aware reader.""",
    ms=("Transactions — round-trip", "Basic format for both readers; extended format with the dummy, the flag byte, the witness stacks and the superfluous-witness test.")),
"BitcoinSer.serTx_strip": dict(title="The witness-stripped serialization ignores witnesses",
    nl=r"""For every transaction: $\mathrm{serTx}(\mathtt{false}, tx) = \mathrm{serTx}(\mathtt{false}, \mathrm{stripWitness}(tx))$.""",
    ms=("Transactions — witness independence of the basic format", "The basic format never consults the witness field.")),
"BitcoinSer.txid_strip": dict(title="The txid does not depend on witness data",
    nl=r"""For every transaction: $\mathrm{txid}(tx) = \mathrm{txid}(\mathrm{stripWitness}(tx))$ — the segregated-witness property that signatures can change without changing the transaction id.""",
    ms=("Transactions — txid is witness-independent", "Immediate from the basic-format lemma.")),
"BitcoinSer.weight_no_witness": dict(title="Without witnesses the weight is four times the size",
    nl=r"""For every transaction with no witness: the two serializations coincide, and $\mathrm{txWeight}(tx) = 4 \cdot |\mathrm{serTx}(\mathtt{false}, tx)|$.""",
    ms=("Weights — legacy transactions", "The flag is zero, so both formats are the basic one.")),
"BitcoinSer.sha256_length": dict(title="SHA-256 outputs 32 bytes",
    nl=r"""For every message: $|\mathrm{sha256}(m)| = 32$.""",
    ms=("Hashes — SHA-256 output size", "Eight big-endian words.")),
"BitcoinSer.hash160_length": dict(title="Hash160 outputs 20 bytes",
    nl=r"""For every message: $|\mathrm{hash160}(m)| = 20$.""",
    ms=("Hashes — Hash160 output size", "Five little-endian words.")),
"BitcoinSer.genesis_merkle": dict(title="The genesis coinbase hashes to the recorded merkle root",
    nl=r"""$\mathrm{txid}(\mathrm{genesisCoinbase}) = \mathrm{genesisMerkleRoot}$: the transcribed genesis coinbase transaction, serialized and double-SHA-256'd by the transcribed algorithms, gives exactly `4a5e1e4b…eda33b`. Checked by kernel evaluation of the full SHA-256.""",
    ms=("Genesis — merkle root", "Kernel evaluation of serialization and SHA-256d.")),
"BitcoinSer.genesis_hash": dict(title="The genesis header hashes to hashGenesisBlock",
    nl=r"""$\mathrm{headerHash}(\mathrm{genesisHeader}) = \mathrm{genesisHash}$: the transcribed genesis header (with the merkle root computed from the coinbase) double-SHA-256's to `000000000019d668…0a8ce26f`, the mainnet genesis hash of `chainparams.cpp`. Checked by kernel evaluation; this ties the hash transcription to the real chain.""",
    ms=("Genesis — block hash", "Kernel evaluation of the 80-byte header and SHA-256d.")),
"BitcoinSer.block_roundtrip": dict(title="Blocks round-trip",
    nl=r"""For every well-formed block $b$, witness mode $aw$ and remainder $r$:
$$\mathrm{readBlock}(aw, \mathrm{serBlock}(aw, b) ++ r) = \mathrm{some}\big(\langle b.\mathrm{header},\ b.\mathrm{vtx}\text{ mapped by (if } aw \text{ then id else stripWitness)}\rangle,\ r\big).$$
Deserialization is a left inverse of serialization on well-formed blocks in both formats: a block read back from its own bytes is the block (with witnesses, in the witness-aware reader; without, in the legacy one). This is the "interpretation of serialized data" that every hash commitment — merkle root, block hash, txid — refers to.

**Formalization Note.** Well-formedness is the field-range predicate of the definition (32-bit fields, 32-byte hashes, 64-bit amounts, vector lengths at most $\mathrm{MAX\_SIZE}$, every transaction with an input or a witness); the last condition reflects the dummy-`vin` reinterpretation of the source.""",
    ms=None),
"BitcoinSer.serBlock_injective": dict(title="Block serialization is injective",
    nl=r"""For well-formed blocks $b_1, b_2$: $\mathrm{serBlock}(\mathtt{true}, b_1) = \mathrm{serBlock}(\mathtt{true}, b_2) \Rightarrow b_1 = b_2$. Consequently distinct well-formed blocks have distinct byte strings, and a hash of the serialization identifies the block up to hash collisions.""",
    ms=("Blocks — injectivity", "Corollary of the round-trip.")),
}
ORDER = ["BitcoinSer.leBytes_length","BitcoinSer.readLE_leBytes","BitcoinSer.compactSize_roundtrip","BitcoinSer.compactSize_canonical",
         "BitcoinSer.compactSize_range","BitcoinSer.serHeader_length","BitcoinSer.header_roundtrip","BitcoinSer.tx_roundtrip",
         "BitcoinSer.serTx_strip","BitcoinSer.txid_strip","BitcoinSer.weight_no_witness","BitcoinSer.sha256_length","BitcoinSer.hash160_length",
         "BitcoinSer.genesis_merkle","BitcoinSer.genesis_hash","BitcoinSer.serBlock_injective","BitcoinSer.block_roundtrip"]
