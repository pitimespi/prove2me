## Why serialization and hashing are consensus

Every commitment in Bitcoin — a transaction id, a merkle root, a block hash, the proof-of-work target test — is a hash of a byte string, and the byte string is produced by a serializer that every node must implement identically. A node that encoded a CompactSize one byte longer, or read a witness flag differently, would compute different ids for the same transaction and fork from the network. Bitcoin Core's serialization lives in `serialize.h` (integers, `CompactSize`, vectors), `primitives/transaction.h` (the basic and BIP144 extended transaction formats), `primitives/block.h` (the 80-byte header), and its hashes in `crypto/` and `hash.h`. ([`serialize.h`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/serialize.h), [`transaction.h`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/primitives/transaction.h), [`sha256.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/crypto/sha256.cpp))

This mission transcribes that layer — writers and readers for integers, CompactSize, vectors, transactions, headers and blocks; SHA-256, RIPEMD-160 and SHA-1 as full algorithms; `Hash`, `Hash160`, `txid`, `wtxid`, the header hash; transaction and block weights; and the mainnet genesis block — and proves the properties the rest of consensus consumes: encodings are canonical and round-trip, the witness-stripped id ignores witnesses, hashes have their sizes, and the transcribed genesis block hashes to the genesis hash of `chainparams.cpp`.

## Bytes, readers, and well-formedness

A **writer** turns a value into a byte list; a **reader** consumes a prefix of a byte list and returns the value and the remainder, or `none` where the source throws. Fixed-width integers are little-endian; signed ones are two's complement. A **CompactSize** is one byte below $253$, or a marker byte $253$, $254$, $255$ followed by $2$, $4$, $8$ little-endian bytes; the reader rejects an encoding that could have been shorter ("non-canonical") and, in its default range-checked mode, any value above $\mathrm{MAX\_SIZE} = 2^{25}$. A vector is its CompactSize length then its elements; a byte string is its length then its bytes; a `uint256` is 32 raw bytes.

A **transaction** serializes as `version vin vout nLockTime`, or, when witnesses are allowed and some input carries one, in the **extended format**: `version 0x00 0x01 vin vout witnesses nLockTime`, where the `0x00` is an empty dummy `vin` and `0x01` the flag byte. The reader follows the source's control flow exactly: it reads `vin`; if that is empty and witnesses are allowed it treats it as the dummy, reads the flag byte and, if non-zero, the real `vin` and `vout`; a set witness bit then reads one witness stack per input and rejects a record whose stacks are all empty; any other flag bit rejects. A **header** is `int32 nVersion`, previous hash, merkle root, `nTime`, `nBits`, `nNonce`; a **block** is a header and a transaction vector.

**Well-formedness** names the field ranges under which the writers are faithful: 32-bit fields below $2^{32}$, hashes of 32 bytes, amounts in $[-2^{63}, 2^{63})$, lengths at most $\mathrm{MAX\_SIZE}$, and — for blocks — every transaction has an input or a witness.

**Hashes** are the algorithms of `crypto/`: Merkle–Damgård padding, 64-byte chunks, the SHA-256 schedule and 64 rounds, the two RIPEMD-160 lines, the SHA-1 rounds; `Hash` is SHA-256 twice and `Hash160` is RIPEMD-160 of SHA-256. The **txid** hashes the witness-stripped serialization; the **wtxid** the full one; the block hash the 80-byte header. **Weight** is three times the stripped size plus the full size.

## Formalization targets

### Goal — blocks round-trip
$$
\mathrm{readBlock}(aw, \mathrm{serBlock}(aw, b) ++ r) = \mathrm{some}(\text{(}b\text{ with witnesses iff } aw\text{)},\ r)
$$
for every well-formed block $b$, witness mode $aw$ and remainder $r$. This is `BitcoinSer.block_roundtrip`: deserialization is a left inverse of serialization, in the witness-aware and the legacy reader alike. It is the statement that gives every hash commitment a referent: the bytes a node hashes are exactly the bytes from which every other node recovers the same block.

### Supporting milestones
1. **Fixed-width integers** (`leBytes_length`, `readLE_leBytes`): width and round-trip.
2. **CompactSize** (`compactSize_roundtrip`, `compactSize_canonical`, `compactSize_range`): the writer's output is accepted; only the shortest encoding is ever accepted; read values are bounded.
3. **Headers** (`serHeader_length`, `header_roundtrip`): 80 bytes, round-trip with the signed version.
4. **Transactions** (`tx_roundtrip`): round-trip in both formats, with the genuine side condition that the witness-aware reader needs a non-empty `vin` or a witness.
5. **Witness independence** (`serTx_strip`, `txid_strip`): the stripped serialization and the txid ignore witness data.
6. **Weights** (`weight_no_witness`): without witnesses, weight is four times the size.
7. **Hash sizes** (`sha256_length`, `hash160_length`).
8. **Genesis** (`genesis_merkle`, `genesis_hash`): the transcribed genesis coinbase and header hash, by kernel evaluation of the transcribed SHA-256, to the merkle root and block hash recorded in `chainparams.cpp`.
9. **Injectivity** (`serBlock_injective`): distinct well-formed blocks have distinct serializations.

## What the result establishes

The round-trip and canonicality theorems make the byte layer of consensus exact: a transaction or block has one encoding, the encoding determines the object, and the identifier hashes are functions of the object alone. The genesis theorems are an end-to-end check against the real chain: the transcriptions of `CreateGenesisBlock`, the serializers and SHA-256 together reproduce the hard-coded genesis hash, which no transcription error in any of them could survive. The witness-independence theorem is the structural fact behind segregated witness. For the whole-consensus development this mission supplies the concrete hash and serialization semantics that the Merkle, header, proof-of-work and script components took as parameters.

Not modeled: network message framing, `CompactSize` reading in the chunked allocation loop (semantically the same read), serialization of `CBlockIndex`/undo data, and the stream exception types (all failures are `none`).

Status: all statements are open with intentional placeholder proofs. The hash functions have been checked against the standard test vectors and the genesis values by evaluation; the genesis theorems are stated so that the kernel re-checks them.

## Where the obvious argument fails

Round-trip looks like unfolding until the transaction reader: because `UnserializeTransaction` reuses the `vin` read as the witness dummy, an empty `vin` is ambiguous, and the honest theorem carries the side condition "an input or a witness". The canonicality theorem is where the three "non-canonical" rejections earn their keep: without them a value would have several encodings and the statement would be false. The signed fields need the two's-complement conversion in both directions. For the genesis theorems the difficulty is not mathematical but computational: the kernel must evaluate nine SHA-256 compressions, which the definitions are written to allow (structural recursion only, no well-founded fixpoints in the evaluated path).

## Formalization scope

Bytes are `BitVec 8`, values are `Nat`/`Int`, words are `UInt32`. Readers return `Option (α × Bytes)`. The writers truncate out-of-range values modulo the width, which the well-formedness predicates exclude; the readers are total. No Mathlib is required; the development imports only `Std`.

A trivializing formalization would define the readers as inverses of the writers; here each reader follows the source's byte-level control flow, and the round-trips are theorems.

## Selected references

- Bitcoin Core contributors. *`serialize.h`*, *`primitives/transaction.h`*, *`primitives/block.h`*, *`hash.h`*, *`crypto/sha256.cpp`*, *`crypto/ripemd160.cpp`*, *`kernel/chainparams.cpp`* at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/tree/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src)
- Eric Lombrozo, Johnson Lau, Pieter Wuille. *BIP141: Segregated Witness* and *BIP144: Peer Services* (transaction serialization with witness), 2015. [BIP144](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0144.mediawiki)
- NIST. *FIPS 180-4: Secure Hash Standard*, 2015. [Standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf)
