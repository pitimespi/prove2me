# Read-back: `BitcoinSer.genesis_merkle`

**Binders and hypothesis.** None. A closed equality between two concrete byte strings.

**Conclusion.**
$$\texttt{txid}(\texttt{genesisCoinbase}) = \texttt{genesisMerkleRoot}.$$

**Unfolding the left side.** $\texttt{txid}(tx) = \texttt{hash256}(\texttt{serTx}\;\mathrm{false}\;tx) = \texttt{sha256}(\texttt{sha256}(\texttt{serTx}\;\mathrm{false}\;tx))$: the file's SHA-256 applied twice to the *witness-free* serialization of the transaction. The constant `genesisCoinbase` has version $1$, exactly one input, exactly one output and lock time $0$. The input's previous outpoint is 32 zero bytes with index $\mathrm{0xffffffff}$; its script is the literal 77-byte `genesisScriptSig` ($\mathrm{04\,ff\,ff\,00\,1d\,01\,04\,45}$ followed by 69 ASCII bytes of English text); its sequence is $\mathrm{0xffffffff}$; its witness list is empty. The output has value $5\,000\,000\,000$ and the literal 67-byte `genesisOutputScript` ($\mathrm{41}$, 65 bytes starting $\mathrm{04}$, then $\mathrm{ac}$). With $aw = \mathrm{false}$ the flag $\phi$ is $0$, so the serialization is
$$\texttt{ser32}(1) \mathbin{+\!\!+} [1] \mathbin{+\!\!+} \big(0^{32} \mathbin{+\!\!+} \texttt{ser32}(\mathrm{0xffffffff}) \mathbin{+\!\!+} [77] \mathbin{+\!\!+} \texttt{genesisScriptSig} \mathbin{+\!\!+} \texttt{ser32}(\mathrm{0xffffffff})\big) \mathbin{+\!\!+} [1] \mathbin{+\!\!+} \big(\texttt{serInt64}(5\,000\,000\,000) \mathbin{+\!\!+} [67] \mathbin{+\!\!+} \texttt{genesisOutputScript}\big) \mathbin{+\!\!+} \texttt{ser32}(0),$$
a string of $4 + 1 + 118 + 1 + 76 + 4 = 204$ bytes (the two "$[1]$" are CompactSize counts of one input and one output; $[77]$ and $[67]$ are the one-byte CompactSize script lengths, both below 253). No marker/flags bytes and no witness section appear. The first SHA-256 pads 204 bytes to 256 (four 64-byte chunks) and the second pads the 32-byte digest to one chunk.

**Unfolding the right side.** `genesisMerkleRoot` is the literal 32-byte list beginning $[\mathrm{3b}, \mathrm{a3}, \mathrm{ed}, \mathrm{fd}, \mathrm{7a}, \mathrm{7b}, \mathrm{12}, \mathrm{b2}, \dots]$ and ending $[\dots, \mathrm{4b}, \mathrm{1e}, \mathrm{5e}, \mathrm{4a}]$. The comparison is against the bytes in the order written.

**Relation to other constants.** The record `genesisHeader` has its merkle-root field *defined* as $\texttt{txid}(\texttt{genesisCoinbase})$, so this theorem is equivalently the statement that `genesisHeader.merkleRoot` equals the literal `genesisMerkleRoot`; but the theorem is phrased in terms of `txid` and does not mention the header. Because the witness list is empty, $\texttt{serTx}\;\mathrm{true}$ would produce the same bytes and $\texttt{wtxid}$ would coincide with $\texttt{txid}$, but that is not stated.

**Nature of the claim.** A ground equality over decidable data, verifiable in principle by evaluation; it tests the transaction serializer (CompactSize, little-endian, signed 64-bit amount) and the SHA-256 implementation together on one example.

**What is not said.** Nothing about any merkle-tree computation — the file has no merkle-tree function; the "merkle root" here is just the txid of one transaction, by the author's choice of constants. Nothing about the block hash (that is `genesis_hash`). Nothing about `wtxid`, `genesisBlock`, or weights. Nothing about any transaction other than this one, nor about SHA-256 on any other input. One 32-byte ground equality.
