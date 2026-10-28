# Read-back: `BitcoinBlockV2.genesis_checkBlock`

**Binders and hypotheses.** None. The statement is closed.

**Conclusion.** $\mathrm{checkBlock}(\mathrm{genesisBlock}) = \mathrm{true}$, where `genesisBlock` is the imported constant block whose header is the genesis header $(\mathit{version} = 1,\ \mathit{prevBlock} = 32 \text{ zero bytes},\ \mathit{merkleRoot} = \mathrm{txid}(\mathrm{genesisCoinbase}),\ \mathit{time} = 1231006505,\ \mathit{bits} = \mathtt{0x1d00ffff},\ \mathit{nonce} = 2083236893)$ and whose transaction list is $[\mathrm{genesisCoinbase}]$, the genesis coinbase being the transaction with version $1$, one input (prevout $=$ (32 zero bytes, $\mathtt{0xffffffff}$), scriptSig the fixed 77-byte literal `genesisScriptSig`, sequence $\mathtt{0xffffffff}$, empty witness), one output (value $5\,000\,000\,000$, scriptPubKey the fixed 67-byte literal `genesisOutputScript`), locktime $0$.

Unfolding $\mathrm{checkBlock}$, the claim is the conjunction of:
1. proof of work: $\mathtt{0x1d00ffff}$ decodes (`deriveTarget`) to a target $t$ (mantissa $\mathtt{0x00ffff}$ shifted left by $8\cdot(\mathtt{0x1d}-3)$ bits, not negative, non-zero, not overflowing, $t \le 2^{224}-1$) and the little-endian integer value of $\mathrm{hash256}$ of the serialized genesis header is $\le t$;
2. the merkle root of $[\mathrm{txid}(\mathrm{genesisCoinbase})]$ — for a single-element list, that txid itself — equals the header's merkle root, and the mutation flag is false;
3. the transaction list is non-empty; $4 \cdot 1 \le 4\,000\,000$; $4 \cdot |\mathrm{serBlock}(\mathrm{false}, \mathrm{genesisBlock})| \le 4\,000\,000$;
4. the first transaction is a coinbase (one input with null prevout) and no later transaction is a coinbase (vacuous);
5. the genesis coinbase passes $\mathrm{checkTransaction}$: non-empty inputs and outputs, $4\cdot$stripped size $\le 4\,000\,000$, the single output value $5\cdot 10^9 \in [0, 21\cdot10^{14}]$, distinct prevouts (one input), and $2 \le |\mathrm{genesisScriptSig}| \le 100$;
6. $4 \cdot \mathrm{legacySigOpCount}(\mathrm{genesisCoinbase}) \le 80\,000$, where the legacy count parses the scriptSig and the output script (which ends in `OP_CHECKSIG` $= \mathtt{0xac}$) counting `CHECKSIG`-family opcodes.

Since everything is concrete, the statement is a closed computation on the fixed constants, including the SHA-256 computations of the header hash and txid.

**Edge cases silently included:** none from quantifiers; the claim depends on the exact byte values of the imported literals and of the SHA-256 implementation.
