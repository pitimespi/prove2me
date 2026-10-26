# Read-back: `BitcoinBlock.genesis_checkBlock`

## Binders and hypotheses

None. This is a closed statement about one fixed block.

## Conclusion

$$\mathrm{checkBlock}(\mathrm{genesisBlock}) = \mathrm{true}.$$

### The block

$\mathrm{genesisBlock} = \langle \mathrm{genesisHeader}, [\mathrm{genesisCoinbase}]\rangle$, where $\mathrm{genesisCoinbase}$ is the transaction with version $1$, a single input whose prevout is $\langle 32 \text{ zero bytes}, 4294967295\rangle$, scriptSig the fixed 77-byte constant beginning $04\,ff\,ff\,00\,1d\,01\,04\,45\,\dots$ ("The Times 03/Jan/2009 …"), sequence $4294967295$ and empty witness; a single output of value $5\,000\,000\,000$ with the fixed 67-byte scriptPubKey beginning $41\,04\,67\,8a\,\dots$ and ending $\dots\,ac$; and lock time $0$. $\mathrm{genesisHeader}$ has version $1$, prevBlock $= 32$ zero bytes, merkleRoot $= \mathrm{txid}(\mathrm{genesisCoinbase})$ (double-SHA256 of its witness-free serialization), time $1231006505$, bits $0x1d00ffff = 486604799$, nonce $2083236893$.

### The check, unfolded

$\mathrm{checkBlock}$ is the Boolean conjunction of:

1. proof of work: the little-endian value of the double-SHA256 of the 80-byte serialized header is $\le$ the target decoded from $0x1d00ffff$ (mantissa $0x00ffff$, exponent $0x1d = 29$, i.e. $0xffff \cdot 256^{26}$), with that compact word not negative, not zero, not overflowing, and the target $\le 2^{224}-1$;
2. the merkle root computed from $[\mathrm{txid}(\mathrm{genesisCoinbase})]$ — a single hash, returned unchanged — equals the header's merkleRoot, and the mutated flag is false;
3. the transaction list is non-empty;
4. $4\cdot 1 \le 4\,000\,000$;
5. $4\cdot|\mathrm{serBlock}(\mathrm{false}, \mathrm{genesisBlock})| \le 4\,000\,000$;
6. the first transaction is a coinbase (one input with null prevout);
7. no later transaction is a coinbase (vacuous);
8. $\mathrm{checkTransaction}(\mathrm{genesisCoinbase})$: non-empty inputs and outputs; $4\cdot$ serialized size $\le 4\,000\,000$; the output value $5\cdot10^9 \in [0, 2.1\cdot10^{15}]$ and the running sum in range; distinct prevouts (one input); coinbase scriptSig length in $[2,100]$ (it is $77$);
9. $4\cdot\mathrm{legacySigOpCount}(\mathrm{genesisCoinbase}) \le 80\,000$, where the count scans the scriptSig and the scriptPubKey adding $1$ per `OP_CHECKSIG`/`OP_CHECKSIGVERIFY` and $20$ per `OP_CHECKMULTISIG`/`OP_CHECKMULTISIGVERIFY` (parsing stops at a malformed push).

The statement asserts the whole conjunction evaluates to true for these concrete constants, which includes the concrete SHA-256 computations.

## Edge cases silently included

None beyond the concrete constants; the claim is decidable by computation.
