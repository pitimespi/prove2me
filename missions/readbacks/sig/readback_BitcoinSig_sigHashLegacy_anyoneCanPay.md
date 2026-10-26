# Read-back: `BitcoinSig.sigHashLegacy_anyoneCanPay`

**Binders and hypothesis.** Universally quantified over: a byte string $scriptCode$; two transactions $tx$ and $tx'$; natural numbers $nIn$ (an input index) and $hashType$ (an unbounded natural number, not restricted to a byte). Write $D$ for the *default input* $\langle\langle[\,],0\rangle,[\,],0,[\,]\rangle$ (empty prevout hash, prevout index 0, empty scriptSig, sequence 0, no witness), and $tx.\text{vin}[nIn]_D$ for the $nIn$-th input of $tx$ or $D$ if $nIn \geq |tx.\text{vin}|$. Five hypotheses:
- $hacp$: $hashType \mathbin{\&} 128 \neq 0$ (bitwise AND on natural numbers; the `SIGHASH_ANYONECANPAY` bit is set);
- $h1$: $tx'.\text{version} = tx.\text{version}$;
- $h2$: $tx'.\text{vout} = tx.\text{vout}$ (the output lists are equal as lists);
- $h3$: $tx'.\text{nLockTime} = tx.\text{nLockTime}$;
- $h4$: $(tx'.\text{vin}[nIn]_D).\text{prevout} = (tx.\text{vin}[nIn]_D).\text{prevout}$;
- $h5$: $(tx'.\text{vin}[nIn]_D).\text{nSequence} = (tx.\text{vin}[nIn]_D).\text{nSequence}$.
Nothing is assumed about the number of inputs of either transaction, about other inputs, or about scriptSigs and witnesses.

**Conclusion.**
$$\text{sigHashLegacy}\ scriptCode\ tx'\ nIn\ hashType = \text{sigHashLegacy}\ scriptCode\ tx\ nIn\ hashType .$$

**Unfolding.** `sigHashLegacy` $sc\,t\,nIn\,ht$ is `uint256One` (the byte 1 followed by 31 zeros) if $ht \mathbin{\&} 31 = 3$ and $|t.\text{vout}| \leq nIn$; otherwise it is the double SHA-256 of `serSigTx` $t\,sc\,nIn\,ht$ followed by the 4 little-endian bytes of $ht \bmod 2^{32}$. The special-case test depends only on $ht$, $nIn$ and the output list, which $h2$ equates, so both sides take the same branch. In the hashing branch, `serSigTx` with the ANYONECANPAY bit set serializes: the 4-byte version; the compact size $1$; exactly one input record, which is `serSigInput` at index $nIn$ (because of the bit, the loop index is overridden by $nIn$): `serOutPoint` of the prevout of $t.\text{vin}[nIn]_D$ (hash bytes, then 4-byte index), then — since the index equals $nIn$ — `serScriptCode` $sc$ (the script code with `OP_CODESEPARATOR` instructions removed, prefixed by its compact size), then the 4-byte sequence of $t.\text{vin}[nIn]_D$; then the compact size of $nOutputs$ and the output records, where $nOutputs$ is $0$ if $ht \mathbin{\&} 31 = 2$, $nIn + 1$ if $ht \mathbin{\&} 31 = 3$, else $|t.\text{vout}|$, and each record is `serTxOut` of output $j$ (or of $\langle -1, [\,] \rangle$ if $j \neq nIn$ in SINGLE mode or if $j$ is out of range); then the 4-byte lock time. Every quantity consulted — version, the chosen input's prevout and sequence, the output list, the lock time, and the common $sc$, $nIn$, $ht$ — is equated by the hypotheses, so the serializations and hence the hashes coincide.

**Edge cases.** If $nIn$ is out of range for one or both transactions, $h4$/$h5$ compare against the default input's empty hash and zero sequence, and the serialized outpoint of the default is only 4 zero bytes. Hash types such as $128$ (ANYONECANPAY with low bits $0$) or $128 + 4$ fall into the "all outputs" treatment. $hashType$ values above $255$ are permitted by the binder.

**What is not said.** The statement does not say anything when the ANYONECANPAY bit is clear (then other inputs' prevouts and sequences matter). It does not say that the hypotheses are *necessary* for equality of hashes. It does not say the two transactions have the same number of inputs or the same inputs other than input $nIn$, and does not need to. It does not mention scriptSigs or witnesses at all. It does not say that the common hash is a hash of anything "meaningful", nor that it differs from `uint256One`. It does not involve the witness-v0 signature hash.
