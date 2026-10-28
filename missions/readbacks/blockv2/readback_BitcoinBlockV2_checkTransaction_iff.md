# Read-back: `BitcoinBlockV2.checkTransaction_iff`

**Binder.** $tx$ is a transaction: a natural number $\mathit{version}$, a list of inputs $\mathit{vin}$ (each an outpoint $(\mathit{hash}, n)$, a scriptSig byte string, a natural $\mathit{nSequence}$ and a witness list), a list of outputs $\mathit{vout}$ (each an integer $\mathit{nValue}$ and a scriptPubKey byte string), and a natural number $\mathit{nLockTime}$. No hypotheses.

**Conclusion.** $\mathrm{checkTransaction}(tx) = \mathrm{true}$ if and only if $\mathrm{TxSpec}(tx)$.

*Left side unfolded.* $\mathrm{checkTransaction}(tx)$ is the Boolean conjunction of:
1. $\mathit{vin}$ is non-empty;
2. $\mathit{vout}$ is non-empty;
3. $4 \cdot |\mathrm{serTx}(\mathrm{false}, tx)| \le 4\,000\,000$, where $\mathrm{serTx}(\mathrm{false},\cdot)$ is the witness-stripped serialization (4 bytes version mod $2^{32}$, compact-size-prefixed inputs each as 36-byte-style outpoint, length-prefixed scriptSig, 4-byte sequence; compact-size-prefixed outputs each as 8-byte value mod $2^{64}$ and length-prefixed script; 4-byte locktime);
4. the output loop $\mathrm{outputsLoop}(\mathit{vout}, 0)$ succeeds: scanning outputs in order with a running total starting at $0$, no output has $\mathit{nValue} < 0$, none has $\mathit{nValue} > \mathrm{MAX\_MONEY} = 21\cdot 10^{14}$, and every running total stays in $[0, \mathrm{MAX\_MONEY}]$;
5. the list of prevouts of $\mathit{vin}$ has no duplicates;
6. if $\mathrm{isCoinBase}(tx)$ (exactly one input whose prevout is 32 zero bytes with index $\mathtt{0xffffffff}$) then $2 \le |\mathit{scriptSig}(i_0)| \le 100$ where $i_0$ is the head of $\mathit{vin}$ (default: an input with empty scriptSig, unreachable under 1); otherwise every input's prevout is *not* null.

*Right side unfolded.* $\mathrm{TxSpec}(tx)$ is the proposition: $\mathit{vin} \ne [\,]$; $\mathit{vout} \ne [\,]$; $4\cdot|\mathrm{serTx}(\mathrm{false}, tx)| \le 4\,000\,000$; for every output $o$, $0 \le o.\mathit{nValue} \le \mathrm{MAX\_MONEY}$; $\mathrm{valueOut}(tx) = \sum_{o} o.\mathit{nValue} \le \mathrm{MAX\_MONEY}$; the prevouts are pairwise distinct; if $\mathrm{isCoinBase}(tx) = \mathrm{true}$ then every input $i$ has $2 \le |i.\mathit{scriptSig}| \le 100$; if $\mathrm{isCoinBase}(tx) = \mathrm{false}$ then every input has a non-null prevout.

**Edge cases silently included:** the right side bounds only the final sum of output values (given all values are non-negative, every partial sum is then bounded too); the left checks the first input's scriptSig only, the right all inputs (a coinbase has exactly one); the serialization reduces $\mathit{version}$, $\mathit{nSequence}$, $\mathit{nLockTime}$, $n$ modulo $2^{32}$ and $\mathit{nValue}$ modulo $2^{64}$, so arbitrarily large field values are silently admitted by the size test.
