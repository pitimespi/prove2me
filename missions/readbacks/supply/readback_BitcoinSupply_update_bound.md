# Read-back: `BitcoinSupply.update_bound`

## Objects and notation

A **ledger** $u$ is a finite list of pairs $(k, c)$: $k$ an *outpoint* (a byte list $k.\mathrm{hash}$ and a natural number $k.n$), $c$ a *coin* $(c.\mathrm{out}, c.\mathrm{height}, c.\mathrm{isCoinbase})$ whose output $c.\mathrm{out}$ has an integer value $c.\mathrm{out}.\mathrm{nValue}$ and a byte-list script. A **transaction** $tx$ has a version $\in \mathbb{N}$, a list of inputs $tx.\mathrm{vin}$ (each input $i$ has an outpoint $i.\mathrm{prevout}$, a scriptSig, a sequence number and a witness), a list of outputs $tx.\mathrm{vout}$ (each output $o$ has an integer $o.\mathrm{nValue}$ and a script), and a lock time.

- $\mathrm{getCoin}(u, p)$: the coin of the **first** entry of $u$ whose key equals $p$, if any. $\mathrm{haveCoin}(u,p)$ is true iff such an entry exists.
- $\mathrm{accessCoin}(u,p)$: that coin if it exists, otherwise the dummy coin whose output has value $-1$ (and empty script, height $0$, non-coinbase).
- $\mathrm{isCoinBase}(tx)$ is true iff $tx.\mathrm{vin}$ consists of **exactly one** input and that input's outpoint is the null outpoint (hash $=$ 32 zero bytes and index $= 2^{32}-1$). A transaction with no inputs, or with two or more inputs, is *not* a coinbase under this definition.
- $\mathrm{valueOut}(tx) = \sum_{o \in tx.\mathrm{vout}} o.\mathrm{nValue}$ (integer sum, $0$ for no outputs).
- $\mathrm{valueIn}(u, \mathit{ins}) = \sum_{i \in \mathit{ins}} \mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out}.\mathrm{nValue}$; an input whose outpoint has no entry in $u$ contributes $-1$.
- $\mathrm{totalValue}(u) = \sum_{(k,c) \in u} c.\mathrm{out}.\mathrm{nValue}$, every list entry counted.
- $\mathrm{keysNodup}(u)$: the list of keys $[k_1, \dots, k_m]$ of $u$ has no repeated element.
- $\mathrm{txid}(tx)$: the double SHA-256 of the witness-stripped serialization of $tx$.
- A script $s$ is **unspendable** iff ($s$ is non-empty and its first byte is $0x6a$) or $|s| > 10{,}000$.
- $\mathrm{updateCoins}(u, tx, H)$ for $H \in \mathbb{N}$: let $u_0 = u$ if $\mathrm{isCoinBase}(tx)$, and otherwise let $u_0$ be $u$ with, for each input $i$ of $tx$ in order, **every** entry whose key equals $i.\mathrm{prevout}$ deleted. Then, for the outputs $o_0, o_1, \dots$ of $tx$ in order with their indices: if $o_j$'s script is unspendable the ledger is unchanged; otherwise every entry with key $(\mathrm{txid}(tx), j)$ is deleted and the entry $\big((\mathrm{txid}(tx), j),\ (o_j, H, \mathrm{isCoinBase}(tx))\big)$ is prepended. The result is the ledger after the last output.

## Statement

For every ledger $u$, every transaction $tx$, and every natural number $H$, under the hypotheses

1. $\mathrm{keysNodup}(u)$: the keys of $u$ are pairwise distinct;
2. for every entry $(k,c) \in u$: $0 \le c.\mathrm{out}.\mathrm{nValue}$;
3. for every output $o \in tx.\mathrm{vout}$: $0 \le o.\mathrm{nValue}$;
4. the list of outpoints $[\,i.\mathrm{prevout} : i \in tx.\mathrm{vin}\,]$ has no repeated element;
5. if $\mathrm{isCoinBase}(tx)$ is false, then for every input $i \in tx.\mathrm{vin}$, $\mathrm{haveCoin}(u, i.\mathrm{prevout})$ is true (some entry of $u$ has key $i.\mathrm{prevout}$);

the following inequality between integers holds:
$$\mathrm{totalValue}\big(\mathrm{updateCoins}(u, tx, H)\big) \;\le\; \mathrm{totalValue}(u) + \mathrm{valueOut}(tx) - \begin{cases} 0 & \text{if } \mathrm{isCoinBase}(tx) \\ \mathrm{valueIn}(u, tx.\mathrm{vin}) & \text{otherwise.} \end{cases}$$

The subtraction is ordinary integer subtraction. The inequality is non-strict.

## Edge cases the statement includes

- $H$ only becomes the recorded height of the newly added coins; it is otherwise unconstrained (it may be $0$, or unrelated to anything in $u$).
- $tx$ with **no inputs**: $\mathrm{isCoinBase}(tx)$ is false, hypothesis 5 is vacuous, no entries are deleted, $\mathrm{valueIn}(u, []) = 0$, and the claim is $\mathrm{totalValue}(\text{$u$ with the spendable outputs of $tx$ added}) \le \mathrm{totalValue}(u) + \mathrm{valueOut}(tx)$.
- $tx$ with **no outputs**: nothing is added; for a non-coinbase the claim is that deleting the spent entries lowers the total by at least $\mathrm{valueIn}$.
- A coinbase (one null-outpoint input): no deletion, no $\mathrm{valueIn}$ term; hypothesis 5 does not apply, and nothing requires $u$ to lack an entry at the null outpoint.
- Outputs with unspendable scripts are counted in $\mathrm{valueOut}(tx)$ but are never added to the ledger.
- Outputs of $tx$ whose key $(\mathrm{txid}(tx), j)$ already occurs in $u$ replace the existing entry (the old entry is deleted); hypothesis 5 and the BIP30 rule are not part of this statement, so such collisions are allowed here.
- No upper bound on any value is assumed: values in $u$ and in $tx.\mathrm{vout}$ may exceed $\mathrm{MAX\_MONEY}$; only non-negativity is assumed.
- The hypotheses do not require $tx$ to be well formed in any other way (no script checks, no size checks, no requirement that non-coinbase inputs have non-null outpoints).
