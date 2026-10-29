# Read-back: `BitcoinReorg.updateCoins_equiv`

## Notions used

**Ledgers and coin lookup.** A *ledger* $u$ is a finite list of pairs $(p, c)$, where $p$ is an *outpoint* (a byte string $p.\mathrm{hash}$ and a natural number $p.n$) and $c$ is a *coin* (an output $c.\mathrm{out}$ consisting of an integer value $c.\mathrm{out}.\mathrm{nValue}$ and a byte-string script $c.\mathrm{out}.\mathrm{scriptPubKey}$; a natural-number creation height $c.\mathrm{height}$; and a Boolean coinbase flag $c.\mathrm{isCoinbase}$). The lookup $\mathrm{getCoin}(u, p)$ scans $u$ from the front and returns the coin of the *first* pair whose outpoint equals $p$ (as a value "some $c$"), or "none" if no pair has outpoint $p$; any later pair with the same outpoint is shadowed and never consulted. Two ledgers are *equivalent*, written $u \sim v$, when
$$\forall p,\quad \mathrm{getCoin}(u, p) = \mathrm{getCoin}(v, p),$$
the quantifier ranging over every outpoint (every byte string and every natural number). Equivalence says nothing about the order of the lists, about duplicate or shadowed entries, or about list length.

**Spending and adding coins.** $\mathrm{spendCoin}(u, p)$ is $u$ with *every* pair whose outpoint equals $p$ removed. A script byte string $s$ is *unspendable* when it is non-empty and its first byte is the opcode $\mathtt{OP\_RETURN}$, or when its length exceeds the constant $\mathrm{MAX\_SCRIPT\_SIZE}$. $\mathrm{addCoin}(u, p, c)$ is $u$ unchanged if $c.\mathrm{out}.\mathrm{scriptPubKey}$ is unspendable, and otherwise is the pair $(p, c)$ prepended to $\mathrm{spendCoin}(u, p)$.

**Transactions.** A transaction $tx$ has a natural-number version, a list of inputs $tx.\mathrm{vin}$ (each input $i$ has an outpoint $i.\mathrm{prevout}$, a script $i.\mathrm{scriptSig}$, a natural number $i.\mathrm{nSequence}$, and a witness stack, a list of byte strings), a list of outputs $tx.\mathrm{vout}$ (each an integer value and a script), and a natural number $tx.\mathrm{nLockTime}$. $tx$ *is a coinbase* exactly when $tx.\mathrm{vin}$ has exactly one input and that input's outpoint is the null outpoint (hash equal to 32 zero bytes and index $n = 2^{32} - 1$). $\mathrm{txid}(tx)$ is the double SHA-256 of the serialization of $tx$ with all witness data stripped.

**The ledger update $\mathrm{updateCoins}(u, tx, h)$**, for a ledger $u$, a transaction $tx$ and a natural number $h$: let $u_1 = u$ if $tx$ is a coinbase, and otherwise let $u_1$ be $u$ with $\mathrm{spendCoin}$ applied successively for the outpoint $i.\mathrm{prevout}$ of every input $i$ of $tx$ in order (no check is made that those outpoints are present). Then, for the outputs $o_0, o_1, \dots, o_{k-1}$ of $tx$ in order, apply successively
$$u_{j+1} = \mathrm{addCoin}\big(u_j,\ (\mathrm{txid}(tx), j),\ \langle o_j,\ h,\ \text{isCoinbase}(tx)\rangle\big),$$
and the result is $u_k$. Outputs with unspendable scripts are therefore not stored, and each stored output replaces (after removal of) any earlier entry with the same outpoint.


## Statement

**Binders.** Two ledgers $u$ and $v$; a hypothesis $h : u \sim v$, i.e. $\forall p,\ \mathrm{getCoin}(u, p) = \mathrm{getCoin}(v, p)$; a transaction $tx$ (arbitrary: it need not be well-formed, need not have any inputs or outputs, and its inputs' outpoints need not be present in $u$ or $v$); and a natural number $H$ (the height stamped on the created coins; any natural number, including $0$).

**Conclusion.**
$$\mathrm{updateCoins}(u, tx, H) \;\sim\; \mathrm{updateCoins}(v, tx, H),$$
that is, for every outpoint $p$, the first-match lookup of $p$ in the ledger obtained from $u$ by (if $tx$ is not a coinbase) removing all entries at each input's outpoint and then adding, for each output index $j$, the coin $\langle o_j, H, \text{isCoinbase}(tx)\rangle$ at outpoint $(\mathrm{txid}(tx), j)$ unless $o_j$'s script is unspendable, equals the same lookup in the ledger obtained from $v$ in the same way.

**Edge cases the statement includes.** $tx$ with no inputs is not a coinbase (a coinbase has exactly one, null-outpoint input), so its (empty) input spend is a no-op; $tx$ with no outputs adds nothing; spending an outpoint absent from both ledgers is a no-op on both; if $u$ and $v$ differ in shadowed duplicate entries, $\mathrm{spendCoin}$ removes all copies and $\mathrm{addCoin}$ prepends, so the conclusion is still only about first-match lookups. The theorem places no condition on $u$, $v$ having distinct keys.
