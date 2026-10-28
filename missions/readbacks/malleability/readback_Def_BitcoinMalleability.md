# Read-back: `Def_BitcoinMalleability.lean`

The file declares one structure and three definitions, inside a namespace `BitcoinMalleability`, on top of the transaction and ledger types of the imported files. The notions those declarations use are unfolded first; then each declaration is read back, in file order.

## Imported notions, unfolded

- A **byte** is an 8-bit value; a **byte string** is a finite list of bytes (possibly empty).
- An **outpoint** is a pair $(h, n)$ with $h$ a byte string (of any length; no 32-byte constraint is part of the type) and $n \in \mathbb N$ (no $2^{32}$ bound is part of the type).
- A **transaction input** is a quadruple $(\mathrm{prevout}, \mathrm{scriptSig}, \mathrm{nSequence}, \mathrm{witness})$: an outpoint, a byte string, a natural number, and a list of byte strings.
- A **transaction output** is a pair $(\mathrm{nValue}, \mathrm{scriptPubKey})$ with $\mathrm{nValue} \in \mathbb Z$ (any integer) and $\mathrm{scriptPubKey}$ a byte string.
- A **transaction** $\mathrm{tx}$ is a quadruple $(\mathrm{version}, \mathrm{vin}, \mathrm{vout}, \mathrm{nLockTime})$: a natural number, a list of inputs, a list of outputs, a natural number. Nothing in the type requires $\mathrm{vin}$ or $\mathrm{vout}$ to be non-empty or any field to be in range.
- A **coin** is a triple $(\mathrm{out}, \mathrm{height}, \mathrm{isCoinbase})$: an output, a natural number, a Boolean. The **dummy coin** is $\big((-1, [\,]), 0, \mathrm{false}\big)$: value $-1$, empty script.
- A **ledger** $u$ is a finite list of pairs (outpoint, coin). It is an association list; keys are not required to be distinct and the order matters for lookup.
- $\mathrm{getCoin}(u, o)$ walks $u$ from the front and returns the coin of the **first** pair whose outpoint equals $o$ exactly (same hash bytes, same index), or nothing if no pair matches.
- $\mathrm{accessCoin}(u, o)$ is $\mathrm{getCoin}(u,o)$ when it exists, and otherwise the dummy coin. In particular, for an outpoint absent from $u$, $\mathrm{accessCoin}(u,o).\mathrm{out}.\mathrm{scriptPubKey} = [\,]$ and $\mathrm{accessCoin}(u,o).\mathrm{out}.\mathrm{nValue} = -1$.
- $\mathrm{isWitnessProgram}(s)$, for a byte string $s = s_0 s_1 \ldots s_{k-1}$ of length $k$, is **defined** (returns a pair) exactly when all three hold:
  1. $4 \le k \le 42$;
  2. $s_0 = 0$, or $\mathrm{0x51} \le s_0 \le \mathrm{0x60}$;
  3. $s_1 + 2 = k$ (so $2 \le s_1 \le 40$).
  
  When defined, it returns $(\mathrm{version}, \mathrm{program})$ with $\mathrm{version} = 0$ if $s_0 = 0$ and $\mathrm{version} = s_0 - \mathrm{0x50}$ otherwise (so $0 \le \mathrm{version} \le 16$), and $\mathrm{program} = s_2 \ldots s_{k-1}$. Otherwise it is undefined ("none"). Note that the empty string and every string of length $< 4$ are not witness programs.

## Declaration 1: structure `Intent`

An **intent** is a record with exactly four fields and no constraints between them:

$$
t = (\mathrm{version},\ \mathrm{inputs},\ \mathrm{vout},\ \mathrm{nLockTime})
$$

where $\mathrm{version} \in \mathbb N$; $\mathrm{inputs}$ is a finite list of pairs $(o, q)$ with $o$ an outpoint and $q \in \mathbb N$; $\mathrm{vout}$ is a finite list of transaction outputs $(\mathrm{nValue} \in \mathbb Z, \mathrm{scriptPubKey})$; and $\mathrm{nLockTime} \in \mathbb N$. Equality of intents is decidable and is field-wise equality: two intents are equal if and only if their versions are equal, their input lists are equal as lists (same length, same pairs in the same order), their output lists are equal as lists, and their lock times are equal. There is no field for script signatures, witnesses, or any ledger. The lists may be empty; there are no range bounds on any natural number and no length bound on any byte string. Nothing in the structure refers to a transaction.

## Declaration 2: `intentOf`

For a transaction $\mathrm{tx} = (v, \mathrm{vin}, \mathrm{vout}, \ell)$ with $\mathrm{vin} = [i_1, \ldots, i_m]$,

$$
\mathrm{intentOf}(\mathrm{tx}) = \big(v,\ [(i_1.\mathrm{prevout}, i_1.\mathrm{nSequence}), \ldots, (i_m.\mathrm{prevout}, i_m.\mathrm{nSequence})],\ \mathrm{vout},\ \ell\big).
$$

That is: the version is copied; each input is replaced by the pair of its outpoint and its sequence number, in the same order and with the same multiplicity (duplicates are kept); the output list is copied unchanged (values and scripts included); the lock time is copied. The fields $\mathrm{scriptSig}$ and $\mathrm{witness}$ of every input are discarded. Consequently, two transactions have the same intent if and only if they have the same version, the same number of inputs with pairwise equal outpoints and sequence numbers, identical output lists, and the same lock time; they may differ arbitrarily in the $\mathrm{scriptSig}$ and $\mathrm{witness}$ of each input. For a transaction with no inputs, the intent's input list is empty. No ledger is involved and no validity is checked.

## Declaration 3: `ofIntent`

For an intent $t = (v, [(o_1, q_1), \ldots, (o_m, q_m)], \mathrm{vout}, \ell)$,

$$
\mathrm{ofIntent}(t) = \big(v,\ [(o_1, [\,], q_1, [\,]), \ldots, (o_m, [\,], q_m, [\,])],\ \mathrm{vout},\ \ell\big),
$$

a transaction whose version is $v$, whose $j$-th input has outpoint $o_j$, **empty** $\mathrm{scriptSig}$, sequence number $q_j$ and **empty** witness list, whose outputs are exactly $\mathrm{vout}$, and whose lock time is $\ell$. By construction $\mathrm{intentOf}(\mathrm{ofIntent}(t)) = t$ for every intent $t$, and for every transaction $\mathrm{tx}$, $\mathrm{ofIntent}(\mathrm{intentOf}(\mathrm{tx}))$ is $\mathrm{tx}$ with every input's $\mathrm{scriptSig}$ replaced by the empty byte string and every input's witness replaced by the empty list, all other data unchanged. No validity, well-formedness or ledger condition is imposed.

## Declaration 4: `SpendsWitnessPrograms`

For a ledger $u$ and a transaction $\mathrm{tx}$, the proposition $\mathrm{SpendsWitnessPrograms}(u, \mathrm{tx})$ states:

$$
\forall\, i \in \mathrm{tx}.\mathrm{vin}:\quad \mathrm{isWitnessProgram}\big(\mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out}.\mathrm{scriptPubKey}\big) \text{ is defined}.
$$

Unfolded: for every input $i$ that occurs in the input list of $\mathrm{tx}$ (membership, so position and repetition are irrelevant), let $s$ be the output script of the first ledger entry whose outpoint equals $i.\mathrm{prevout}$, or the empty string if there is no such entry; then $4 \le |s| \le 42$, the first byte of $s$ is $0$ or lies in $[\mathrm{0x51}, \mathrm{0x60}]$, and the second byte of $s$ equals $|s| - 2$. Edge cases: if $\mathrm{tx}.\mathrm{vin}$ is empty the proposition holds vacuously; since the empty string is not a witness program, the proposition fails for any input whose outpoint has no entry in $u$, so it entails that every input's outpoint is a key of $u$; any witness version $0$ to $16$ and any program length $2$ to $40$ is accepted, with no distinction among P2WPKH, P2WSH, Taproot or unknown versions; nothing is said about the inputs' $\mathrm{scriptSig}$, witness, sequence number, about coinbase status, about duplicate keys in $u$ (only the first match counts), or about the transaction's outputs.
