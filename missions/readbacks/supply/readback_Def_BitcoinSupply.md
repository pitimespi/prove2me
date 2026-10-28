# Read-back: `Def_BitcoinSupply.lean` (namespace `BitcoinSupply`)

Throughout, a **ledger** is a finite list of pairs $(k, c)$ where $k$ is an *outpoint* (a pair of a byte list $k.\mathrm{hash}$ and a natural number $k.n$) and $c$ is a *coin*: a triple $(c.\mathrm{out},\ c.\mathrm{height},\ c.\mathrm{isCoinbase})$ with $c.\mathrm{out}$ an *output* (an integer value $c.\mathrm{out}.\mathrm{nValue} \in \mathbb{Z}$ and a byte-list script), $c.\mathrm{height} \in \mathbb{N}$, and $c.\mathrm{isCoinbase}$ a boolean. The type places no restriction on the list: keys may repeat, values may be negative or arbitrarily large, and the list may be empty.

The constant $\mathrm{MAX\_MONEY}$ used in this file is the integer $2{,}100{,}000{,}000{,}000{,}000$ (the block mission's integer constant, not the subsidy mission's natural-number constant; the two are numerically equal).

---

## `totalValue : Ledger → ℤ`

For a ledger $u = [(k_1,c_1), \dots, (k_m,c_m)]$,
$$\mathrm{totalValue}(u) \;=\; \sum_{j=1}^{m} c_j.\mathrm{out}.\mathrm{nValue},$$
an integer. The empty ledger has total value $0$. Every entry of the list contributes, including entries whose key coincides with an earlier entry's key (no de-duplication is performed), entries whose value is negative, and entries whose script is unspendable; the coin's height and coinbase flag play no role.

---

## `ValuesInRange : Ledger → Prop`

For a ledger $u$, $\mathrm{ValuesInRange}(u)$ is the proposition
$$\forall\, (k, c) \in u:\quad 0 \le c.\mathrm{out}.\mathrm{nValue} \;\wedge\; c.\mathrm{out}.\mathrm{nValue} \le 2{,}100{,}000{,}000{,}000{,}000 .$$
Both bounds are non-strict. It is vacuously true for the empty ledger. It says nothing about the sum of the values, about repeated keys, or about any field other than the value.

---

## `issued : ℕ → ℤ`

For $n \in \mathbb{N}$, $\mathrm{issued}(n)$ is the natural number $\mathrm{issuedBelow}(n)$ of the subsidy mission, cast to an integer, where
$$\mathrm{issuedBelow}(0) = 0,\qquad \mathrm{issuedBelow}(n+1) = \mathrm{issuedBelow}(n) + \mathrm{coreSubsidy}(n),$$
so that
$$\mathrm{issued}(n) \;=\; \sum_{h=0}^{n-1} \mathrm{coreSubsidy}(h) .$$
Here, for a height $h \in \mathbb{N}$, with $q = \lfloor h / 210{,}000 \rfloor$,
$$\mathrm{coreSubsidy}(h) \;=\; \begin{cases} 0 & \text{if } q \ge 64,\\[2pt] \left\lfloor \dfrac{5{,}000{,}000{,}000}{2^{\,q}} \right\rfloor & \text{otherwise} \end{cases}$$
(the right shift of the natural number $50 \cdot 10^{8}$ by $q$ bits). Note that for $q \ge 33$ the shifted value is already $0$, so the $q \ge 64$ branch does not change any value. In particular $\mathrm{issued}(0) = 0$, $\mathrm{issued}(1) = 5{,}000{,}000{,}000$, and $\mathrm{issued}$ is non-decreasing in $n$ and eventually constant. The argument $n$ is a count of blocks, not a largest height: the sum runs over heights $0, \dots, n-1$.

---

## `genesisSubsidy : ℤ`

The constant $\mathrm{genesisSubsidy} = \mathrm{coreSubsidy}(0)$ cast to an integer, i.e.
$$\mathrm{genesisSubsidy} = 5{,}000{,}000{,}000 .$$
It is a bare numeric constant; nothing in this definition refers to the genesis block, its coinbase, or any ledger.
