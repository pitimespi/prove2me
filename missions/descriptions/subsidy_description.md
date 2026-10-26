## Why the issuance schedule matters

Every Bitcoin block may create new coins through its coinbase transaction, and the amount it may create is fixed by consensus: a **block subsidy** that starts at fifty bitcoin and halves every 210,000 blocks, plus the fees of the block's other transactions. The schedule is the mechanism behind the often-quoted cap of twenty-one million bitcoin, yet the cap appears nowhere in the code as a rule. What the code enforces is the per-block subsidy, computed by `GetBlockSubsidy` in `validation.cpp`, and the check in `ConnectBlock` that the coinbase pays no more than fees plus subsidy. The cap is a consequence, and the only place a number near it appears is `MAX_MONEY`, a sanity bound on individual amounts whose comment says explicitly that it is "*not* the total money supply". ([`GetBlockSubsidy`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833), [`amount.h`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h), [`CMainParams`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp))

This mission makes the consequence a theorem about the pinned implementation: the sum of the subsidies of all blocks, at every height the chain can reach, is strictly below `MAX_MONEY`, and in fact equals a specific constant once the subsidy reaches zero. It is the arithmetic core of the ledger-supply results that a whole-consensus development will need, and it is small enough to be verified completely.

## The subsidy function and its schedule

Amounts are counted in satoshi. One bitcoin is $\mathrm{COIN} = 10^8$ satoshi and $\mathrm{MAX\_MONEY} = 21{,}000{,}000 \cdot \mathrm{COIN}$. The mainnet **halving interval** is $I = 210{,}000$ blocks.

The **Core subsidy** at height $h \in \mathbb N$ is the transcription of `GetBlockSubsidy`: with $k = \lfloor h / I \rfloor$ the number of halvings, the subsidy is $0$ if $k \ge 64$, and otherwise $(50 \cdot \mathrm{COIN}) \gg k$, the right shift of the initial subsidy by $k$ bits. Heights are nonnegative integers in the source, and the shift acts on the nonnegative value $50 \cdot \mathrm{COIN}$, so natural numbers represent both exactly. The explicit `halvings >= 64` branch exists because a shift by 64 or more is undefined in C++.

The **declarative schedule** is $\mathrm{specSubsidy}(h) = \lfloor 50 \cdot \mathrm{COIN} \,/\, 2^{\lfloor h/I \rfloor} \rfloor$: fifty bitcoin, halved once per interval with the remainder discarded.

**Issuance** below height $n$ is the running sum of Core subsidies, $\mathrm{issuedBelow}(0) = 0$ and $\mathrm{issuedBelow}(n+1) = \mathrm{issuedBelow}(n) + \mathrm{coreSubsidy}(n)$. The **interval sum** $\mathrm{intervalSum}(m) = \sum_{j < m} \lfloor 50 \cdot \mathrm{COIN} / 2^j \rfloor$ collects one subsidy per interval. The **zero height** is $33 I = 6{,}930{,}000$.

## Formalization targets

### Goal — issuance below the cap
$$
\forall n,\quad \mathrm{issuedBelow}(n) < \mathrm{MAX\_MONEY}.
$$
This is the weakest stable statement: it survives any refinement of the constants below and is what a supply argument downstream consumes. It is `BitcoinSubsidy.issuance_bound`.

### Supporting milestones
1. **Core equals schedule** (`core_eq_spec`): $\mathrm{coreSubsidy}(h) = \mathrm{specSubsidy}(h)$ for every $h$, including heights where the `64` branch fires.
2. **Amount range** (`subsidy_le_maxMoney`): $\mathrm{coreSubsidy}(h) \le \mathrm{MAX\_MONEY}$, so the subsidy is always a valid amount.
3. **Monotone decrease** (`subsidy_antitone`): $h_1 \le h_2 \implies \mathrm{coreSubsidy}(h_2) \le \mathrm{coreSubsidy}(h_1)$.
4. **Halving step** (`subsidy_halving`): $\mathrm{coreSubsidy}(h + I) = \lfloor \mathrm{coreSubsidy}(h) / 2 \rfloor$.
5. **Exact extinction** (`subsidy_zero_iff`): $\mathrm{coreSubsidy}(h) = 0 \iff h \ge 33 I$. The subsidy is one satoshi throughout the thirty-third interval and zero from the thirty-fourth on.
6. **Exact total** (`issuance_total`): $\mathrm{issuedBelow}(33 I) = 2{,}099{,}999{,}997{,}690{,}000$ satoshi.
7. **Bounded by the total** (`issuance_le_total`): $\mathrm{issuedBelow}(n) \le 2{,}099{,}999{,}997{,}690{,}000$ for every $n$.

## What the result establishes

The goal is a kernel-checked statement that the implemented subsidy schedule can never issue `MAX_MONEY` or more in total, for any chain length, and the milestones pin down the exact figure: $20{,}999{,}999.9769$ bitcoin, $2{,}310{,}000$ satoshi short of twenty-one million because of the floor in each halving. Milestones 1 and 5 record two facts about the implementation worth having on the record: the `halvings >= 64` guard is never the reason the subsidy is zero (division already gives zero from 33 halvings), and the subsidy is exactly one satoshi for the 210,000 blocks of the thirty-third interval.

What formalizing adds is separation of the arithmetic from the accounting. The supply bound on an actual ledger needs more than this: fees move value without creating it, unclaimed coinbase value is never issued, and outputs can be made unspendable. Those are statements about the UTXO transition and belong to a separate mission; this one supplies the exact upper bound they will cite.

Status: every statement is open with an intentional placeholder proof. The constants and the shift are checked against the pinned source; nothing about compiled Bitcoin Core is claimed.

## Where the obvious argument fails

The naive proof of the goal is to evaluate the sum: unfold `issuedBelow` at $6{,}930{,}000$ and compute. The kernel cannot do that in reasonable time, and the statement is for every $n$, not one. The argument has to be structural: within an interval the subsidy is constant, so the sum over the first $m$ intervals is $I \cdot \mathrm{intervalSum}(m)$; past the zero height every term vanishes, so the sum is stable; and for $n$ below the zero height the sum is bounded by monotonicity. Only the thirty-three-term interval sum is evaluated by computation.

A second trap is the shift. $(50 \cdot \mathrm{COIN}) \gg k$ equals $\lfloor 50 \cdot \mathrm{COIN} / 2^k \rfloor$ only because the value is nonnegative; the schedule theorem is what licenses replacing the bitwise operation with division everywhere else.

## Formalization scope

Heights, amounts and counts are `Nat`. `coreSubsidy` uses Lean's `>>>` on `Nat`, which is exact division by $2^k$. `issuedBelow` and `intervalSum` are structurally recursive, so proofs about them are inductions on the height or the interval count. No Mathlib is required; the development imports only `Std`.

A trivializing formalization would define `issuedBelow` through `specSubsidy` and prove the bound about the schedule alone; the definition is fixed on `coreSubsidy` so that the result is about the transcription. Weakening the goal to a bound at one fixed height is out of scope.

Out of scope: the coinbase check `GetValueOut() > blockReward` in `ConnectBlock`, fee accounting, and the UTXO set. Those take this mission's definitions as inputs. Proofs of the milestones in any order are welcome, as are reusable lemmas on `issuedBelow`.

## Selected references

- Bitcoin Core contributors. *`GetBlockSubsidy`*, `src/validation.cpp` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833)
- Bitcoin Core contributors. *`COIN`, `MAX_MONEY`, `MoneyRange`*, `src/consensus/amount.h`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h)
- Bitcoin Core contributors. *`CMainParams::nSubsidyHalvingInterval`*, `src/kernel/chainparams.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp)
- Bitcoin Core contributors. *Coinbase amount check in `Chainstate::ConnectBlock`*, `src/validation.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2608)
- Satoshi Nakamoto. *Bitcoin: A Peer-to-Peer Electronic Cash System*, 2008. [Paper](https://bitcoin.org/bitcoin.pdf)
