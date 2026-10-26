## Why the header clock matters

Bitcoin has no trusted clock. A block's timestamp is chosen by its miner, so the consensus rules constrain it from two sides: it must exceed the **median time past** of the previous eleven blocks (`time-too-old`), and it must not run more than two hours ahead of the validating node's own clock (`time-too-new`). The median, rather than the previous block's time, is what makes the rule robust to a few manipulated timestamps, and since BIP113 the same median is the clock against which time-based lock-times are evaluated. The remaining contextual header rules fix the required difficulty bits and refuse block versions that predate the BIP34, BIP66 and BIP65 soft forks once those are active. ([`GetMedianTimePast`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h), [`ContextualCheckBlockHeader`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp), [`CMainParams`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp))

One property of this design is used everywhere but stated nowhere in the code: along any chain that obeys `time-too-old`, the median time past never decreases. It is what makes a time-based lock, once satisfied, stay satisfied. This mission transcribes the median and the contextual rules and proves that property.

## The median, the window, and the rules

A chain of ancestors is represented by the list of its block times, most recent first. The **window** is the first eleven entries (`nMedianTimeSpan`), or all of them for a shorter chain. The **median time past** sorts the window and takes the element at index $\lfloor |w| / 2 \rfloor$; for an even-length window this is the upper of the two middle elements, as the source's `pbegin[(pend - pbegin) / 2]`. For an empty chain the model returns $0$, a case the source never queries.

A **header** carries a version, a time and `nBits`. For a buried deployment, `DeploymentActiveAfter(prev)` holds when $\mathrm{prev.height} + 1$ reaches the activation height: $227{,}931$ for BIP34, $363{,}725$ for BIP66, $388{,}381$ for BIP65. The **version floor** rejects a version below 2, 3 or 4 when the corresponding deployment is active. The **contextual check** of a header against its predecessor requires: `nBits` equals the required work (supplied by the caller, as `GetNextWorkRequired` computes it in the proof-of-work development); the time strictly exceeds the predecessor's median time past; the time is at most the local clock plus $7{,}200$ seconds; and the version is not outdated. Mainnet has `enforce_BIP94 = false`, so the testnet timewarp rule is absent.

## Formalization targets

### Goal — median time past is non-decreasing along a valid chain
For a chain of block times $t_0, t_1, \dots$ (most recent first) in which every block satisfies `time-too-old` against its predecessor — $\mathrm{MTP}(t_{i+1}, t_{i+2}, \dots) < t_i$ for every $i$ — the median time past of every suffix is at most that of every shorter suffix:
$$
i \le j \;\Longrightarrow\; \mathrm{MTP}(\text{drop}_j) \le \mathrm{MTP}(\text{drop}_i).
$$
This is `BitcoinHeader.mtp_mono_chain`. It is the clock-monotonicity that BIP113 and BIP68 time locks rely on.

### Supporting milestones
1. **Window membership** (`mtp_mem_window`, `mtp_mem`): for a non-empty chain the median is one of the window's times, hence one of the chain's.
2. **Bounds** (`mtp_bounds`): the median lies between any lower and upper bound of the window.
3. **Only eleven matter** (`mtp_take`): the median of a chain equals the median of its first eleven times.
4. **One step** (`mtp_mono`): if $\mathrm{MTP}(c) < t$ then $\mathrm{MTP}(c) \le \mathrm{MTP}(t :: c)$. The heart of the goal, by a counting argument on the sorted window.
5. **Version floor** (`versionOutdated_iff`): the rejection condition as a disjunction of height thresholds.
6. **The contextual check** (`contextualCheck_iff`): acceptance as a conjunction of the four rules.
7. **Floors after activation** (`version_floor`): an accepted header has version at least 2, 3, 4 after the respective heights.

## What the result establishes

The goal is a kernel-checked statement about the transcribed median: appending blocks that pass `time-too-old` can only move the median forward. Together with the characterization of the contextual check it gives the exact semantics of Bitcoin's block clock: bounded from below by a non-decreasing median, from above by local time plus two hours.

Formalizing adds the general proof of a fact usually argued by example. The argument is a counting one: the median of a window of $n$ sorted times is the smallest value with at least $n - \lfloor n/2 \rfloor$ window elements at or above it; appending a time above the old median and dropping at most one old element keeps that count high enough, including when the window is still growing in the first ten blocks of a chain.

Not in scope, and stated as such: the computation of the required `nBits` (the proof-of-work mission), the local-clock model behind `NodeClock::now()`, checkpoints, minimum chain work, and the `CheckBlockHeader` proof-of-work test itself. Status: all statements are open with intentional placeholder proofs.

## Where the obvious argument fails

The naive argument — "the new time is larger than the median, so the median cannot fall" — overlooks that the window also loses its oldest element, which may have been one of the elements above the median. The proof must show that losing one such element and gaining one keeps at least $n - \lfloor n/2 \rfloor$ elements at or above the old median. A second subtlety is the growing window: for the first ten blocks the window length increases by one and the median index may move, so the count required changes from $n - \lfloor n/2 \rfloor$ to $(n+1) - \lfloor (n+1)/2 \rfloor$; the two cases are not the same inequality. The even-length convention (upper middle) is what makes the bookkeeping close.

## Formalization scope

Times are `Int`, as `int64_t` block times. The window is `List.take 11`, the sort is `List.mergeSort` on `≤`, and the median is `getD (length / 2) 0`. The required `nBits` is a parameter of the check. Heights are `Nat`. `enforce_BIP94`, checkpoints and minimum chain work are not modeled.

A trivializing formalization would define the median as the previous block's time, or sort with a different index convention; the definitions follow the source's sort-and-index. Assuming the chain's times are themselves sorted is ruled out: the goal assumes only the `time-too-old` rule.

No Mathlib is required; the development imports only `Std`. The counting lemmas on sorted lists are reusable for any later median-based rule.

## Selected references

- Bitcoin Core contributors. *`CBlockIndex::GetMedianTimePast`*, `src/chain.h` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h)
- Bitcoin Core contributors. *`ContextualCheckBlockHeader`*, `src/validation.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp)
- Bitcoin Core contributors. *`DeploymentActiveAfter`*, `src/deploymentstatus.h`, and `CMainParams` activation heights, `src/kernel/chainparams.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/deploymentstatus.h)
- Thomas Kerin, Mark Friedenbach. *BIP113: Median time-past as endpoint for lock-time calculations*, 2015. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0113.mediawiki)
- Gavin Andresen. *BIP34: Block v2, Height in Coinbase*, 2012; Pieter Wuille. *BIP66: Strict DER signatures*, 2015; Peter Todd. *BIP65: OP_CHECKLOCKTIMEVERIFY*, 2014. [BIPs](https://github.com/bitcoin/bips/tree/100ba872c808946155b1eeb8c4568058f2eea0a7)
