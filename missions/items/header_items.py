SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CBlockIndex::GetMedianTimePast and nMedianTimeSpan, MAX_FUTURE_BLOCK_TIME, src/chain.h: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/chain.h; "
       "ContextualCheckBlockHeader, src/validation.cpp (lines 4091-4128): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; "
       "DeploymentActiveAfter (buried), src/deploymentstatus.h; BIP34Height, BIP66Height, BIP65Height in CMainParams, src/kernel/chainparams.cpp")
TAGS = ["bitcoin", "consensus", "block-header", "median-time-past", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinHeader",
    "definition_title": "Median time past and the contextual block-header rules",
    "natural_language_statement": r"""A chain of ancestors is the list of its block times $t_0, t_1, \dots$, most recent first. The **window** is the first $\mathrm{nMedianTimeSpan} = 11$ times. The **median time past** of a chain sorts its window by $\le$ and returns the element at index $\lfloor |w| / 2 \rfloor$, or $0$ for an empty chain:
$$\mathrm{MTP}(t_0, t_1, \dots) = \mathrm{sort}(t_0, \dots, t_{\min(10,\,n-1)})\big[\lfloor \min(11, n) / 2 \rfloor\big].$$

A **header** has a version, a time and `nBits`. $\mathrm{MAX\_FUTURE\_BLOCK\_TIME} = 7{,}200$ seconds. The mainnet activation heights are $\mathrm{BIP34Height} = 227{,}931$, $\mathrm{BIP66Height} = 363{,}725$, $\mathrm{BIP65Height} = 388{,}381$. `activeAfter`(prevHeight, h) holds when $h \le \mathrm{prevHeight} + 1$, as `DeploymentActiveAfter` for a buried deployment. `versionOutdated`(v, prevHeight) holds when $v < 2$ with BIP34 active, or $v < 3$ with BIP66 active, or $v < 4$ with BIP65 active.

`contextualCheck`(header, prevHeight, prevTimes, required, now) is `ContextualCheckBlockHeader` at mainnet parameters: `nBits` $=$ required, $\mathrm{MTP}(\text{prevTimes}) <$ time, time $\le$ now $+ 7{,}200$, and the version is not outdated. The required `nBits` is supplied by the caller, as `GetNextWorkRequired` computes it.

**Formalization Note.** Times are `Int`; the sort is `List.mergeSort` on `≤` and the index access is `getD` with default `0`. `enforce_BIP94` is `false` as on mainnet, so the testnet timewarp rule is absent. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinHeader.mtp_mem_window": dict(title="The median time past is one of the window's times",
    nl=r"""For every non-empty chain of times, $\mathrm{MTP}(\text{times}) \in \mathrm{timeWindow}(\text{times})$: the median is an element of the (at most eleven) most recent block times, not an average or an interpolation.""",
    ms=("MTP — member of the window", "Show the sorted window's element at index |w|/2 is an element of the window.")),
"BitcoinHeader.mtp_mem": dict(title="The median time past is one of the chain's times",
    nl=r"""For every non-empty chain of times, $\mathrm{MTP}(\text{times}) \in \text{times}$. Immediate from window membership, since the window is a prefix of the chain.""",
    ms=("MTP — member of the chain", "Transfer window membership to the chain.")),
"BitcoinHeader.mtp_bounds": dict(title="The median time past lies within any bounds of the window",
    nl=r"""For every non-empty chain and integers $lo \le hi$ such that every time $t$ in the window satisfies $lo \le t \le hi$, also $lo \le \mathrm{MTP}(\text{times}) \le hi$. In particular the median is between the oldest and the newest time of the window.""",
    ms=("MTP — bounded by the window", "Derive bounds from window membership.")),
"BitcoinHeader.mtp_take": dict(title="Only the eleven most recent times determine the median",
    nl=r"""For every chain of times, $\mathrm{MTP}(\text{times}) = \mathrm{MTP}(\text{first eleven of times})$: block times older than the eleventh ancestor have no influence on the median time past.""",
    ms=("MTP — depends on eleven times only", "Show taking the window twice is taking it once.")),
"BitcoinHeader.mtp_mono": dict(title="Appending a block that passes time-too-old never lowers the median",
    nl=r"""For every chain of times $c$ and time $t$ with $\mathrm{MTP}(c) < t$,
$$\mathrm{MTP}(c) \le \mathrm{MTP}(t :: c).$$
The new window is $t$ followed by the ten most recent times of $c$: it gains $t$, which lies above the old median, and loses at most the eleventh time of the old window. For a chain shorter than eleven blocks the window grows instead and the median index may move; the inequality holds in both cases.""",
    ms=("MTP — one-step monotonicity", "Counting argument on the sorted window: at least n − n/2 elements at or above the old median survive.")),
"BitcoinHeader.versionOutdated_iff": dict(title="The outdated-version condition as height thresholds",
    nl=r"""For every version $v$ and previous height $p$, $\mathrm{versionOutdated}(v, p)$ holds exactly when
$$(v < 2 \wedge 227{,}931 \le p + 1) \;\vee\; (v < 3 \wedge 363{,}725 \le p + 1) \;\vee\; (v < 4 \wedge 388{,}381 \le p + 1),$$
the BIP34, BIP66 and BIP65 version floors at their mainnet activation heights.""",
    ms=("Version floors — characterization", "Unfold the Boolean rejection test into the three threshold disjuncts.")),
"BitcoinHeader.contextualCheck_iff": dict(title="Acceptance by the contextual header check, characterized",
    nl=r"""For every header $h$, previous height $p$, chain of previous times, required `nBits` $r$ and local time $now$, the contextual check accepts exactly when
$$h.\mathrm{bits} = r \;\wedge\; \mathrm{MTP}(\text{prevTimes}) < h.\mathrm{time} \;\wedge\; h.\mathrm{time} \le now + 7{,}200 \;\wedge\; \neg\,\mathrm{outdated},$$
where outdated is the disjunction of the three version-floor conditions. These are the `bad-diffbits`, `time-too-old`, `time-too-new` and `bad-version` rejections of `ContextualCheckBlockHeader`.""",
    ms=("ContextualCheckBlockHeader — characterization", "Read the four Boolean conjuncts back as propositions.")),
"BitcoinHeader.version_floor": dict(title="Accepted headers respect the version floors after activation",
    nl=r"""For every header accepted by the contextual check against previous height $p$: if $227{,}931 \le p + 1$ then its version is at least 2; if $363{,}725 \le p + 1$ then at least 3; if $388{,}381 \le p + 1$ then at least 4.""",
    ms=("Version floors — consequence for accepted headers", "Derive the three floors from the characterization.")),
"BitcoinHeader.mtp_mono_chain": dict(title="Median time past is non-decreasing along a chain obeying time-too-old",
    nl=r"""Let $t_0, t_1, \dots, t_{n-1}$ be the block times of a chain, most recent first, such that every block satisfies the `time-too-old` rule against its predecessor:
$$\forall i < n,\quad \mathrm{MTP}(t_{i+1}, t_{i+2}, \dots) < t_i .$$
Then for all $i \le j \le n$,
$$\mathrm{MTP}(t_j, t_{j+1}, \dots) \le \mathrm{MTP}(t_i, t_{i+1}, \dots):$$
the median time past of any ancestor is at most that of any descendant. Here $\mathrm{MTP}$ is the transcription of `GetMedianTimePast`: the element at index $\lfloor |w|/2 \rfloor$ of the sorted window of at most eleven most recent times.

This is the clock-monotonicity property that time-based lock-times (BIP113, BIP68) rely on: once the chain's median time has passed a threshold, it never falls back below it. The chain's times themselves need not be increasing; only the median rule is assumed.

**Formalization Note.** The statement is about suffixes `times.drop i` of the time list; the hypothesis is the `time-too-old` conjunct of `ContextualCheckBlockHeader` at every position.""",
    ms=None),
}
ORDER = ["BitcoinHeader.mtp_mem_window","BitcoinHeader.mtp_mem","BitcoinHeader.mtp_bounds","BitcoinHeader.mtp_take",
         "BitcoinHeader.mtp_mono","BitcoinHeader.versionOutdated_iff","BitcoinHeader.contextualCheck_iff",
         "BitcoinHeader.version_floor","BitcoinHeader.mtp_mono_chain"]
