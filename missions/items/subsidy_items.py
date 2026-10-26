SRC_SUB = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: "
           "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; "
           "COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; "
           "nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp")
TAGS = ["bitcoin", "consensus", "block-subsidy", "issuance", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinSubsidy",
    "definition_title": "Block subsidy, issuance schedule, and cumulative issuance",
    "natural_language_statement": r"""Amounts are counted in satoshi. One bitcoin is $\mathrm{COIN} = 10^{8}$ satoshi and $\mathrm{MAX\_MONEY} = 21{,}000{,}000 \cdot \mathrm{COIN} = 2.1 \times 10^{15}$ satoshi. The mainnet halving interval is $I = 210{,}000$ blocks.

The **Core subsidy** at a block height $h \in \mathbb N$ transcribes `GetBlockSubsidy` at mainnet parameters. With $k = \lfloor h / I \rfloor$ halvings, the subsidy is $0$ when $k \ge 64$, and otherwise the right shift $(50 \cdot \mathrm{COIN}) \gg k$. Heights are nonnegative in the source and the shifted value is nonnegative, so natural numbers represent both exactly; the explicit $k \ge 64$ branch mirrors the source's guard against an undefined shift.

The **declarative schedule** is
$$\mathrm{specSubsidy}(h) = \left\lfloor \frac{50 \cdot \mathrm{COIN}}{2^{\lfloor h / I \rfloor}} \right\rfloor ,$$
fifty bitcoin halved once per interval with the remainder discarded.

**Cumulative issuance** below height $n$ is the running sum $\mathrm{issuedBelow}(0) = 0$, $\mathrm{issuedBelow}(n+1) = \mathrm{issuedBelow}(n) + \mathrm{coreSubsidy}(n)$. The **interval sum** $\mathrm{intervalSum}(m) = \sum_{j<m} \lfloor 50 \cdot \mathrm{COIN} / 2^{j} \rfloor$ collects one subsidy per interval. The **zero height** is $33 I = 6{,}930{,}000$, the first height whose subsidy the theorems show to be zero.

These definitions are the inputs for the issuance theorems and for any later ledger-supply argument, which will cite the cumulative issuance as its upper bound.

**Formalization Note.** All quantities are natural numbers. The shift is Lean's `>>>` on `Nat`, which is exact division by a power of two; the recursive definitions are structural so that proofs proceed by induction on height or interval count. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinSubsidy.core_eq_spec": dict(
    title="Core block subsidy equals the halving schedule",
    nl=r"""For every block height $h \in \mathbb N$, the transcription of `GetBlockSubsidy` and the declarative halving schedule agree:
$$\mathrm{coreSubsidy}(h) = \left\lfloor \frac{50 \cdot \mathrm{COIN}}{2^{\lfloor h / 210000 \rfloor}} \right\rfloor .$$
On the left, $\mathrm{coreSubsidy}$ returns $0$ when $\lfloor h/210000 \rfloor \ge 64$ and otherwise right-shifts $50 \cdot \mathrm{COIN} = 5 \times 10^{9}$ by that many bits; on the right the schedule divides by the corresponding power of two.

The statement covers every height, including those where the source's `halvings >= 64` guard fires, where it asserts that the division already yields zero. It is the bridge that lets the remaining results be proved about the schedule and transferred to the implementation.""",
    ms=("GetBlockSubsidy — schedule correspondence", "Show the shift-based implementation equals the division-based schedule at every height, including the halvings ≥ 64 branch.")),
"BitcoinSubsidy.subsidy_le_maxMoney": dict(
    title="The block subsidy is always a valid amount",
    nl=r"""For every block height $h \in \mathbb N$,
$$\mathrm{coreSubsidy}(h) \le \mathrm{MAX\_MONEY} = 2.1 \times 10^{15}.$$
Since amounts are natural numbers here, this is exactly the `MoneyRange` condition of `consensus/amount.h` applied to the subsidy: it is nonnegative and at most `MAX_MONEY`. The bound is far from tight, as the subsidy never exceeds $5 \times 10^{9}$ satoshi; the point is that the subsidy term of the block reward is always a representable, in-range amount.""",
    ms=("GetBlockSubsidy — MoneyRange", "Bound the subsidy by MAX_MONEY at every height.")),
"BitcoinSubsidy.subsidy_antitone": dict(
    title="The block subsidy never increases with height",
    nl=r"""For all block heights $h_1 \le h_2$,
$$\mathrm{coreSubsidy}(h_2) \le \mathrm{coreSubsidy}(h_1).$$
The subsidy is a non-increasing function of height: it is constant within each interval of $210{,}000$ blocks and drops at each interval boundary. The inequality is not strict, since consecutive heights within an interval share the same subsidy.""",
    ms=("GetBlockSubsidy — monotonicity", "Prove the subsidy is non-increasing in height.")),
"BitcoinSubsidy.subsidy_halving": dict(
    title="Advancing one interval halves the subsidy",
    nl=r"""For every block height $h \in \mathbb N$,
$$\mathrm{coreSubsidy}(h + 210000) = \left\lfloor \frac{\mathrm{coreSubsidy}(h)}{2} \right\rfloor .$$
Moving forward by exactly one halving interval halves the subsidy, with the remainder discarded. This is the defining recurrence of the schedule stated directly on the implementation; iterating it from height $0$ reproduces the sequence $50, 25, 12.5, \dots$ bitcoin.""",
    ms=("GetBlockSubsidy — halving recurrence", "Prove the one-interval shift halves the subsidy with floor.")),
"BitcoinSubsidy.subsidy_zero_iff": dict(
    title="The subsidy is zero exactly from the thirty-third halving",
    nl=r"""For every block height $h \in \mathbb N$,
$$\mathrm{coreSubsidy}(h) = 0 \iff h \ge 33 \cdot 210000 = 6{,}930{,}000 .$$
Both directions are asserted. Below the zero height the subsidy is positive; in particular it equals one satoshi throughout the thirty-third interval (heights $6{,}720{,}000$ to $6{,}929{,}999$), since $\lfloor 5 \times 10^{9} / 2^{32} \rfloor = 1$. From the zero height on it is zero, since $5 \times 10^{9} < 2^{33}$. The source's `halvings >= 64` guard is therefore never the operative reason for a zero subsidy.""",
    ms=("GetBlockSubsidy — exact extinction height", "Characterize zero subsidy as height ≥ 6,930,000, both directions.")),
"BitcoinSubsidy.issuance_total": dict(
    title="Total issuance at the zero height",
    nl=r"""The cumulative subsidy of all blocks below the zero height is
$$\mathrm{issuedBelow}(6{,}930{,}000) = 2{,}099{,}999{,}997{,}690{,}000 \text{ satoshi},$$
that is, $20{,}999{,}999.9769$ bitcoin. Equivalently, $210{,}000 \cdot \sum_{j=0}^{32} \lfloor 5 \times 10^{9} / 2^{j} \rfloor = 210{,}000 \cdot 9{,}999{,}999{,}989$.

The figure falls $2{,}310{,}000$ satoshi short of twenty-one million bitcoin because each halving discards a remainder. Together with the extinction result it gives the exact total the schedule can ever issue.""",
    ms=("Issuance — exact total", "Compute the cumulative subsidy up to the zero height via the per-interval decomposition.")),
"BitcoinSubsidy.issuance_le_total": dict(
    title="Cumulative issuance is bounded by the final total",
    nl=r"""For every $n \in \mathbb N$,
$$\mathrm{issuedBelow}(n) \le 2{,}099{,}999{,}997{,}690{,}000 .$$
The cumulative subsidy below any height is at most the total reached at the zero height: below it the sum is still growing, and from it on every further term is zero, so the sum is constant. This is the exact form of the supply bound for the subsidy schedule alone.""",
    ms=("Issuance — bounded by the total", "Prove issuedBelow is monotone and stable past the zero height, hence bounded by the exact total.")),
"BitcoinSubsidy.issuance_bound": dict(
    title="Total block subsidy stays below MAX_MONEY",
    nl=r"""For every $n \in \mathbb N$, the cumulative subsidy of all blocks at heights below $n$ is strictly less than the consensus amount bound:
$$\mathrm{issuedBelow}(n) < \mathrm{MAX\_MONEY} = 21{,}000{,}000 \cdot 10^{8}.$$
Here $\mathrm{issuedBelow}(n) = \sum_{h < n} \mathrm{coreSubsidy}(h)$ with $\mathrm{coreSubsidy}$ the transcription of `GetBlockSubsidy` at mainnet parameters.

This is the arithmetic content of the twenty-one-million cap: no chain length, however long, lets the subsidy schedule issue `MAX_MONEY` or more. It is stated as a strict inequality against the named constant rather than as an exact value, so that it is the weakest statement a ledger-supply argument needs and remains true under any refinement of the exact total.

**Formalization Note.** The bound concerns the subsidy schedule only. Fees, unclaimed coinbase value and unspendable outputs are matters for the UTXO transition and are not modeled here.""",
    ms=None),
}
ORDER = ["BitcoinSubsidy.core_eq_spec", "BitcoinSubsidy.subsidy_le_maxMoney", "BitcoinSubsidy.subsidy_antitone",
         "BitcoinSubsidy.subsidy_halving", "BitcoinSubsidy.subsidy_zero_iff", "BitcoinSubsidy.issuance_total",
         "BitcoinSubsidy.issuance_le_total", "BitcoinSubsidy.issuance_bound"]
