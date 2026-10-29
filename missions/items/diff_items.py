SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, "
       "src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; "
       "arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)")
TAGS = ["bitcoin", "consensus", "difficulty", "retarget", "timewarp", "proof-of-work", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinDifficulty",
    "definition_title": "The raw next target of a retarget period and the target after a sequence of periods",
    "natural_language_statement": r"""Two names over the proof-of-work mission's `BitcoinPow`; nothing is re-transcribed.

**`rawNextTarget t lastTime firstTime`** — the value `CalculateNextWorkRequired` encodes: the last target $t$ times the clamped actual timespan (`clampTimespan (lastTime − firstTime)`, between `targetTimespan/4` and `4·targetTimespan`), taken modulo $2^{256}$, divided by `targetTimespan` (1,209,600 s), and capped at `powLimit`. `calculateNextWork bits lastTime firstTime` is by definition `getCompact (rawNextTarget (setCompact bits) lastTime firstTime)`.

**`targetAfter bits periods`** — the encoded target after applying `calculateNextWork` once per element of `periods`, a list of (last time, first time) pairs, starting from `bits`.

**Formalization Note.** `setCompact`, `getCompact`, `clampTimespan`, `calculateNextWork`, `nextWorkRequired`, `powLimit`, `width` are the proof-of-work mission's; `ChainState.requiredBits` is the block mission's `GetNextWorkRequired` on a chain. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinDifficulty.no_wrap": dict(title="A valid target times the clamped timespan never wraps around 2^256",
    nl=r"""For $t \le$ `powLimit` ($2^{224}-1$) and $ts \le 4{,}838{,}400$ (four times the target timespan): $t \cdot ts < 2^{256}$. The modular multiplication of `arith_uint256` is exact on every valid input.""",
    ms=None),
"BitcoinDifficulty.raw_target_bounds": dict(title="The raw next target is between a quarter and four times the last target",
    nl=r"""For a last target $t \le$ `powLimit` and any timestamps: `rawNextTarget t lastTime firstTime` $\le 4t$, and either the cap binds (the raw target is `powLimit`) or `rawNextTarget t lastTime firstTime` $\ge \lfloor t/4 \rfloor$. From the clamp bounds of the proof-of-work mission and the exact arithmetic.""",
    ms=("The clamp bounds the ratio", "`clamp_bounds`, `no_wrap`, and integer division monotonicity.")),
"BitcoinDifficulty.encoded_target_upper": dict(title="The encoded target at most quadruples per period",
    nl=r"""For `setCompact bits ≤ powLimit` and any timestamps: `setCompact (calculateNextWork bits lastTime firstTime) ≤ 4 · setCompact bits`. The compact encoding rounds down (`getCompact_le`).""",
    ms=None),
"BitcoinDifficulty.encoded_target_lower": dict(title="The encoded target drops by at most a factor of four per period, up to rounding",
    nl=r"""For `setCompact bits ≤ powLimit` and any timestamps: `setCompact (getCompact (setCompact bits / 4)) ≤ setCompact (calculateNextWork bits lastTime firstTime)`. The new target is at least the compact encoding of a quarter of the old one (`round_mono`).""",
    ms=("Rounding is monotone", "`round_mono` on the raw lower bound; the capped case compares a quarter of a valid target with `powLimit`.")),
"BitcoinDifficulty.target_after_upper": dict(title="Over m periods the target grows by at most 4^m",
    nl=r"""For `setCompact bits ≤ powLimit` and any list of $m$ periods with any timestamps: `setCompact (targetAfter bits periods) ≤ 4^m · setCompact bits`.""",
    ms=None),
"BitcoinDifficulty.target_after_le_powLimit": dict(title="The target never exceeds powLimit",
    nl=r"""For `setCompact bits ≤ powLimit` and any list of periods: `setCompact (targetAfter bits periods) ≤ powLimit`.""",
    ms=None),
"BitcoinDifficulty.requiredBits_le": dict(title="Timewarp bound: the next required target is at most four times the tip's",
    nl=r"""For any chain state whose tip target is valid (`setCompact (tip bits) ≤ powLimit`): `setCompact S.requiredBits ≤ 4 · setCompact (tip bits)`, whether or not the next block is at a retarget boundary, whatever the timestamps of the period's blocks. This is the whole of what an adversary who controls timestamps can do to the difficulty in one period under the mainnet rules: lower it by at most a factor of four (and, by `encoded_target_lower`, raise it by at most a factor of four); the known timewarp attack is the repetition of this bound across periods, which `target_after_upper` quantifies.""",
    ms=None),
}
ORDER = ["BitcoinDifficulty.no_wrap", "BitcoinDifficulty.raw_target_bounds", "BitcoinDifficulty.encoded_target_upper",
         "BitcoinDifficulty.encoded_target_lower", "BitcoinDifficulty.target_after_upper",
         "BitcoinDifficulty.target_after_le_powLimit", "BitcoinDifficulty.requiredBits_le"]
