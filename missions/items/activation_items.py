SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; "
       "DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; "
       "CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; "
       "LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478")
TAGS = ["bitcoin", "consensus", "soft-fork-activation", "script-flags", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinActivation",
    "definition_title": "Buried deployments, script-verification flags by height, and the two exception blocks",
    "natural_language_statement": r"""A **buried deployment** is one of `HEIGHTINCB` (BIP34), `CLTV` (BIP65), `DERSIG` (BIP66), `CSV`, `SEGWIT`, with mainnet activation heights $227{,}931$, $388{,}381$, $363{,}725$, $419{,}328$, $481{,}824$ (`deploymentHeight`). `activeAt`(height, dep) holds when the deployment height is at most the block height, as `DeploymentActiveAt`; `activeAfter`(prevHeight, dep) holds when it is at most prevHeight $+ 1$, as `DeploymentActiveAfter`.

A **flag set** is a record of seven Booleans: `p2sh`, `witness`, `taproot`, `dersig`, `cltv`, `csv`, `nulldummy`. `noFlags` has none; `baseFlags` has `p2sh`, `witness`, `taproot`. A block's **exception status** is `none`, `bip16Block` (the hash-keyed P2SH violation) or `taprootBlock` (the hash-keyed Taproot violation); `exceptionBase` yields `baseFlags`, `noFlags`, and `p2sh`+`witness` respectively.

`blockScriptFlags`(height, exc) is `GetBlockScriptFlags`: the exception base, with `dersig`, `cltv`, `csv`, `nulldummy` each OR-ed with `activeAt` of `DERSIG`, `CLTV`, `CSV`, `SEGWIT` at the height. `ScriptFlags.le` is pointwise inclusion: every flag true in the first is true in the second.

$\mathrm{LOCKTIME\_VERIFY\_SEQUENCE} = 1$, and `lockTimeFlags`(height) is that value when `CSV` is active at the height and $0$ otherwise, as `nLockTimeFlags` in `ConnectBlock`.

**Formalization Note.** The exception table is modeled by the three-valued classification rather than a hash lookup. Versionbits deployments are not modeled, since the pinned source consults none for mainnet consensus flags. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinActivation.activeAt_mono": dict(title="Buried-deployment activation is monotone in height",
    nl=r"""For every buried deployment and heights $h_1 \le h_2$, if the deployment is active at $h_1$ then it is active at $h_2$: a buried deployment, once active, stays active.""",
    ms=("DeploymentActiveAt — monotone", "Immediate from the height comparison.")),
"BitcoinActivation.activeAfter_eq": dict(title="Active-after is active-at the next height",
    nl=r"""For every buried deployment and previous height $p$, `activeAfter`$(p, dep)$ equals `activeAt`$(p+1, dep)$: `DeploymentActiveAfter(pindexPrev)` is `DeploymentActiveAt` of the block that follows.""",
    ms=("DeploymentActiveAfter — relation to ActiveAt", "Definitional.")),
"BitcoinActivation.flags_before_bip66": dict(title="Before BIP66 an ordinary block enforces only the base flags",
    nl=r"""For every height $h < 363{,}725$, the flags of an ordinary block are exactly `P2SH | WITNESS | TAPROOT`: none of the height-gated rules is active yet.""",
    ms=("GetBlockScriptFlags — before BIP66", "Evaluate the four activation tests below the first threshold.")),
"BitcoinActivation.flags_after_segwit": dict(title="From SegWit on an ordinary block enforces every flag",
    nl=r"""For every height $h \ge 481{,}824$, the flags of an ordinary block are all seven: `P2SH`, `WITNESS`, `TAPROOT`, `DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY`, `NULLDUMMY`.""",
    ms=("GetBlockScriptFlags — from SegWit on", "Evaluate the four activation tests above the last threshold.")),
"BitcoinActivation.flags_order": dict(title="The height-gated flags activate in a fixed order",
    nl=r"""For every height, in the flags of an ordinary block: `CHECKLOCKTIMEVERIFY` implies `DERSIG`, `CHECKSEQUENCEVERIFY` implies `CHECKLOCKTIMEVERIFY`, and `NULLDUMMY` implies `CHECKSEQUENCEVERIFY` — the order $363{,}725 < 388{,}381 < 419{,}328 < 481{,}824$ of the activation heights.""",
    ms=("GetBlockScriptFlags — activation order", "Derive the implications from the ordering of the four heights.")),
"BitcoinActivation.bip16_exception": dict(title="The BIP16 exception block enforces no script flags",
    nl=r"""For every height $h < 363{,}725$ — in particular the exception block's height $170{,}060$ — the flags of the BIP16 exception block are `SCRIPT_VERIFY_NONE`: the exception base is empty and no height-gated rule is active.""",
    ms=("Exception — BIP16 block", "Evaluate the exception base and the activation tests.")),
"BitcoinActivation.taproot_exception": dict(title="The Taproot exception block enforces every flag except Taproot",
    nl=r"""For every height $h \ge 481{,}824$ — in particular the exception block's height $692{,}261$ — the flags of the Taproot exception block are `P2SH | WITNESS | DERSIG | CHECKLOCKTIMEVERIFY | CHECKSEQUENCEVERIFY | NULLDUMMY`: the exception removes `TAPROOT` only, and the height-gated rules are all active.""",
    ms=("Exception — Taproot block", "Evaluate the exception base and the activation tests.")),
"BitcoinActivation.exception_le": dict(title="An exception never adds a rule",
    nl=r"""For every height and exception status, the flags of the block are included in the flags an ordinary block at that height would have: the exception table only ever removes rules.""",
    ms=("Exceptions — only remove", "Case split on the exception status.")),
"BitcoinActivation.lockTimeFlags_eq": dict(title="Sequence locks are verified exactly from CSV activation",
    nl=r"""For every height $h$, `lockTimeFlags`$(h)$ is `LOCKTIME_VERIFY_SEQUENCE` when $419{,}328 \le h$ and $0$ otherwise: BIP68 relative locks are enforced from the CSV activation height on.""",
    ms=("nLockTimeFlags — CSV threshold", "Definitional unfolding of the CSV activation test.")),
"BitcoinActivation.flags_mono": dict(title="Soft forks only add script rules",
    nl=r"""For all heights $h_1 \le h_2$, every script-verification flag enforced for an ordinary block at height $h_1$ is enforced at height $h_2$:
$$\mathrm{blockScriptFlags}(h_1, \mathrm{none}) \subseteq \mathrm{blockScriptFlags}(h_2, \mathrm{none}),$$
where inclusion is pointwise over the seven flags `P2SH`, `WITNESS`, `TAPROOT`, `DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY`, `NULLDUMMY`, and `blockScriptFlags` is the transcription of `GetBlockScriptFlags` at mainnet heights.

This is the structural content of buried deployments: the ruleset in force is a non-decreasing function of height, so "the rules at height $h$" is well defined and a rule, once enforced, is never relaxed for ordinary blocks. The two hash-keyed exception blocks are the only departures, and are covered by separate theorems.""",
    ms=None),
}
ORDER = ["BitcoinActivation.activeAt_mono","BitcoinActivation.activeAfter_eq","BitcoinActivation.flags_before_bip66",
         "BitcoinActivation.flags_after_segwit","BitcoinActivation.flags_order","BitcoinActivation.bip16_exception",
         "BitcoinActivation.taproot_exception","BitcoinActivation.exception_le","BitcoinActivation.lockTimeFlags_eq",
         "BitcoinActivation.flags_mono"]
