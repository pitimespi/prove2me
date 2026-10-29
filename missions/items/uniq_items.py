SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), "
       "src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; "
       "CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34")
TAGS = ["bitcoin", "consensus", "bip30", "bip34", "uniqueness", "coinbase", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinUniqueness",
    "definition_title": "The BIP30 scan condition, freshness of a block's outputs, and the coinbase scriptSig",
    "natural_language_statement": r"""Three names over the block mission's `BitcoinBlockV2` and the reorganization mission's `BitcoinReorg`; nothing is re-transcribed.

**`coinbaseScriptSig b`** — the `scriptSig` of the first input of the first transaction of a block (defaults: the genesis coinbase, an empty input).

**`ScanRuns S b`** — `ConnectBlock` performs the BIP30 scan when connecting `b` to `S`: `fEnforceBIP30 || nHeight >= BIP34_IMPLIES_BIP30_LIMIT`, i.e. the block mission's `bip30Checked` at the next height and the block's hash.

**`FreshOutputs u b`** — for every transaction of `b` and every output index below its output count, the ledger `u` holds no coin at that outpoint.

**Formalization Note.** `validate`, `Reachable`, `heightScript` (`CScript() << nHeight`), `bip30Checked`, `isBIP30Repeat` are the block mission's; `connectChain` is the reorganization mission's; `pushBytes` is the signature mission's push encoder and `serialize` the Script mission's `CScriptNum::serialize`. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinUniqueness.pushBytes_prefix": dict(title="A push is never a proper prefix of another push",
    nl=r"""For byte strings $d, d'$ shorter than $2^{32}$: if the canonical push of $d$ is a prefix of the canonical push of $d'$ then $d = d'$. The first byte fixes the encoding class (direct, `PUSHDATA1/2/4`) and, with the length field, the length.""",
    ms=("Push encodings are prefix-free", "Case analysis on the four length classes; the little-endian length fields are injective below their range.")),
"BitcoinUniqueness.heightScript_prefix": dict(title="BIP34 height pushes are prefix-free",
    nl=r"""For heights $a, b < 2^{31}$: if `CScript() << a` is a prefix of `CScript() << b` then $a = b$. The single-byte forms (`OP_0`, `OP_1`..`OP_16`) never prefix a data push and vice versa, and data pushes are prefix-free with `CScriptNum::serialize` injective.""",
    ms=("Height pushes are prefix-free", "`pushBytes_prefix`, `serialize_roundtrip`, and the byte ranges of the small-number opcodes.")),
"BitcoinUniqueness.scan_freshness": dict(title="Where the BIP30 scan runs, an accepted block's outputs are fresh",
    nl=r"""For a reachable state, an accepted block (not hashing to the genesis hash) and `ScanRuns S b`: `FreshOutputs S.utxo b`. From the acceptance theorem: the ledger predicate's BIP30 clause.""",
    ms=None),
"BitcoinUniqueness.scan_runs_late": dict(title="From height 1,983,702 the scan always runs",
    nl=r"""If `BIP34_IMPLIES_BIP30_LIMIT ≤ S.nextHeight` then `ScanRuns S b` for every block `b`.""",
    ms=None),
"BitcoinUniqueness.scan_runs_early": dict(title="Before the BIP34 block can be an ancestor, the scan runs except at the two repeats",
    nl=r"""If the state has at most 227,931 headers and the block is not one of the two `IsBIP30Repeat` blocks at its height, then `ScanRuns S b`.""",
    ms=None),
"BitcoinUniqueness.coinbase_height_prefix": dict(title="An accepted post-BIP34 block's coinbase starts with its height push",
    nl=r"""For a reachable state at next height $\ge 227{,}931$ and an accepted block: `heightScript S.nextHeight` is a prefix of `coinbaseScriptSig b`. From the acceptance theorem's contextual clause (`ContextualCheckBlock`'s `bad-cb-height`).""",
    ms=("The BIP34 clause of ContextSpec", "`DeploymentActiveAfter(HEIGHTINCB)` holds at the next height; the coinbase is the first transaction and has an input.")),
"BitcoinUniqueness.coinbases_distinct": dict(title="Blocks accepted at different post-BIP34 heights have different coinbase scriptSigs",
    nl=r"""For two reachable states at next heights $h_1 \ne h_2$, both $\ge 227{,}931$ and $< 2^{31}$, and blocks accepted on them: the coinbase `scriptSig`s differ. Each starts with its own height push, and if both pushes were prefixes of the same bytes the shorter would prefix the longer, forcing equal heights.""",
    ms=("Two height pushes prefixing the same bytes", "`heightScript_prefix` applied to the shorter of the two.")),
"BitcoinUniqueness.chain_coinbases_distinct": dict(title="Along a post-BIP34 chain the coinbase scriptSigs are pairwise distinct",
    nl=r"""For a reachable state at next height $\ge 227{,}931$ and a chain `bs` connected to it (`connectChain`) staying below height $2^{31}$: the list of coinbase `scriptSig`s of the blocks of `bs` has no duplicates. Hence no two post-BIP34 blocks of one chain have the same coinbase *transaction* — the structural half of the argument that lets `ConnectBlock` skip the BIP30 scan. What this does not establish, and the model cannot: that two different transactions never share a txid (collision resistance of SHA-256d), and that no pre-BIP34 coinbase `scriptSig` happens to start with a height push of a height below 1,983,702 (a fact about the historical chain's data, which is why Core re-enables the scan from that height).""",
    ms=None),
}
ORDER = ["BitcoinUniqueness.pushBytes_prefix", "BitcoinUniqueness.heightScript_prefix", "BitcoinUniqueness.scan_freshness",
         "BitcoinUniqueness.scan_runs_late", "BitcoinUniqueness.scan_runs_early", "BitcoinUniqueness.coinbase_height_prefix",
         "BitcoinUniqueness.coinbases_distinct", "BitcoinUniqueness.chain_coinbases_distinct"]
