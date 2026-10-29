SRC = ("J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 "
       "(full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; "
       "Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork")
TAGS = ["bitcoin", "nakamoto-consensus", "backbone", "common-prefix", "chain-quality", "chain-growth", "garay-kiayias-leonardos", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "BitcoinBackbone",
    "definition_title": "The synchronous backbone model: executions, valid chains, typical executions",
    "natural_language_statement": r"""The deterministic core of Garay, Kiayias and Leonardos's synchronous analysis, over Mathlib.

**`Block`** — `honest p r` (found by honest party $p$ in round $r$) or `adv r j` (the $j$-th adversarial block of round $r$); `Block.round`, `Block.isHonest`. **`Chain`** — a list of blocks oldest first (genesis omitted); `Chain.work` is its length; `Chain.upTo C t` the prefix of blocks of round $\le t$.

**`Execution`** — a trace: the number $n$ of honest parties, `mined p r` (whether $p$ found a block in round $r$), `Z r` (the adversary's block count in round $r$), `base p r` (the chain $p$ adopted at the start of round $r$ after `maxvalid`), `advParent r j` (the chain the adversary's $j$-th block of round $r$ extends). Derived: **`chain p r`** (the end-of-round chain: `base`, plus $p$'s own block if mined; the empty chain at round 0), **`honestCount r`**, **`X r`** (1 iff some honest block in round $r$), **`Y r`** (1 iff exactly one honest block in round $r$).

**`Extends E parent B`** and **`ValidChain E C`** — every block of $C$ sits on exactly the chain its creator extended (the hash-chain abstraction: a block determines its ancestry). **`Legal E`** — the rules of the synchronous model: nothing mined in round 0; adopted chains are valid and made of earlier rounds' blocks; every honest chain of round $r$ is at most as long as what any honest party adopts in round $r+1$ (`maxvalid` over delivered chains); the adversary extends valid chains of rounds $\le r$ (rushing). **`Typical E λ`** — on every window $[a, b]$ with $a + λ \le b$, the adversary's blocks in $[a, b]$ are strictly fewer than the uniquely successful rounds strictly inside $(a, b)$. **`advBlocks E a b`** — the adversarial blocks of rounds $a$ to $b$ as a finite set.

**Formalization Note.** Imports Mathlib and the block mission's `BitcoinBlockV2`. `Typical` is the paper's typical-execution property combined with honest majority, assumed rather than derived from Chernoff bounds; boundary rounds are credited to the adversary.""",
}

THEOREMS = {
"BitcoinBackbone.chainWork_const_bits": dict(title="At constant difficulty, Core's chain work is the number of blocks times one block's proof",
    nl=r"""For a block-mission chain state all of whose headers carry the same `bits`: `S.chainWork = S.headers.length * blockProof bits`. The link between the paper's "length" and Core's `nChainWork`.""", ms=None),
"BitcoinBackbone.chain_growth": dict(title="Chain growth (Lemma 7): an honest chain grows by at least the successful rounds",
    nl=r"""For a legal execution, honest parties $p, q$ and rounds $r < s$: `(chain p r).length + ∑_{i ∈ [r+1, s)} X i ≤ (chain q s).length`. Every successful round adds a block to every honest party's chain by the next round.""", ms=None),
"BitcoinBackbone.chain_growth_self": dict(title="Chain growth for one party",
    nl=r"""The same bound with $q = p$ and $r \le s$.""", ms=None),
"BitcoinBackbone.uniquely_successful_height": dict(title="A uniquely successful round pins the honest block at its height (Lemma 14)",
    nl=r"""If round $i$ is uniquely successful with honest miner $m$, then in any valid chain the block at height `(base m i).length` (0-based index), if honest, is $m$'s block of round $i$.""", ms=None),
"BitcoinBackbone.common_prefix_private": dict(title="A private fork loses (the core of Lemma 15)",
    nl=r"""For a legal, typical execution and honest party $p$ at round $r$: any valid chain $D$ of rounds $\le r$ that forks from an honest block of round $r_0$ (or from genesis) and is adversarial above the fork, with $r_0 + λ \le r$, is strictly shorter than `chain p r`.""",
    ms=("The pairing argument", "Each uniquely successful round inside the window contributes a distinct height the private chain must match with an adversarial block.")),
"BitcoinBackbone.common_prefix_rounds": dict(title="Common prefix, round form (Lemma 15 and Theorem 16)",
    nl=r"""For a legal, typical execution, honest $p_1, p_2$, rounds $r_1 \le r_2$ and a window $λ \le w \le r_1$: the blocks of `chain p₁ r₁` of round $\le r_1 - w$ form a prefix of `chain p₂ r₂`.""",
    ms=("Induction over rounds", "`common_prefix_private` with `Nat.le_induction`.")),
"BitcoinBackbone.common_prefix": dict(title="Common prefix (Theorem 16): dropping 2λ blocks gives a prefix of every later honest chain",
    nl=r"""For a legal, typical execution, honest $p_1, p_2$ and rounds $r_1 \le r_2$: `(chain p₁ r₁).take ((chain p₁ r₁).length - 2λ)` is a prefix of `chain p₂ r₂`. The paper's $k = 2λf$ becomes $2λ$ here.""", ms=None),
"BitcoinBackbone.chain_quality": dict(title="Chain quality: every λ consecutive blocks of an honest chain contain an honest block",
    nl=r"""For a legal, typical execution, honest $p$, round $r$ and position $u$ with $u + λ \le$ `(chain p r).length`: among the $λ$ blocks of `chain p r` starting at position $u$ there is an honest one. The weak ($μ > 0$) form of the paper's chain-quality theorem.""", ms=None),
}
ORDER = ["BitcoinBackbone.chainWork_const_bits", "BitcoinBackbone.chain_growth", "BitcoinBackbone.chain_growth_self",
         "BitcoinBackbone.uniquely_successful_height", "BitcoinBackbone.common_prefix_private", "BitcoinBackbone.common_prefix_rounds",
         "BitcoinBackbone.common_prefix", "BitcoinBackbone.chain_quality"]
