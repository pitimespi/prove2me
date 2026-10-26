SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), "
       "PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; "
       "arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), "
       "src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; "
       "CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp")
TAGS = ["bitcoin", "consensus", "proof-of-work", "difficulty", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinPow",
    "definition_title": "Compact targets, proof of work, and difficulty retargeting at mainnet parameters",
    "natural_language_statement": r"""This file transcribes the mainnet proof-of-work arithmetic of Bitcoin Core. An `arith_uint256` is modelled by its value, a natural number below $2^{256}$ (`width`); its left shift and its multiplications discard carries out of the top word, so they reduce modulo $2^{256}$, and its division is exact integer division.

**Parameters.** $\mathrm{powLimit} = 2^{224} - 1$, the target timespan $T = 14 \cdot 24 \cdot 60 \cdot 60 = 1{,}209{,}600$ seconds, the target spacing $600$ seconds, and the difficulty adjustment interval $T / 600 = 2016$ blocks.

**Compact words.** For a 32-bit word $c$: the size $S = \lfloor c / 2^{24} \rfloor$ and the mantissa $W = c \mathbin{\&} \mathtt{0x007fffff}$. `SetCompact` yields $\lfloor W / 2^{8(3-S)} \rfloor$ when $S \le 3$ and $(W \cdot 2^{8(S-3)}) \bmod 2^{256}$ otherwise. The word is **negative** when $W \ne 0$ and $c \mathbin{\&} \mathtt{0x00800000} \ne 0$; it **overflows** when $W \ne 0$ and ($S > 34$, or $W > \mathtt{0xff}$ and $S > 33$, or $W > \mathtt{0xffff}$ and $S > 32$). The **exact value** $\mathrm{specTarget}(c)$ is the same formula without the reduction modulo $2^{256}$.

**Encoding.** `bitLength` is $0$ at $0$ and $\lfloor \log_2 v \rfloor + 1$ otherwise. `GetCompact` of $v$ sets $S = \lfloor (\mathrm{bitLength}(v) + 7) / 8 \rfloor$, forms the mantissa as $((v \bmod 2^{64}) \cdot 2^{8(3-S)}) \bmod 2^{32}$ when $S \le 3$ and as $((\lfloor v / 2^{8(S-3)} \rfloor \bmod 2^{64}) \bmod 2^{32})$ otherwise; if bit 23 of the mantissa is set it divides the mantissa by $256$ and increments $S$; the result is the 32-bit word mantissa $\lor (S \cdot 2^{24})$.

**Validation.** `deriveTarget` returns the decoded value unless the word is negative, decodes to $0$, overflows, or exceeds $\mathrm{powLimit}$. `checkProofOfWork`(hash, word) holds when a target is derived and $\mathrm{hash} \le$ target. `clampTimespan` raises a signed timespan to $T/4$ and lowers it to $4T$. `calculateNextWork`(last word, last time, first time) decodes the last word, multiplies by the clamped elapsed time modulo $2^{256}$, divides by $T$, caps at $\mathrm{powLimit}$, and re-encodes. `permittedTransition`(height, old, new) at a height divisible by $2016$ requires the decoded new word to lie between the re-encoded caps of old $\cdot (T/4) / T$ and old $\cdot 4T / T$ (products modulo $2^{256}$); at other heights it requires old $=$ new. `nextWorkRequired` returns the last word unless the next height is divisible by $2016$, in which case it retargets.

These definitions fix the meaning of `nBits` on the wire and the retarget rule, as inputs for header validation.

**Formalization Note.** Compact words are `BitVec 32` read through `toNat`; values are `Nat`; block times are `Int`, converted with `Int.toNat` only after clamping. `fPowAllowMinDifficultyBlocks`, `fPowNoRetargeting`, and `enforce_BIP94` are fixed to `false` as on mainnet. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinPow.overflow_iff": dict(
    title="The compact overflow flag is exactly the 256-bit bound",
    nl=r"""For every 32-bit word $c$ with size $S$ and mantissa $W$,
$$\mathrm{compactOverflow}(c) = \mathtt{true} \iff 2^{256} \le \mathrm{specTarget}(c),$$
where $\mathrm{specTarget}(c) = W \cdot 256^{S-3}$ for $S > 3$ and $\lfloor W / 256^{3-S} \rfloor$ otherwise. The flag computed by `SetCompact` from the three threshold tests on $S$ and $W$ is therefore not an approximation: it is set precisely when the encoded value does not fit in 256 bits. Both directions are asserted, for all $2^{32}$ words.""",
    ms=("SetCompact — overflow flag is exact", "Prove the three-clause overflow test is equivalent to specTarget ≥ 2^256.")),
"BitcoinPow.setCompact_eq_spec": dict(
    title="Without overflow, SetCompact decodes the exact value",
    nl=r"""For every 32-bit word $c$ whose overflow flag is clear,
$$\mathrm{setCompact}(c) = \mathrm{specTarget}(c).$$
The 256-bit register arithmetic of `SetCompact` (a left shift that drops carried-out bits) loses nothing when the flag is clear, so the decoded target is the mathematical value $W \cdot 256^{S-3}$ (or $\lfloor W / 256^{3-S} \rfloor$ for $S \le 3$).""",
    ms=("SetCompact — exact decoding", "Show the modular shift equals the exact value whenever the overflow flag is clear.")),
"BitcoinPow.checkProofOfWork_iff": dict(
    title="Proof-of-work acceptance, characterized",
    nl=r"""For every hash value $h \in \mathbb N$ and every 32-bit word $c$,
$$\mathrm{checkProofOfWork}(h, c) = \mathtt{true} \iff \neg\mathrm{negative}(c) \wedge \neg\mathrm{overflow}(c) \wedge 0 < \mathrm{specTarget}(c) \wedge \mathrm{specTarget}(c) \le 2^{224}-1 \wedge h \le \mathrm{specTarget}(c).$$
This is `DeriveTarget` followed by the comparison in `CheckProofOfWorkImpl`, restated on the exact value of the word. A header passes exactly when its `nBits` is a well-formed, in-range, positive target and the hash is at most that target.""",
    ms=("CheckProofOfWork — acceptance condition", "Characterize acceptance via DeriveTarget's four rejections and the hash comparison, on the exact target.")),
"BitcoinPow.getCompact_le": dict(
    title="Re-encoding a target rounds it down",
    nl=r"""For every $v < 2^{256}$,
$$\mathrm{setCompact}(\mathrm{getCompact}(v)) \le v.$$
`GetCompact` keeps only the top three bytes of $v$ (fewer when the mantissa's bit 23 forces a further byte shift), so decoding the result gives $v$ with some low bits cleared, never more than $v$. The case $v = 0$ is included and gives $0$.""",
    ms=("GetCompact — rounds down", "Prove SetCompact ∘ GetCompact never exceeds its input below 2^256.")),
"BitcoinPow.getCompact_valid": dict(
    title="GetCompact never produces a negative or overflowing word",
    nl=r"""For every $v < 2^{256}$, the word $\mathrm{getCompact}(v)$ has its negative flag clear and its overflow flag clear. The mantissa it assembles is below $2^{23}$ after the bit-23 normalization, so the sign bit is never set, and its size byte is at most $33$ with a mantissa below $2^{16}$ in that extreme case, so none of the overflow thresholds is met.""",
    ms=("GetCompact — output is a valid word", "Show the assembled word is non-negative and non-overflowing for every 256-bit input.")),
"BitcoinPow.round_mono": dict(
    title="Compact rounding is order-preserving",
    nl=r"""For all $v \le w$ with $w < 2^{256}$,
$$\mathrm{setCompact}(\mathrm{getCompact}(v)) \le \mathrm{setCompact}(\mathrm{getCompact}(w)).$$
Decoding after encoding clears a number of low bits that depends only on the position of the top bit; values with the same top bit are rounded on the same grid, and a value with a lower top bit is below the retained top bit of the other. This is the property `PermittedDifficultyTransition` relies on when it compares re-encoded bounds with a decoded word.""",
    ms=("GetCompact — rounding is monotone", "Prove monotonicity of SetCompact ∘ GetCompact via the top-bit-dependent grid.")),
"BitcoinPow.clamp_bounds": dict(
    title="The retarget timespan is clamped to [T/4, 4T]",
    nl=r"""For every signed elapsed time $a \in \mathbb Z$, the clamped timespan used by `CalculateNextWorkRequired` satisfies
$$\frac{T}{4} = 302{,}400 \le \mathrm{clampTimespan}(a) \le 4T = 4{,}838{,}400,$$
with $T = 1{,}209{,}600$. Negative inputs, which arise when timestamps go backwards, are raised to $T/4$; this bounds every difficulty change to a factor of four in either direction.""",
    ms=("CalculateNextWorkRequired — timespan clamp", "Bound the clamped signed timespan in [T/4, 4T].")),
"BitcoinPow.nextWork_le_powLimit": dict(
    title="The next required target never exceeds the proof-of-work limit",
    nl=r"""For every last word $c$ and all block times $t_{\text{last}}, t_{\text{first}} \in \mathbb Z$,
$$\mathrm{setCompact}\big(\mathrm{calculateNextWork}(c, t_{\text{last}}, t_{\text{first}})\big) \le 2^{224} - 1.$$
The retarget caps its result at $\mathrm{powLimit}$ before re-encoding, and re-encoding rounds down, so the decoded next target is at most the limit. No hypothesis is placed on $c$.""",
    ms=("CalculateNextWorkRequired — capped at powLimit", "Combine the cap with rounding-down to bound the decoded next target.")),
"BitcoinPow.nextWork_off_boundary": dict(
    title="Off a retarget boundary the required word is unchanged and permitted",
    nl=r"""For every last height $h$ with $h + 1 \not\equiv 0 \pmod{2016}$, every last word $c$, and all block times,
$$\mathrm{nextWorkRequired}(h, c, t_{\text{last}}, t_{\text{first}}) = c \qquad\text{and}\qquad \mathrm{permittedTransition}(h+1, c, c) = \mathtt{true}.$$
On mainnet, where minimum-difficulty blocks are disabled, `GetNextWorkRequired` returns the previous word between retargets, and `PermittedDifficultyTransition` accepts an unchanged word there.""",
    ms=("GetNextWorkRequired — no change between retargets", "Show the off-boundary branch returns the last word and that this transition is permitted.")),
"BitcoinPow.nextWork_permitted": dict(
    title="The retarget always passes the permitted-transition check",
    nl=r"""For every height $h$ divisible by $2016$, every last word $c_{\text{old}}$ whose decoded value is at most $\mathrm{powLimit} = 2^{224} - 1$, and all block times $t_{\text{last}}, t_{\text{first}} \in \mathbb Z$,
$$\mathrm{permittedTransition}\big(h,\ c_{\text{old}},\ \mathrm{calculateNextWork}(c_{\text{old}}, t_{\text{last}}, t_{\text{first}})\big) = \mathtt{true}.$$
Here `calculateNextWork` is the mainnet `CalculateNextWorkRequired`: decode, multiply by the clamped elapsed time inside 256 bits, divide by $T$, cap, re-encode. `permittedTransition` is the mainnet `PermittedDifficultyTransition`: the decoded new word must lie between the re-encoded caps of $c_{\text{old}} \cdot (T/4) / T$ and $c_{\text{old}} \cdot 4T / T$.

The hypothesis on $c_{\text{old}}$ holds for every word `DeriveTarget` accepts, hence for every block on a valid chain; under it none of the three 256-bit products wraps. The statement is the consistency of the two functions: a header carrying the required `nBits` is never rejected by the cheap header-chain check, whatever the timestamps.

**Formalization Note.** The proof reduces to the monotonicity of the rounding map $\mathrm{setCompact} \circ \mathrm{getCompact}$ and to the ordering of the three capped quotients; no assumption that $c_{\text{old}}$ is itself a `GetCompact` output is made.""",
    ms=None),
}
ORDER = ["BitcoinPow.overflow_iff", "BitcoinPow.setCompact_eq_spec", "BitcoinPow.checkProofOfWork_iff",
         "BitcoinPow.getCompact_le", "BitcoinPow.getCompact_valid", "BitcoinPow.round_mono",
         "BitcoinPow.clamp_bounds", "BitcoinPow.nextWork_le_powLimit", "BitcoinPow.nextWork_off_boundary",
         "BitcoinPow.nextWork_permitted"]
