## Why the difficulty arithmetic matters

A Bitcoin block header is valid only if its hash, read as a 256-bit number, is at most a **target** encoded in the header's 32-bit `nBits` field, and only if that `nBits` is the one the consensus rules require at that height. Every 2016 blocks the required target is recomputed from the time the previous 2016 blocks took, so that blocks keep arriving roughly every ten minutes. Three pieces of arithmetic carry the whole rule: the lossy **compact encoding** between a 32-bit word and a 256-bit target (`arith_uint256::SetCompact` and `GetCompact`), the **retarget computation** with its clamped timespan and cap (`CalculateNextWorkRequired`), and the **transition check** that a header's claimed difficulty change is within the permitted range (`PermittedDifficultyTransition`), which Bitcoin Core uses to reject headers cheaply before it has the full chain. ([`pow.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp), [`arith_uint256.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp), [`CMainParams`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp))

These functions are short but intricate: the encoding has sign and overflow flags, a mantissa that must be re-normalized when its top bit is set, and a rounding step that discards low bits; the retarget multiplies inside 256 bits where a carry would be lost. A disagreement in any of them splits the network. This mission states what the pinned implementation computes and proves that its own pieces are consistent: the retarget never produces a target the transition check rejects.

## Targets, compact words, and the retarget

A **compact word** $c$ is a 32-bit value with **size** $S = \lfloor c / 2^{24} \rfloor$ (the top byte) and **mantissa** $W = c \bmod 2^{23}$ (the low 23 bits; bit 23 is the sign). Its **exact value** is $\mathrm{specTarget}(c) = W \cdot 256^{S-3}$ when $S > 3$ and $\lfloor W / 256^{3-S} \rfloor$ otherwise. `SetCompact` computes the same quantity but inside a 256-bit register, so its result is $\mathrm{setCompact}(c) = (W \ll 8(S-3)) \bmod 2^{256}$ for $S > 3$. It also reports **negative** ($W \ne 0$ and bit 23 set) and **overflow** ($W \ne 0$ and $S > 34$, or $W > 255$ and $S > 33$, or $W > 65535$ and $S > 32$).

`GetCompact` encodes a 256-bit value $v$: with $b$ the bit length of $v$ and $S = \lceil b / 8 \rceil$, the mantissa is $v$ shifted to its top three bytes (shifted left into three bytes when $S \le 3$); if bit 23 of that mantissa is set, the mantissa is divided by 256 and $S$ incremented; the word is mantissa $\lor (S \ll 24)$. Because only three bytes survive, $\mathrm{setCompact}(\mathrm{getCompact}(v))$ is $v$ rounded down.

Mainnet parameters: $\mathrm{powLimit} = 2^{224} - 1$, target timespan $T = 1{,}209{,}600$ seconds, spacing $600$ seconds, interval $2016$ blocks; minimum-difficulty blocks, no-retargeting, and BIP94 are all off.

`DeriveTarget` rejects a word that is negative, zero, overflowing, or above $\mathrm{powLimit}$; **proof of work** holds when the hash is at most the derived target. `CalculateNextWorkRequired` takes the last target $t_{\text{old}}$ and the signed elapsed time $a$ of the period, **clamps** it to $[T/4,\ 4T]$, computes $(t_{\text{old}} \cdot a \bmod 2^{256}) / T$, caps at $\mathrm{powLimit}$, and re-encodes with `GetCompact`. `PermittedDifficultyTransition` at a retarget height decodes the claimed new word and requires it to lie between the re-encoded caps of $t_{\text{old}} \cdot (T/4) / T$ and $t_{\text{old}} \cdot 4T / T$; off a retarget height it requires the word to be unchanged. `GetNextWorkRequired` returns the last word off a retarget height and calls the retarget on one.

## Formalization targets

### Goal — the retarget passes its own transition check
$$
\forall h, c_{\text{old}}, t_{\text{last}}, t_{\text{first}}:\quad
h \equiv 0 \pmod{2016}\ \wedge\ \mathrm{setCompact}(c_{\text{old}}) \le \mathrm{powLimit}
\ \Longrightarrow\
\mathrm{permittedTransition}\big(h,\ c_{\text{old}},\ \mathrm{calculateNextWork}(c_{\text{old}}, t_{\text{last}}, t_{\text{first}})\big) = \mathtt{true}.
$$
The hypothesis on $c_{\text{old}}$ holds for every target `DeriveTarget` accepts, hence for every block on a valid chain. This is `BitcoinPow.nextWork_permitted`. It is the weakest stable statement: it says only that the two functions are consistent, without fixing the rounding constants that make them so.

### Supporting milestones
1. **Overflow is exact** (`overflow_iff`): the overflow flag is set iff $\mathrm{specTarget}(c) \ge 2^{256}$.
2. **Decoding is exact without overflow** (`setCompact_eq_spec`): if the flag is clear, $\mathrm{setCompact}(c) = \mathrm{specTarget}(c)$.
3. **Proof of work** (`checkProofOfWork_iff`): acceptance iff the word is non-negative, non-overflowing, positive, at most $\mathrm{powLimit}$, and $\mathrm{hash} \le \mathrm{specTarget}(c)$.
4. **Rounding down** (`getCompact_le`): $\mathrm{setCompact}(\mathrm{getCompact}(v)) \le v$ for $v < 2^{256}$.
5. **Encoding is valid** (`getCompact_valid`): `GetCompact` never produces a negative or overflowing word.
6. **Rounding is monotone** (`round_mono`): $v \le w < 2^{256} \implies \mathrm{setCompact}(\mathrm{getCompact}(v)) \le \mathrm{setCompact}(\mathrm{getCompact}(w))$.
7. **Clamp** (`clamp_bounds`): the clamped timespan lies in $[T/4, 4T]$ for every signed input.
8. **Cap** (`nextWork_le_powLimit`): the next target decodes to at most $\mathrm{powLimit}$, for every input.
9. **Off-boundary** (`nextWork_off_boundary`): off a retarget height the required word is the last word, and that transition is permitted.

## What the result establishes

The goal is a kernel-checked consistency property of the pinned implementation: whatever the last target and the two block times, a block carrying the required `nBits` is never rejected by the cheap header-chain check. Milestones 1–3 give an exact mathematical reading of what `nBits` means on the wire, including when the implementation refuses it. Milestones 4–6 characterize the lossy re-encoding: it rounds down, keeps the top bit, and is order-preserving, which is the property the transition check silently relies on when it compares re-encoded bounds against a decoded value.

Formalizing adds two things to the C++. It makes the 256-bit wrap-around explicit: the retarget's multiplication is proved not to wrap only under the bound on the previous target, and the overflow flag is proved to be exactly the "does not fit" condition rather than an approximation. And it isolates the rounding as a function of the top-bit position, which is what the monotonicity argument needs and what the source never states.

Status: all statements are open with intentional placeholder proofs. Nothing about compiled Bitcoin Core is claimed; the value-level model of `arith_uint256` (a natural number below $2^{256}$, shifts and products reduced modulo $2^{256}$, exact division) is the documented correspondence.

## Where the obvious argument fails

The naive proof of the goal is to unfold both functions and compare. It fails at the re-encoding: the new word is $\mathrm{getCompact}(x)$ and the check compares $\mathrm{setCompact}(\mathrm{getCompact}(x))$ against $\mathrm{setCompact}(\mathrm{getCompact}(y))$ for the two bounds $y$. These are not $x$ and $y$; they are $x$ and $y$ with low bits cleared, and how many bits are cleared depends on the bit length of each. The argument needs that the rounding map is monotone across different bit lengths, which holds because the rounded value always retains the top bit — a value with fewer bits is below the top bit of any value with more.

A second trap is the mantissa normalization. When the top three bytes have bit 23 set, `GetCompact` shifts by a further byte, so the number of discarded bits is not a function of the size byte alone; the case split in the proofs is on the bit position modulo 8.

A third is `nActualTimespan`, a signed 64-bit difference that can be negative when timestamps go backwards. The clamp is stated on signed integers and the conversion to a natural number happens after it.

## Formalization scope

`arith_uint256` values are `Nat` below `width = 2 ^ 256`; `<<=` and `*=` reduce modulo `width`, `/=` is `Nat` division, `bits()` is `Nat.log2 + 1` with `0` for zero, and `GetLow64` is `% 2 ^ 64`. The `uint32_t` assignment in `GetCompact` is `% 2 ^ 32`. Compact words are `BitVec 32`; their fields are read through `toNat`. Block times are `Int`; the clamped timespan is converted with `Int.toNat` after clamping. Hashes enter `checkProofOfWork` already as natural numbers; the byte-order correspondence of `UintToArith256` is a serialization matter outside this mission. `fPowAllowMinDifficultyBlocks`, `fPowNoRetargeting`, `enforce_BIP94`, and the fuzz-determinism shortcut are fixed to their mainnet values and not modeled as parameters.

A trivializing formalization would define `permittedTransition` by calling `calculateNextWork`; both are transcribed independently from the source. Assuming the previous target is already a `GetCompact` output, which would make rounding exact, is also ruled out: the goal assumes only the `powLimit` bound.

No Mathlib is required; the development imports only `Std`. Proofs of milestones in any order are welcome, and lemmas on the rounding map are reusable by any later header-validation work.

## Selected references

- Bitcoin Core contributors. *`GetNextWorkRequired`, `CalculateNextWorkRequired`, `PermittedDifficultyTransition`, `DeriveTarget`, `CheckProofOfWorkImpl`*, `src/pow.cpp` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp)
- Bitcoin Core contributors. *`arith_uint256::SetCompact`, `arith_uint256::GetCompact`, `base_uint::operator<<=`, `operator*=`, `operator/=`, `bits`*, `src/arith_uint256.cpp` and `.h`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp)
- Bitcoin Core contributors. *`CMainParams` proof-of-work parameters*, `src/kernel/chainparams.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp)
- Satoshi Nakamoto. *Bitcoin: A Peer-to-Peer Electronic Cash System*, 2008, section 4. [Paper](https://bitcoin.org/bitcoin.pdf)
