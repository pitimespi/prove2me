# Read-back: `BitcoinTaproot.sighash_type_invalid`

**Binders.** $\mathrm{tx}$ : a transaction (record with a natural-number version, a list of inputs, a list of outputs, a natural-number lock time); $\mathrm{spent}$ : a list of transaction outputs (each an integer value and a byte-string script); $\mathrm{inPos}, \mathrm{hashType}$ : natural numbers; $\mathrm{tapscript}$ : a Boolean; $\mathrm{ed}$ : an `ExecData` record (a Boolean `annexPresent`, byte strings `annexHash` and `tapleafHash`, a natural `codeseparatorPos`).

**Hypothesis.** $\neg\big(\mathrm{hashType} \le 3 \;\lor\; (0x81 \le \mathrm{hashType} \land \mathrm{hashType} \le 0x83)\big)$, i.e. $\mathrm{hashType} \notin \{0,1,2,3,0x81,0x82,0x83\}$.

**Conclusion.**

$$\mathrm{sigHashSchnorr}(\mathrm{tx}, \mathrm{spent}, \mathrm{inPos}, \mathrm{hashType}, \mathrm{tapscript}, \mathrm{ed}) = \mathrm{none}.$$

Unfolded: $\mathrm{sigHashSchnorr}$ returns an optional byte string; its very first step is the test "if not ($\mathrm{hashType} \le 3$ or $0x81 \le \mathrm{hashType} \le 0x83$) then $\mathrm{none}$", and only otherwise does it compute the tagged hash $\mathrm{tagged}(\texttt{"TapSighash"}, \cdot)$ of the BIP341-style message (epoch byte, hash-type byte, version, lock time, the optional four prevout/amount/scriptPubKey/sequence hashes, the optional outputs hash, the spend-type byte, the per-input data or input index, the optional annex hash, the optional single-output hash, and the optional tapscript extension). The hypothesis is exactly the negation of that guard, so the conclusion is that the first branch is taken.

**Edge cases the quantifiers include.** $\mathrm{hashType} = 0x80$ (excluded by the guard and therefore covered by this theorem); any $\mathrm{hashType} \ge 0x84$ including values above $255$; $\mathrm{tx}$ with no inputs or outputs; $\mathrm{inPos}$ beyond the input list; $\mathrm{spent}$ of any length, all irrelevant since the guard fails first.
