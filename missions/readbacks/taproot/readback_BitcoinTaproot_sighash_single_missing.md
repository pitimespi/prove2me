# Read-back: `BitcoinTaproot.sighash_single_missing`

**Binders.** $\mathrm{tx}$ : a transaction (natural version, list of inputs $\mathrm{vin}$, list of outputs $\mathrm{vout}$, natural lock time); $\mathrm{spent}$ : a list of outputs; $\mathrm{inPos}, \mathrm{hashType}$ : natural numbers; $\mathrm{tapscript}$ : a Boolean; $\mathrm{ed}$ : an `ExecData` record (`annexPresent` : Boolean, `annexHash`, `tapleafHash` : byte strings, `codeseparatorPos` : natural).

**Hypotheses.**
1. $\mathrm{hashType} \le 3 \;\lor\; (0x81 \le \mathrm{hashType} \land \mathrm{hashType} \le 0x83)$;
2. $\mathrm{hashType} \,\&\, 3 = 3$ (bitwise AND on naturals);
3. $|\mathrm{tx}.\mathrm{vout}| \le \mathrm{inPos}$.

**Conclusion.**

$$\mathrm{sigHashSchnorr}(\mathrm{tx}, \mathrm{spent}, \mathrm{inPos}, \mathrm{hashType}, \mathrm{tapscript}, \mathrm{ed}) = \mathrm{none}.$$

Unfolded: $\mathrm{sigHashSchnorr}$ first tests the guard of hypothesis 1 (it passes). It then sets the output type $o := 1$ if $\mathrm{hashType} = 0$, else $o := \mathrm{hashType} \,\&\, 3$. By hypothesis 2, $\mathrm{hashType} \neq 0$ (since $0 \,\&\, 3 = 0$) and $o = 3$, the file's `SIGHASH_SINGLE`. Combined with hypothesis 1 this means $\mathrm{hashType} \in \{3, 0x83\}$. When $o = 3$ the function computes the "single output" component as: $\mathrm{none}$ if $|\mathrm{vout}| \le \mathrm{inPos}$, otherwise the SHA-256 of the serialized output $\mathrm{vout}_{\mathrm{inPos}}$. When that component is $\mathrm{none}$ the whole function returns $\mathrm{none}$ without computing the tagged hash. Hypothesis 3 makes that component $\mathrm{none}$.

**Edge cases the quantifiers include.** $\mathrm{vout}$ empty (then every $\mathrm{inPos}$ qualifies); $\mathrm{inPos}$ also beyond $\mathrm{vin}$ (irrelevant, the default input is never reached); $\mathrm{spent}$ of any length; the Boolean $\mathrm{tapscript}$ and the record $\mathrm{ed}$ are arbitrary and unused.
