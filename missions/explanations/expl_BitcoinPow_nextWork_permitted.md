We prove the consistency of the retarget with the transition check: for a height $h$ divisible by $2016$ and a last word $c_{\text{old}}$ whose decoded value $t_{\text{old}}$ is at most $\mathrm{powLimit}$,
$$\mathrm{permittedTransition}\big(h,\ c_{\text{old}},\ \mathrm{calculateNextWork}(c_{\text{old}}, t_{\text{last}}, t_{\text{first}})\big) = \mathtt{true}$$
for all block times.

**Idea.** Write $r = \mathrm{setCompact} \circ \mathrm{getCompact}$ for the rounding map and $\mathrm{cap}(x) = \min(x, \mathrm{powLimit})$. With $\tau$ the clamped timespan, the retarget produces the word $\mathrm{getCompact}(\mathrm{cap}(t_{\text{old}} \tau / T))$, which the check decodes to $r(\mathrm{cap}(t_{\text{old}} \tau / T))$, and compares against $r(\mathrm{cap}(t_{\text{old}} \cdot 4T / T))$ from above and $r(\mathrm{cap}(t_{\text{old}} \cdot (T/4) / T))$ from below. Since $T/4 \le \tau \le 4T$, the three capped quotients are ordered, and $r$ is monotone, so the two comparisons hold.

**Step 1 (no wrap-around).** By `BitcoinPow.clamp_bounds`, $T/4 \le \tau \le 4T < 2^{32}$. With $t_{\text{old}} \le \mathrm{powLimit} < 2^{224}$, each of the three products $t_{\text{old}} \cdot \tau$, $t_{\text{old}} \cdot 4T$, $t_{\text{old}} \cdot (T/4)$ is below $2^{224} \cdot 2^{32} = 2^{256}$, so the reductions modulo $2^{256}$ in all three computations are the identity.

**Step 2 (ordering).** $t_{\text{old}} (T/4) / T \le t_{\text{old}} \tau / T \le t_{\text{old}} \cdot 4T / T$, since multiplication by a larger factor and division by the same $T$ preserve order; and $\mathrm{cap}$ is monotone.

**Step 3 (rounding).** The capped values are at most $\mathrm{powLimit} < 2^{256}$, so `BitcoinPow.round_mono` applies: $r(\text{lower}) \le r(\text{observed}) \le r(\text{upper})$.

**Step 4.** The check is the conjunction of "not (upper $<$ observed)" and "not (lower $>$ observed)", which Step 3 gives.

The hypothesis $t_{\text{old}} \le \mathrm{powLimit}$ is exactly what `DeriveTarget` guarantees for any accepted previous header; no assumption that $c_{\text{old}}$ is itself a `GetCompact` output is used.
