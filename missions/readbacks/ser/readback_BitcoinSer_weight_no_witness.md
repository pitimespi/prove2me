# Read-back: `BitcoinSer.weight_no_witness`

**Binders and hypothesis.** A transaction record $tx$ and the hypothesis
$$h : \texttt{hasWitness}(tx) = \mathrm{false},$$
i.e. the Boolean "some input has a non-empty witness list" evaluates to false — every input of $tx$ has an empty witness list (vacuously so if $tx$ has no inputs). No well-formedness is assumed; field values may be arbitrary.

**Conclusion.** A conjunction of two equalities:
$$\texttt{serTx}\;\mathrm{true}\;tx = \texttt{serTx}\;\mathrm{false}\;tx \qquad\text{and}\qquad \texttt{txWeight}(tx) = \texttt{WITNESS\_SCALE\_FACTOR} \cdot |\texttt{serTx}\;\mathrm{false}\;tx| ,$$
where $\texttt{WITNESS\_SCALE\_FACTOR} = 4$.

**Unfolding the first conjunct.** $\texttt{serTx}\;aw\;tx$ computes $\phi = 1$ if $aw \wedge \texttt{hasWitness}(tx)$, else $0$; the output is the 4-byte version, then $[0, \phi]$ only when $\phi \ne 0$, then the CompactSize-prefixed inputs, the CompactSize-prefixed outputs, then (only when $\phi \ne 0$) one CompactSize-prefixed witness stack per input, then the 4-byte lock time. Under the hypothesis, $\phi = 0$ for both $aw = \mathrm{true}$ and $aw = \mathrm{false}$, so the marker bytes and the witness section are absent in both and the two byte strings coincide. The first conjunct says exactly this: with no non-empty witness, the "allow witness" mode produces the legacy encoding.

**Unfolding the second conjunct.** $\texttt{txWeight}(tx) = |\texttt{serTx}\;\mathrm{false}\;tx| \cdot (\texttt{WITNESS\_SCALE\_FACTOR} - 1) + |\texttt{serTx}\;\mathrm{true}\;tx| = 3\,|\texttt{serTx}\;\mathrm{false}\;tx| + |\texttt{serTx}\;\mathrm{true}\;tx|$ (the subtraction $4 - 1$ is on natural numbers and is $3$). Using the first conjunct, the second summand equals $|\texttt{serTx}\;\mathrm{false}\;tx|$, giving $3L + L = 4L$ with $L = |\texttt{serTx}\;\mathrm{false}\;tx|$. The conclusion writes the right side as $\texttt{WITNESS\_SCALE\_FACTOR} \cdot L$, i.e. $4L$, with the constant on the left of the product.

Edge cases covered: $tx$ with no inputs (then $\texttt{hasWitness}$ is false automatically and the hypothesis holds); $tx$ whose inputs all have witness $[\,]$; arbitrary out-of-range version/lock time (truncated identically on both sides).

**What is not said.** Nothing when $\texttt{hasWitness}(tx)$ is true: no formula for the weight of a witness-bearing transaction, and no claim that the two serializations differ. Nothing about $\texttt{blockWeight}$, $\texttt{MAX\_BLOCK\_WEIGHT}$, or any bound on the weight. Nothing about $\texttt{wtxid}$ (the definition makes $\texttt{wtxid} = \texttt{txid}$ in this case, but the theorem does not mention it). No lengths are computed: the theorem relates the weight to the serialized length but does not say what that length is. It is a two-part equality under the single Boolean hypothesis.
