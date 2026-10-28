# Read-back: `BitcoinBlockV2.bip30_history`

**Binders.** $S$ is a chain state (a list of headers $S.\mathit{headers}$ and a ledger); $\mathit{height}$ is a natural number; $\mathit{hash}$ is a byte string (list of 8-bit words, any length). No hypotheses.

**Conclusion.** The following are equivalent:

*Left:* $\mathrm{bip30Checked}(S, \mathit{height}, \mathit{hash}) = \mathrm{false}$. Unfolding: let $A$ ("BIP34 ancestor") be the Boolean that is true exactly when the list $S.\mathit{headers}$ has an element $h$ at index $227931$ (`BitcoinHeader.BIP34Height`) and $\mathrm{headerHash}(h)$ — $\mathrm{hash256}$ of the serialized header — equals the fixed 32-byte literal `bip34Hash`; then
$$\mathrm{bip30Checked}(S, \mathit{height}, \mathit{hash}) = \big(\lnot\mathrm{isBIP30Repeat}(\mathit{height}, \mathit{hash}) \land \lnot A\big) \lor (1\,983\,702 \le \mathit{height}),$$
so the left side says this Boolean is false.

*Right:* $\mathit{height} < 1\,983\,702$ (the constant `BIP34_IMPLIES_BIP30_LIMIT`) **and** at least one of:
- $\mathrm{isBIP30Repeat}(\mathit{height}, \mathit{hash}) = \mathrm{true}$, i.e. ($\mathit{height} = 91842$ and $\mathit{hash}$ equals the literal `bip30Repeat91842`) or ($\mathit{height} = 91880$ and $\mathit{hash}$ equals the literal `bip30Repeat91880`);
- there exists a header $h$ such that the element of $S.\mathit{headers}$ at index $227931$ exists and equals $h$, and $\mathrm{headerHash}(h) = $ `bip34Hash`.

**Edge cases silently included:** $S.\mathit{headers}$ shorter than $227932$ elements (no ancestor, second disjunct false); $\mathit{hash}$ of a length other than $32$ (never equal to the literals); $\mathit{height}$ is not required to be related to $S$ in any way.
