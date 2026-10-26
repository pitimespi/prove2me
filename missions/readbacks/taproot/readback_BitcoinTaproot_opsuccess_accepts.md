# Read-back: `BitcoinTaproot.opsuccess_accepts`

**Binders.** $c$ : a `TapCtx` record (flags `cltv`, `csv`, `nulldummy`; transaction; list of spent outputs; input index); $\mathrm{ed}$ : an `ExecData` record; $\mathrm{stack}$ : a list of byte strings; $\mathrm{script}$ : a byte string; $\mathrm{weight} \in \mathbb{Z}$.

**Hypothesis.** $\mathrm{opSuccessScan}(|\mathrm{script}|, \mathrm{script}) = \mathrm{some}(\mathrm{true})$.

Here $\mathrm{opSuccessScan}(f, s)$ is a fuel-bounded scan of the byte string $s$: if $s$ is empty the result is $\mathrm{some}(\mathrm{false})$; else if the fuel $f$ is $0$ the result is $\mathrm{none}$; else one instruction is read from the front of $s$ by the bundle's `GetOp` (bytes $\le \texttt{0x4e}$ are pushes — a direct push of $o$ bytes for $o < \texttt{0x4c}$, or `PUSHDATA1/2/4` with a 1/2/4-byte little-endian length — and reading fails, giving $\mathrm{none}$, if the length prefix or the push data runs past the end; any byte $> \texttt{0x4e}$ is a non-push opcode). On a push the scan continues on the remainder with fuel $f - 1$; on an opcode byte $o$, if $\mathrm{isOpSuccess}(o)$ holds the result is $\mathrm{some}(\mathrm{true})$, otherwise the scan continues. $\mathrm{isOpSuccess}(o)$ holds iff $o \in \{80, 98\} \cup [126,129] \cup [131,134] \cup [137,138] \cup [141,142] \cup [149,153] \cup [187,254]$. So the hypothesis says: reading $\mathrm{script}$ instruction by instruction from the start, an `OP_SUCCESSx` byte is reached before any malformed push and before the end.

**Conclusion.**

$$\mathrm{executeTapscript}(c, \mathrm{ed}, \mathrm{stack}, \mathrm{script}, \mathrm{weight}) = \mathrm{true}.$$

Unfolded: $\mathrm{executeTapscript}$ first evaluates $\mathrm{opSuccessScan}(|\mathrm{script}|, \mathrm{script})$; on $\mathrm{none}$ it returns $\mathrm{false}$, on $\mathrm{some}(\mathrm{true})$ it returns $\mathrm{true}$ immediately, and only on $\mathrm{some}(\mathrm{false})$ does it go on to the stack-size test ($|\mathrm{stack}| \le 1000$), the element-size test (every element $\le 520$ bytes), parsing, running the Tapscript loop from the initial state (main stack $= \mathrm{stack}$, empty alt stack and condition stack, weight $\mathrm{weight}$, code-separator position $\texttt{0xFFFFFFFF}$, opcode position $0$), and the final "exactly one element, and it is true" test. The theorem asserts the second case.

**Edge cases the quantifiers include.** $\mathrm{stack}$ with more than $1000$ elements or with elements longer than $520$ bytes (still $\mathrm{true}$); $\mathrm{weight}$ negative; $\mathrm{script}$ that would fail to parse *after* the success opcode (the scan stops at the first success opcode, so later bytes are unconstrained); the success opcode may be preceded by pushes and by non-success opcodes; $\mathrm{ed}$ and $c$ are never consulted.
