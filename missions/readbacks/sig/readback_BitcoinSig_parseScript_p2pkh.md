# Read-back: `BitcoinSig.parseScript_p2pkh`

**Binders and hypothesis.** Universally quantified over a byte string $h$, with one hypothesis $hh$: $|h| = 20$.

**Conclusion.**
$$\text{parseScript}\ (\text{p2pkhBytes}\ h) = \text{some}\ (\text{p2pkhScript}\ h).$$

**Unfolding the left side.** `p2pkhBytes` $h$ is $[\texttt{0x76}, \texttt{0xa9}] \,\|\, \text{pushBytes}\ h \,\|\, [\texttt{0x88}, \texttt{0xac}]$. Since $|h| = 20 < 76$, `pushBytes` $h$ is the single length byte `0x14` followed by the 20 bytes of $h$; so the whole string is the 25 bytes $[\texttt{0x76}, \texttt{0xa9}, \texttt{0x14}] \,\|\, h \,\|\, [\texttt{0x88}, \texttt{0xac}]$. `parseScript` runs the instruction parser with fuel equal to the length (25) and returns "none" if any push runs past the end of the data, else "some" of the instruction list. `getOp` on each prefix: `0x76` exceeds `0x4e` so it is the opcode instruction with byte `0x76`; likewise `0xa9`; `0x14` $= 20 <$ `0x4c` so it is a direct push of the next 20 bytes, which are exactly $h$ (there are 22 bytes remaining, so the push does not run short); then `0x88` and `0xac` are opcode instructions; the empty remainder parses to the empty list. The result is "some" of
$$[\ \text{op}\ \texttt{0x76},\ \text{op}\ \texttt{0xa9},\ \text{push}\ h,\ \text{op}\ \texttt{0x88},\ \text{op}\ \texttt{0xac}\ ].$$

**Unfolding the right side.** `p2pkhScript` $h$ (from the script file) is the instruction list $[\text{op}\ \texttt{OP\_DUP}, \text{op}\ \texttt{OP\_HASH160}, \text{push}\ h, \text{op}\ \texttt{OP\_EQUALVERIFY}, \text{op}\ \texttt{OP\_CHECKSIG}]$, where the opcode constants are the bytes `0x76`, `0xa9`, `0x88`, `0xac` respectively. So the two sides are the same list wrapped in "some".

**What is not said.** The statement does not say anything for $|h| \neq 20$: in particular it does not assert the (by the definitions also true) parse for other lengths below 76, nor for lengths that would use `OP_PUSHDATA1/2/4` encodings. It does not say that `p2pkhBytes` is the *only* byte string parsing to `p2pkhScript` $h$ (a non-canonical push such as `0x4c 0x14` followed by $h$ would parse to the same instruction list). It does not say anything about executing the script, about `findAndDelete`, about `serScriptCode`, or about the oracle. It does not say that $h$ is a hash of anything. It does not involve any flags, transaction, or signature.
