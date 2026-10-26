# Read-back: `BitcoinSig.sigHash_single_bug`

**Binders and hypothesis.** Universally quantified over a byte string $scriptCode$, a transaction $tx$, and natural numbers $nIn$ and $hashType$ (the latter unbounded, not restricted to one byte). Two hypotheses:
- $h1$: $hashType \mathbin{\&} 31 = 3$, i.e. the low five bits of $hashType$ (bitwise AND on natural numbers with `0x1f`) equal the constant `SIGHASH_SINGLE` $= 3$; the remaining bits, in particular the ANYONECANPAY bit $128$ and any bits above the eighth, are unconstrained;
- $h2$: $|tx.\text{vout}| \leq nIn$, the input index is at least the number of outputs (so there is no output at position $nIn$; this includes the case of a transaction with no outputs at all, for every $nIn$).

**Conclusion.**
$$\text{sigHashLegacy}\ scriptCode\ tx\ nIn\ hashType = \text{uint256One},$$
where `uint256One` is the 32-byte string consisting of the byte $1$ followed by 31 zero bytes.

**Unfolding.** `sigHashLegacy` $sc\,tx\,nIn\,ht$ is defined as: if $ht \mathbin{\&} 31 = 3$ and $|tx.\text{vout}| \leq nIn$ then `uint256One`, else the double SHA-256 of the legacy serialization followed by the 4-byte hash type. The two hypotheses are literally the two conjuncts of the guard, so the conclusion is the first branch of the definition. The script code, the inputs, version, lock time, and the number of inputs play no role; $nIn$ need not be a valid input index either.

**Edge cases.** With $tx.\text{vout} = [\,]$ the conclusion holds for every $nIn$ including $0$. With $|tx.\text{vout}| = nIn$ exactly, the bound is met (it is $\leq$, not $<$). Hash types $3$, $131$ ($3 + 128$), $35$, $259$, etc. all satisfy $h1$.

**What is not said.** The statement does not say what the hash is when $nIn < |tx.\text{vout}|$ or when the low five bits are not $3$. It does not say that `uint256One` is "the number one" in any particular reading: as a byte string it begins with the byte $1$; read big-endian by `pubkeyVerify` it is the scalar $2^{248} \bmod n$ — the theorem asserts only equality of byte strings. It does not say anything about whether a signature over this value verifies, nor about `checkECDSASignature` or `checkSigPreTapscript`. It does not say the BIP143 hash has any analogous behaviour (by its definition it does not; it uses a zero `hashOutputs` instead). It does not assert that this is a "bug" despite the theorem's name — the name is not part of the statement.
