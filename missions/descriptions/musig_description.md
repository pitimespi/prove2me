## The claim

MuSig2 (BIP327) lets $n$ signers produce one BIP340 Schnorr signature for an aggregate key, indistinguishable on chain from a single-signer Taproot spend; FROST does the same for a threshold of signers. The correctness claim is that partial signatures which each pass their partial check combine into a signature that the ordinary Schnorr verifier accepts. Earlier this was judged infeasible here: the signature mission's secp256k1 is an executable transcription without a proof of the group law. This mission supplies that proof, by connecting the executable curve to Mathlib's elliptic-curve group, and then proves MuSig2 correctness end to end against the executable `schnorrVerify`, and FROST correctness in the group.

## What is proved

- **The bridge** (`toPoint_padd`, `valid_padd`, `tp_padd`, `valid_pmul`, `tp_pmul`, `toPoint_pneg`, `eq_of_tp_eq`, `padd_comm`, `padd_assoc`, `pmul_add`, `pmul_padd`, `pmul_pmul`, `tp_G`): the executable point addition, negation and scalar ladder are Mathlib's group operations on $y^2 = x^3 + 7$ over $\mathbb{F}_p$; hence they are associative, commutative and linear.
- **The group** (`n_prime`, `n_nsmul_Gpt`, `nsmul_Gpt_mem`, `addOrderOf_Gpt`): $p$ and $n$ are prime (Lucas–Pratt certificates checked by the kernel) and the generator has order exactly $n$.
- **Encodings** (`cpoint_spec`, `cpoint_cbytes`): compressed points parse to reduced curve points and round-trip.
- **MuSig2** (`musig2_partialSigAgg`, `musig2_sign_partialSigVerify`, `musig2_correct`, `musig2_partialSigAgg_secp256k1`, `partialSigAgg_schnorrVerify`, the goal): the aggregation algebra in any module and on secp256k1, and the end-to-end statement that BIP327's `PartialSigAgg` of partial signatures that pass `PartialSigVerifyInternal` is a signature `schnorrVerify` accepts for the aggregate x-only key, with key aggregation coefficients, plain and x-only tweaks, and the parity negations of the BIP.
- **FROST** (`lagrange_interpolate_zero`, `frost_partialSigAgg`, `frost_sign_partialVerify`, `frost_correct`, `frost_correct_secp256k1`): Lagrange interpolation at 0 and the aggregation of shares into a Schnorr signature for the group key, in any `ZMod n`-module and on secp256k1.

## What this rests on and what it does not say

Correctness only, not security: nothing is claimed about unforgeability or the hardness of discrete logarithms. The end-to-end theorem assumes each signer key has order dividing $n$ (true of every secp256k1 point because the group has prime order, but proving $\#E(\mathbb{F}_p) = n$ needs point counting; for keys of the form $dG$ it is discharged by `nsmul_Gpt_mem`), and that the aggregate nonce is not the point at infinity, where BIP327 substitutes $G$ and honest partial signatures no longer combine. FROST is proved in the group only: there is no executable FROST transcription. ([BIP327](https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki), [RFC 9591](https://www.rfc-editor.org/rfc/rfc9591))
