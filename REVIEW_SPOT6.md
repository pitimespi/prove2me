# Spot 6: the secp256k1 arithmetic, ECDSA and BIP340 verification versus the specifications

Lean: `Definitions/Def_BitcoinSig.lean` (`p`, `n`, `G`, `powMod`, `finv`, `ninv`, `padd`, `pmul`,
`onCurve`, `liftXParity`, `liftX`, `ecdsaVerifyRaw`, `taggedHash`, `schnorrVerify`). Compared against
the mathematical definitions (secp256k1 parameters, affine group law, ECDSA verification, BIP340
section "Verification") and against libsecp256k1's `secp256k1_ecdsa_sig_verify` (`ecdsa_impl.h:195`)
and `secp256k1_schnorrsig_verify` (`modules/schnorrsig/main_impl.h:208`) for the order of checks.
libsecp256k1's constant-time Jacobian implementation is not transcribed and should not be: the
model's obligation is the mathematics, and the two agree by the standard correctness of the
library.

## Verdict

Agreement. Every operation is the textbook affine formula, with reductions placed so that the
inputs the model actually produces (coordinates below `p`, scalars below `n`) give correct results.

## Parameters and field/scalar arithmetic

`p = 2^256 − 2^32 − 977`, `n`, `Gx`, `Gy`: the SEC 2 values. `powMod` is square-and-multiply with a
fuel that is a bound, not an iteration count (the recursion stops at exponent 0); `finv a = a^(p−2)`,
`ninv a = a^(n−2)` by Fermat, with `0 ↦ 0`, which is only ever reached on branches the group law has
already excluded (doubling with `y = 0`, addition with equal abscissae).

## `padd` (affine group law)

- `∞ + Q = Q`, `P + ∞ = P`.
- `x1 ≡ x2`: if `y1 + y2 ≡ 0` the result is `∞` (this covers `P + (−P)` and doubling a point with
  `y = 0`); otherwise doubling with `λ = 3x1²/(2y1)`, `x3 = λ² − 2x1`, `y3 = λ(x1 − x3) − y1`.
  For points on the curve, `x1 ≡ x2` forces `y2 ≡ ±y1`, so the "doubling" branch is reached only
  when `P = Q`; every point the model adds comes from `parsePubkey`/`liftX` (on-curve checked) or
  is `G`, or is a sum of such.
- otherwise `λ = (y2 − y1)/(x2 − x1)`, `x3 = λ² − x1 − x2`, `y3 = λ(x1 − x3) − y1`.
All subtractions are written as additions of `p − (· mod p)`, so the results are reduced and
non-negative.

## `pmul`

Double-and-add from the least significant bit; fuel 257 covers every scalar below `2^257`, and
scalars are below `n < 2^256`. `pmul 0 P = ∞`.

## `ecdsaVerifyRaw` versus ECDSA

`r = 0 ∨ s = 0` → false (plus the redundant `≥ n` tests); `w = s⁻¹`, `u1 = e·w`, `u2 = r·w`,
`R = u1·G + u2·Q`; `R = ∞` → false; accept iff `x(R) mod n = r`. This is the ECDSA verification
equation; libsecp256k1 tests it as `xr·z² = x ∨ (xr + n < p ∧ (xr + n)·z² = x)`, which its own
comment shows equivalent because `2n > p`. The message scalar is `e = H mod n` (`beVal hash % n`),
as `secp256k1_scalar_set_b32` without an overflow check gives. (Spot 4 covers the parsing,
normalization and key validity around this.)

## `liftXParity`, `liftX`

`y = (x³ + 7)^((p+1)/4) mod p` is a square root when one exists because `p ≡ 3 (mod 4)`; the check
`y² ≡ x³ + 7` rejects non-residues; the parity is selected by negation; `x ≥ p` is rejected by
`liftX` (and by `parsePubkey` before calling `liftXParity`). This is BIP340's `lift_x` and
`secp256k1_ge_set_xo_var`.

## `schnorrVerify` versus BIP340 and `secp256k1_schnorrsig_verify`

| Specification / library | Lean | Agree |
|---|---|---|
| `pk` 32 bytes, `sig` 64 bytes (lengths are checked by the callers in Core; `XOnlyPubKey` is always 32, `CheckSchnorrSignature` checks 64/65) | explicit length tests | yes |
| `r = int(sig[0:32])`, fail if `r ≥ p` (`fe_set_b32_limit`) | `p ≤ r → false` | yes |
| `s = int(sig[32:64])`, fail if `s ≥ n` (`scalar_set_b32` overflow) | `n ≤ s → false` | yes |
| `P = lift_x(pk)`, fail if none (`xonly_pubkey_parse`/`load`) | `liftX` | yes |
| `e = int(tagged_hash("BIP0340/challenge", r ‖ pk ‖ m)) mod n` | identical, with `taggedHash` = `SHA256(SHA256(tag) ‖ SHA256(tag) ‖ m)` | yes |
| `R = s·G − e·P`; fail if `∞` | `padd (pmul s G) (pmul ((n − e) mod n) P)` | yes |
| fail if `y(R)` odd or `x(R) ≠ r` | `ry % 2 = 0 ∧ rx = r` | yes |

The library computes `e` from the *loaded* key's abscissa serialized back to 32 bytes, which equals
`pk` once parsing succeeded.

## Vectors

BIP340's official test vectors (`tests/SigVectors.lean`), the ECDSA signatures of `tests/SigVectors.lean`,
`tests/LaxDerVectors.lean` (spot 4) and the 29 Python-signed Schnorr signatures of
`tests/TapscriptVectors.lean` (spots 8 and 9), all produced by code that shares nothing with the Lean
beyond the curve parameters.
