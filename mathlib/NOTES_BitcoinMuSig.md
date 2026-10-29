# NOTES — BitcoinMuSig

MuSig2 (BIP327) and FROST (RFC 9591) aggregation over secp256k1, with a bridge from the
executable curve arithmetic of `Def_BitcoinSig` to Mathlib's group law on Weierstrass curves.
Files: `Definitions/Def_BitcoinMuSig.lean` (model; imports `Def_BitcoinSig`, `Def_BitcoinTaproot`)
and `Solutions/Sol_BitcoinMuSig_all.lean` (29 public theorems, no `sorry`; every public theorem
depends only on `[propext, Classical.choice, Quot.sound]`; the kernel computations use
`decide +kernel`, never `native_decide`).

**Rung reached: all three.** (1) the bridge, unconditionally (both primality facts are
certified); (2) MuSig2 in Mathlib's group *and* transported end to end to the executable BIP327
transcription and BIP340 `schnorrVerify` on byte strings, parity negations included; (3) FROST in
Mathlib's group (abstract module, `ZMod n`-module, and secp256k1 itself).

## The model (Definitions)

* `W : WeierstrassCurve.Affine (ZMod p)`, `⟨0, 0, 0, 0, 7⟩` (secp256k1, `y² = x³ + 7`).
* `toPoint : Point → Option W.Point` (`none` ↦ `some 0`; `some (x, y)` ↦ the affine point
  `(x mod p, y mod p)` when `onCurve (x, y)`, else `none`), its total version `tp` (off-curve ↦ `0`),
  `Valid P` (the affine data, if any, is on the curve), `Reduced P` (coordinates `< p`), `Gpt` (G as
  a Mathlib point), `pneg`, `hasEvenY`, `evenY`, `ofPoint`.
* Primality of `p`: **certified, no hypothesis**. `p_prime_cert : Nat.Prime p` is a Lucas–Pratt
  certificate (witness 3, `p − 1 = 2·3·7·13441·q₅`, recursively), whose modular exponentiations are
  kernel-checked through the executable `powMod` (`powMod_eq : powMod b e m = b ^ e % m`,
  `prime_of_cert`). It provides `instance : Fact (Nat.Prime p)`, so `ZMod p` is a field and
  `W.Point` an `AddCommGroup`. These proofs sit in the Def file because `toPoint` needs
  `nonsingular_of_onCurve` (from `equation_iff_onCurve` and `W.Δ = −21168 ≠ 0`) and the statements
  need the field instance.
* BIP327, transcribed on bytes: `cbytes`/`cpoint` (33-byte compressed encodings, `parsePubkey`),
  `cbytesExt`/`cpointExt`, `hashKeys`, `getSecondKey`, `keyAggCoeff`, `keyAggSum`, `keyAgg`,
  `applyTweak(s)` (with `gacc`/`tacc`), `keyAggTweaked`, `nonceSum`, `nonceAgg`, `SessionCtx`,
  `getSessionValues` (also returns the raw `R' = R₁ + b⋅R₂` before the infinity→G substitution),
  `partialSigVerifyInternal`, `partialSigAgg`. Tagged hashes are `BitcoinSig.taggedHash`.
* FROST: `lagrangeCoeff S i = ∏_{j ∈ S∖{i}} j / (j − i)` in `ZMod n`.

## Theorems (`BitcoinMuSig.<name>`)

Bridge (rung 1):
1. `toPoint_padd`: `Valid P → Valid Q → toPoint (padd P Q) = some (tp P + tp Q)`.
2. `valid_padd`, `tp_padd`: the sum of curve points is a curve point; `tp (padd P Q) = tp P + tp Q`.
3. `valid_pmul`, `tp_pmul`: for `k < 2^257` (the ladder's fuel), `tp (pmul k P) = k • tp P`.
4. `toPoint_pneg`: `toPoint (pneg P) = some (-tp P)`.
5. `eq_of_tp_eq`: `tp` is injective on valid reduced points.
6. `padd_comm` (valid points), `padd_assoc` (valid reduced points): exact equalities of executable
   points. `pmul_add`, `pmul_padd`, `pmul_pmul`: linearity / composition of the ladder (scalars
   within the fuel bound, reduced valid points).
7. `tp_G : tp G = Gpt`; `n_nsmul_Gpt : n • Gpt = 0` (kernel evaluation `pmul n G = none`, ~25 s);
   `nsmul_Gpt_mem : n • (d • Gpt) = 0`; `n_prime : Nat.Prime n` (Lucas–Pratt certificate,
   witness 7, `n − 1 = 2⁶·3·149·631·107361793816595537·174723607534414371449·
   341948486974166000522343609283189`, recursively); `addOrderOf_Gpt : addOrderOf Gpt = n`.
8. `cpoint_spec`: every parsed compressed point is a reduced curve point;
   `cpoint_cbytes`: `cpoint (cbytes P) = some P` on reduced curve points (square root by
   `(p+1)/4`-th power and parity selection).

MuSig2 (rung 2), Mathlib's group:
9. `musig2_partialSigAgg` (any `CommRing K`, `K`-module `M`): if every
   `sᵢ⋅G = ε⋅(R₁ᵢ + b⋅R₂ᵢ) + (e⋅aᵢ⋅g⋅gacc)⋅Xᵢ` and `Q = gacc⋅Σ aᵢXᵢ + tacc⋅G`, then
   `(Σ sᵢ + e⋅g⋅tacc)⋅G = ε⋅(Σ R₁ᵢ + b⋅Σ R₂ᵢ) + e⋅(g⋅Q)`.
10. `musig2_sign_partialSigVerify`: BIP327 `Sign`'s `s = ε k₁ + b ε k₂ + e a g gacc d` passes it.
11. `musig2_correct`: honest signers ⇒ the Schnorr equation.
12. `musig2_partialSigAgg_secp256k1`: item 9 on `W.Point` with `G = Gpt` (integer scalars).

MuSig2 (rung 2), transported to the executable transcription:
13. `partialSigAgg_schnorrVerify`: for a session whose key list is the signers' keys
    (`ctx.pks = sigs.map (·.2.2)`), whose aggregate nonce is `nonceAgg` of the signers' public
    nonces, every partial signature passing `partialSigVerifyInternal`, `sigs ≠ []`, the raw
    aggregate nonce `R' ≠ ∞`, and every key in the order-`n` subgroup
    (`hkeys : ∀ pk ∈ ctx.pks, n • tp (cpoint pk) = 0`): `getSessionValues ctx = some sv`,
    `partialSigAgg` returns some `sig`, and `schnorrVerify (xbytes sv.Q) ctx.msg sig = true`.
    The proof covers the tweak accumulators `gacc`/`tacc` (any list of plain or x-only tweaks), the
    negation for odd `Q.y` (`g = n − 1`) and odd `R.y`, `lift_x` of the x-only key, the 33-byte
    nonce encodings and the 32-byte scalar/abscissa encodings (`beVal ∘ be32 = id`).

FROST (rung 3):
14. `lagrange_interpolate_zero`: `Σ_{i∈S} lagrangeCoeff S i * f(i) = f(0)` for identifiers
    `i < n` and `deg f < |S|` (via `Lagrange.eq_interpolate`; `ZMod n` is a field by `n_prime`).
15. `frost_partialSigAgg` (any module): `zᵢ⋅G = Dᵢ + ρᵢ⋅Eᵢ + (c⋅λᵢ)⋅Yᵢ` for all `i` ⇒
    `(Σ zᵢ)⋅G = Σ (Dᵢ + ρᵢ⋅Eᵢ) + c⋅Σ λᵢ⋅Yᵢ`.
16. `frost_sign_partialVerify`: `z = d + e⋅ρ + λ⋅s⋅c` passes the partial verification.
17. `frost_correct` (`ZMod n`-module): with Shamir shares `Yᵢ = f(i)⋅G` and `λᵢ = lagrangeCoeff S i`,
    `(Σ zᵢ)⋅G = Σ (Dᵢ + ρᵢ⋅Eᵢ) + c⋅(f(0)⋅G)`.
18. `frost_correct_secp256k1`: the same on `W.Point`, scalars of `ZMod n` acting by `ZMod.val`
    (uses `n • Gpt = 0`).

## Hypotheses and limits

* No primality hypothesis anywhere: `p` and `n` are both certified.
* `partialSigAgg_schnorrVerify` assumes `hkeys`: each session key has order dividing `n`. This is
  true of every secp256k1 point (the group has prime order `n`, cofactor 1), but proving
  `#E(𝔽_p) = n` (point counting) is out of reach here; what *is* proved is `n • Gpt = 0`, hence
  `hkeys` for every honestly generated key `d ⋅ G` (`nsmul_Gpt_mem`). Nonces need no such
  hypothesis (they enter linearly, never through a reduced scalar).
* `R' ≠ ∞` is necessary: when `R₁ + b⋅R₂ = ∞`, BIP327 substitutes `R = G`, and the honest partial
  signatures then do not verify as a whole.
* `tp_pmul` and its corollaries hold for `k < 2^257` (the executable ladder runs 257 rounds); all
  BIP327 scalars are reduced mod `n < 2^256`.
* FROST is proved at the group level (no executable FROST transcription exists in the Def files).
* Pipeline: `stubs` → 29 stubs, build errors 0; `split` → every split file `errors=0` (split files
  with dependencies show `sorryAx` only through the `Theorems/Thm_*` stubs they import).
