SRC = ("BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): "
       "https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); "
       "secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)")
TAGS = ["bitcoin", "musig2", "bip327", "frost", "schnorr", "bip340", "secp256k1", "elliptic-curve", "multisignature", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "BitcoinMuSig",
    "definition_title": "secp256k1 as a Mathlib elliptic curve, the bridge from the executable curve, and BIP327 MuSig2 session algorithms",
    "natural_language_statement": r"""Over Mathlib and the signature and Taproot missions.

**Primality.** `powMod_eq`, `prime_of_cert` (a Lucas–Pratt certificate checker) and `p_prime_cert : Nat.Prime p` with the instance `Fact (Nat.Prime p)`: the field prime of secp256k1 is certified, so `ZMod p` is a field. **`W`** — the curve $y^2 = x^3 + 7$ over `ZMod p` as a Mathlib `WeierstrassCurve.Affine`, with discriminant $-21168 \ne 0$ and `nonsingular_of_onCurve`.

**The bridge.** **`toPoint`**, **`tp`** — the executable point (an optional pair of naturals) as a Mathlib point (`0` for infinity); **`Valid P`** — on the curve; **`Reduced P`** — coordinates below $p$; **`ofPoint`**, **`Gpt`** (the generator as a Mathlib point), **`pneg`**, **`hasEvenY`**, **`evenY`**.

**BIP327.** **`tagged`**, **`xbytes`** (32-byte x-coordinate), **`cbytes`** (33-byte compressed point), **`cpoint`** (parse a compressed point), **`KeyAggCtx`** (aggregate point, `gacc`, `tacc`), **`hashKeys`**, **`getSecondKey`**, **`keyAggCoeffInternal`**, **`keyAggCoeff`**, **`keyAggSum`**, **`keyAgg`**, **`applyTweak`**, **`applyTweaks`**, **`keyAggTweaked`**, **`nonceSum`**, **`nonceAgg`**, **`SessionCtx`**, **`SessionValues`**, **`getSessionValues`**, **`partialSigVerifyInternal`**, **`partialSigAgg`** — the BIP's algorithms over byte strings and the executable curve, including the second-key exception, plain and x-only tweaks, the negations for odd `Q.y` and `R.y`, and the substitution $R = G$ at infinity.

**FROST.** **`lagrangeCoeff S i`** — the Lagrange coefficient at 0 for identifier set $S$, in `ZMod n`.

**Formalization Note.** Imports Mathlib, `BitcoinSig`, `BitcoinTaproot`. The file carries the primality certificate and the curve's nonsingularity as lemmas because Mathlib's group structure on points needs them; they are checked by `decide +kernel`, never `native_decide`.""",
}

T = {}
T["toPoint_padd"] = ("The executable addition is Mathlib's group addition", r"""For points on the curve: `toPoint (padd P Q) = some (tp P + tp Q)`.""")
T["valid_padd"] = ("The executable sum of curve points is on the curve", r"""`Valid P → Valid Q → Valid (padd P Q)`.""")
T["tp_padd"] = ("tp is additive", r"""For valid points: `tp (padd P Q) = tp P + tp Q`.""")
T["valid_pmul"] = ("Scalar multiples of curve points are on the curve", r"""For $k < 2^{257}$ (the ladder's fuel): `Valid (pmul k P)`.""")
T["tp_pmul"] = ("The executable scalar multiplication is Mathlib's scalar action", r"""For valid $P$ and $k < 2^{257}$: `tp (pmul k P) = k • tp P`.""")
T["toPoint_pneg"] = ("The executable negation is Mathlib's negation", r"""`toPoint (pneg P) = some (-tp P)` for valid $P$.""")
T["eq_of_tp_eq"] = ("tp is injective on reduced curve points", r"""Valid, reduced $P$, $Q$ with `tp P = tp Q` are equal.""")
T["padd_comm"] = ("The executable addition is commutative", r"""`padd P Q = padd Q P` for valid points.""")
T["padd_assoc"] = ("The executable addition is associative", r"""For valid, reduced points: `padd (padd P Q) R = padd P (padd Q R)`. This is the group law the signature mission's executable curve lacked a proof of.""")
T["pmul_add"] = ("The scalar ladder is additive in the scalar", r"""`pmul (a+b) P = padd (pmul a P) (pmul b P)` for $a + b < 2^{257}$ and valid, reduced $P$.""")
T["pmul_padd"] = ("The scalar ladder distributes over addition", r"""`pmul k (padd P Q) = padd (pmul k P) (pmul k Q)`.""")
T["pmul_pmul"] = ("Scalar multiplications compose", r"""`pmul a (pmul b P) = pmul (a·b) P` within the fuel bound.""")
T["tp_G"] = ("The executable generator is the Mathlib generator", r"""`tp G = Gpt`.""")
T["n_nsmul_Gpt"] = ("The generator has order dividing n", r"""`n • Gpt = 0`, by kernel evaluation of `pmul n G = none`.""")
T["nsmul_Gpt_mem"] = ("Multiples of the generator are killed by n", r"""`n • (d • Gpt) = 0` for every $d$.""")
T["n_prime"] = ("The group order n of secp256k1 is prime", r"""`Nat.Prime n`, by a recursive Lucas–Pratt certificate.""")
T["addOrderOf_Gpt"] = ("The generator has order exactly n", r"""`addOrderOf Gpt = n`.""")
T["cpoint_spec"] = ("Parsed compressed points are reduced curve points", r"""`cpoint b = some P → onCurve P ∧ P.1 < p ∧ P.2 < p`.""")
T["cpoint_cbytes"] = ("Compressed encoding round-trips", r"""For reduced curve points: `cpoint (cbytes P) = some P`.""")
T["musig2_partialSigAgg"] = ("MuSig2 partial-signature aggregation in any module", r"""Over any commutative ring $K$ and $K$-module: if every partial signature satisfies $s_iG = \varepsilon(R_{1,i} + bR_{2,i}) + (e\,a_i\,g\,g_{acc})X_i$ and $Q = g_{acc}\sum a_iX_i + t_{acc}G$, then $(\sum s_i + e\,g\,t_{acc})G = \varepsilon(\sum R_{1,i} + b\sum R_{2,i}) + e(gQ)$: the BIP340 equation for the aggregate.""")
T["musig2_sign_partialSigVerify"] = ("An honest BIP327 Sign output passes the partial check", r"""With $s = \varepsilon k_1 + b\varepsilon k_2 + e\,a\,g\,g_{acc}\,d$: $sG = \varepsilon(k_1G + b\,k_2G) + (e\,a\,g\,g_{acc})(dG)$.""")
T["musig2_correct"] = ("MuSig2 correctness with honest signers", r"""Honest partial signatures sum to a signature satisfying the Schnorr equation for the aggregate key.""")
T["musig2_partialSigAgg_secp256k1"] = ("MuSig2 aggregation on secp256k1's group", r"""`musig2_partialSigAgg` on Mathlib's points of $W$ with generator `Gpt` and integer scalars.""")
T["partialSigAgg_schnorrVerify"] = ("BIP327 end to end: partial signatures that verify aggregate to a BIP340 signature that verifies", r"""For a session over a nonempty list of signers whose keys are the session's keys, whose nonces aggregate to the session's aggregate nonce, whose keys have order dividing $n$, and whose aggregate nonce point is not infinity: if every partial signature passes `partialSigVerifyInternal`, then the session values exist, `partialSigAgg` returns some `sig`, and the signature mission's `schnorrVerify (xbytes Q) msg sig = true`. All of BIP327's tweak accumulation, parity negations and encodings are included.""")
T["lagrange_interpolate_zero"] = ("Lagrange interpolation at 0", r"""For identifiers below $n$ and a polynomial of degree below $|S|$ over `ZMod n`: $\sum_{i\in S} \lambda_i f(i) = f(0)$.""")
T["frost_partialSigAgg"] = ("FROST partial-signature aggregation in any module", r"""If every $z_iG = D_i + \rho_iE_i + (c\lambda_i)Y_i$ then $(\sum z_i)G = \sum(D_i + \rho_iE_i) + c\sum\lambda_iY_i$.""")
T["frost_sign_partialVerify"] = ("An honest FROST share passes the partial check", r"""$(d + e\rho + \lambda s c)G = dG + \rho(eG) + (c\lambda)(sG)$.""")
T["frost_correct"] = ("FROST correctness with Shamir shares", r"""In a `ZMod n`-module, with shares $f(i)$ of a polynomial of degree below $|S|$: $(\sum z_i)G = R + c\,(f(0)G)$, the Schnorr equation for the group key $f(0)G$.""")
T["frost_correct_secp256k1"] = ("FROST correctness on secp256k1", r"""`frost_correct` on Mathlib's points of $W$ with `ZMod n` scalars acting through their representatives.""")
THEOREMS = {f"BitcoinMuSig.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinMuSig.padd_assoc"]["ms"] = ("The bridge", "The executable affine formulas agree with Mathlib's group law case by case; associativity and commutativity transfer back.")
THEOREMS["BitcoinMuSig.musig2_partialSigAgg"]["ms"] = ("MuSig2 algebra", "Linear combination of the partial verification equations in the module.")
ORDER = ["BitcoinMuSig." + k for k in ["toPoint_padd", "valid_padd", "tp_padd", "valid_pmul", "tp_pmul", "toPoint_pneg", "eq_of_tp_eq", "padd_comm",
  "padd_assoc", "pmul_add", "pmul_padd", "pmul_pmul", "tp_G", "n_nsmul_Gpt", "nsmul_Gpt_mem", "n_prime", "addOrderOf_Gpt", "cpoint_spec",
  "cpoint_cbytes", "musig2_partialSigAgg", "musig2_sign_partialSigVerify", "musig2_correct", "musig2_partialSigAgg_secp256k1",
  "partialSigAgg_schnorrVerify", "lagrange_interpolate_zero", "frost_partialSigAgg", "frost_sign_partialVerify", "frost_correct",
  "frost_correct_secp256k1"]]
