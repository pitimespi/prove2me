# Spot 4: `CPubKey::Verify`, `ecdsa_signature_parse_der_lax`, key parsing, S normalization versus `BitcoinSig`

Core: [`pubkey.cpp:283`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L283)
(`CPubKey::Verify`), [`pubkey.cpp:45`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L45)
(`ecdsa_signature_parse_der_lax`), [`pubkey.h:69`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.h#L69)
(`GetLen`, `Set`, `IsValid`), libsecp256k1 `eckey_impl.h` (`secp256k1_eckey_pubkey_parse`),
`ecdsa_impl.h:195` (`secp256k1_ecdsa_sig_verify`), `secp256k1.c` (`secp256k1_ecdsa_verify`,
`secp256k1_ecdsa_signature_normalize`, `secp256k1_ecdsa_signature_parse_compact`). Lean:
`Definitions/Def_BitcoinSig.lean` (`pubkeyValid`, `parsePubkey`, `liftXParity`, `parseDerLax`,
`normalizeS`, `ecdsaVerifyRaw`, `pubkeyVerify`). Read-back: `missions/readbacks/sig/readback_Def_BitcoinSig.md`.

## Verdict

Agreement at every step. The field and group arithmetic is compared against the mathematics (the
Lean implements affine arithmetic over `p` and `n` directly), not against libsecp256k1's code;
29 generated vectors confirm the parser and the normalization, including the cases where the lax
parser accepts what strict DER rejects.

## `CPubKey::Verify` — `pubkeyVerify`

| Core | Lean | Agree |
|---|---|---|
| `IsValid()`: `size() > 0`; the constructor stores the bytes only if `GetLen(header)` equals the length (`02`/`03` → 33, `04`/`06`/`07` → 65, else 0), otherwise `Invalidate` makes `size()` zero | `pubkeyValid`: header-determined length equals the length | yes |
| `secp256k1_ec_pubkey_parse` fails → `false` | `parsePubkey = none → false` | yes |
| `ecdsa_signature_parse_der_lax` returns 0 → `false` | `parseDerLax = none → false` | yes |
| `secp256k1_ecdsa_signature_normalize`: a high `s` is replaced by `n − s` | `normalizeS` (`isHighS s = n/2 < s`, which for odd `n` is `s ≥ (n+1)/2`, the same as `secp256k1_scalar_is_high`) | yes |
| `secp256k1_ecdsa_verify`: message scalar `set_b32` reduces modulo `n` without failing; rejects a high `s` (none after normalization); `secp256k1_ecdsa_sig_verify` | `ecdsaVerifyRaw Q (beVal hash % n) r (normalizeS s)` | yes |

## `secp256k1_ecdsa_sig_verify` — `ecdsaVerifyRaw`

| Core | Lean | Agree |
|---|---|---|
| `r = 0 ∨ s = 0` → 0 | identical (the `n ≤ r ∨ n ≤ s` tests are redundant: parsed scalars are below `n`) | yes |
| `u1 = s⁻¹·m`, `u2 = s⁻¹·r`, `pr = u1·G + u2·Q`; infinity → 0 | identical, with `padd (pmul u1 G) (pmul u2 Q)` | yes |
| `r ≡ X(pr) (mod n)`, implemented without inversion as `xr·z² = x ∨ (xr + n < p ∧ (xr + n)·z² = x)` | `x % n = r` on the affine abscissa; equivalent since `2n > p` makes the two forms coincide, as Core's own comment derives | yes |

## `secp256k1_eckey_pubkey_parse` — `parsePubkey`

| Core | Lean | Agree |
|---|---|---|
| 33 bytes with `02`/`03`: `x = fe_set_b32` (fails if `x ≥ p`); `ge_set_xo_var(x, odd)`: the square root of `x³ + 7` if it exists, negated to the requested parity | `x < p`, `liftXParity`: `y = (x³+7)^((p+1)/4)`, check `y² ≡ x³ + 7`, pick the parity; `y = 0` is left as `0` for either parity, as negation of `0` is `0` in Core | yes |
| 65 bytes with `04`/`06`/`07`: `x, y < p`; for `06`/`07` the parity of `y` must match (`07` odd); point must be on the curve | identical | yes |
| any other length or tag → 0 | `none` | yes |
| `secp256k1_ec_pubkey_parse` adds the subgroup test, trivially true on secp256k1 (cofactor 1) | not modeled | yes |

## `ecdsa_signature_parse_der_lax` — `parseDerLax`

Both return "no signature" (`0` / `none`) or a pair `(r, s)`; an *overflow* (an integer with more
than 32 significant bytes, or a value at or above `n`) is "correctly parsed but invalid", i.e.
`(0, 0)`, which then fails verification. Trailing bytes after the S integer are ignored.

| Core | Lean | Agree |
|---|---|---|
| sequence tag `0x30`; a sequence length byte that is read and, in long form (`≥ 0x80`), *skipped without validation* (`lenbyte − 0x80` bytes, bounded by the input) | identical | yes |
| each integer: tag `0x02`; short length; or long length with leading zero length bytes stripped, then at most 3 length bytes (`lenbyte ≥ 4` after stripping → 0), big-endian value; bounded by the input | identical (`skipZeros` before the `4 ≤ lb` test) | yes |
| leading zero *value* bytes stripped; more than 32 remaining → overflow | identical | yes |
| `secp256k1_ecdsa_signature_parse_compact`: `r ≥ n` or `s ≥ n` → overflow | identical | yes |
| every `input[pos]` read is guarded by a bound test | `getD` reads only where Core reads | yes |

## Vectors (`tests/LaxDerVectors.lean`, generator `tests/reference/laxder_reference.py`)

A Python signer written from the ECDSA definition produces a low-S signature; the file then
re-encodes it 21 ways and offers 8 key encodings, with the verdict Core's parser semantics
require: strict DER, high-S (accepted after normalization), overlong sequence and integer lengths
(`81`, `82 00`, `83 00 00`, `84 00 00 00`, `85 00 00 00 00`: accepted after zero stripping;
`84 01 00 00`: rejected), an ignored sequence-length value, zero-padded and *unpadded* R (the
latter is "negative" in strict DER and still verifies here), trailing garbage (accepted), a wrong
tag, 33-significant-byte R, `r = n`, `s = n`, `r = 0`, `s = 0`, truncation, the empty signature, a
wrong message; keys compressed, uncompressed, hybrid with the right and the wrong parity, `x ≥ p`,
off-curve, wrong length, tag `05`. All 29 agree with the Lean. (One expectation in the first draft of
the generator was wrong in the direction of being stricter than Core; the Lean was right.)

Note for the reader: these lax cases only matter for signatures that reach `CPubKey::Verify`, i.e.
before BIP66 (`DERSIG` off) any encoding the lax parser accepts was consensus-valid; after BIP66
`IsValidSignatureEncoding` (spot 5) rejects everything but strict DER first.
