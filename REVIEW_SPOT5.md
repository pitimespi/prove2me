# Spot 5: `IsValidSignatureEncoding`, `CheckSignatureEncoding`, `CheckPubKeyEncoding` versus `BitcoinSig`

Core: [`interpreter.cpp:118`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L118)
(`IsValidSignatureEncoding`), `:177` (`IsLowDERSignature`), `:187` (`IsDefinedHashtypeSignature`),
`:211` (`CheckSignatureEncoding`), `:228` (`CheckPubKeyEncoding`), `:49` (`IsCompressedOrUncompressedPubKey`,
`IsCompressedPubKey`), [`pubkey.cpp:393`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L393)
(`CheckLowS`). Lean: `Definitions/Def_BitcoinSig.lean` (`isValidSignatureEncoding`, `isLowDERSignature`,
`checkLowS`, `isDefinedHashtypeSignature`, `checkSignatureEncoding`, `checkPubKeyEncoding`,
`isCompressedOrUncompressedPubKey`, `isCompressedPubKey`, `SigFlags`).

## Verdict

Agreement, rule by rule. On mainnet consensus only `DERSIG` is ever set (`BitcoinVerify.sigFlagsOf`
maps the activation flags to `⟨dersig, false, false, false⟩`), so of these functions only
`IsValidSignatureEncoding` and the `DERSIG` branch of `CheckSignatureEncoding` are consensus; the
rest is transcribed for fidelity and confirmed to be reachable only under policy flags.

## `IsValidSignatureEncoding` — `isValidSignatureEncoding`

The sixteen tests, in Core's order, each with the Lean clause: size < 9; size > 73; `sig[0] ≠ 0x30`;
`sig[1] ≠ size − 3`; `5 + lenR ≥ size`; `lenR + lenS + 7 ≠ size`; `sig[2] ≠ 0x02`; `lenR = 0`;
`sig[4] & 0x80`; `lenR > 1 ∧ sig[4] = 0 ∧ ¬(sig[5] & 0x80)`; `sig[lenR+4] ≠ 0x02`; `lenS = 0`;
`sig[lenR+6] & 0x80`; `lenS > 1 ∧ sig[lenR+6] = 0 ∧ ¬(sig[lenR+7] & 0x80)`. The Lean reads bytes with
`getD 0`; every index Core reads is within `size` once `lenR + lenS + 7 = size` has been checked, and
before that point only indices 0–4 and `5 + lenR < size` are read, as in Core. The hash-type byte
is not inspected here (so `strict[:-1] ++ [0xff]` is valid DER, as in Core).

## `CheckSignatureEncoding` — `checkSignatureEncoding`

Empty signature → `true` (a failed `CHECKSIG`, not a script error); `DERSIG ∨ LOW_S ∨ STRICTENC` and
not strict DER → script error; `LOW_S` and not low-S (`CheckLowS`: lax parse of the signature without
its last byte, `s` not high) → script error; `STRICTENC` and hash type (with the `ANYONECANPAY` bit
cleared) outside `1..3` → script error. Identical, including `checkLowS` through `parseDerLax` and
`isHighS`.

## `CheckPubKeyEncoding` — `checkPubKeyEncoding`

`STRICTENC` and not compressed-or-uncompressed (`02`/`03` with 33 bytes, `04` with 65) → error;
`WITNESS_PUBKEYTYPE` under `WITNESS_V0` and not compressed → error. Identical. Neither flag is set by
`GetBlockScriptFlags`, so hybrid keys remain consensus-valid in legacy and v0 scripts, which is
what `CPubKey::Verify` (spot 4) accepts.

## Vectors (`tests/DerEncodingVectors.lean`, generator `tests/reference/derencoding_reference.py`)

A strict-DER signature from the spot 4 signer, then one mutation per rule (19 cases: lengths 8 and
74, wrong tags, sequence length off by one, `lenR` covering the rest, `lenR + lenS + 7` mismatch,
zero-length integers, "negative" integers, unnecessary padding, high S still valid, arbitrary
hash-type byte, the minimal 9-byte and maximal 73-byte forms), then 11 cases for the flag logic
(empty signature, `DERSIG` off, `LOW_S`, `STRICTENC` with hash types `0` and `0x83`, hybrid and
uncompressed keys under each flag). All 30 agree.
