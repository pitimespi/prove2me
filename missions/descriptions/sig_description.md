## Why the signature layer is consensus

A Bitcoin transaction is authorized by signatures, and whether a signature counts is decided by a chain of exact rules: the byte layout the signature must have (strict DER since BIP66), which parts of the transaction the signature commits to (the signature hash, in its legacy and BIP143 forms, with the historical `SIGHASH_SINGLE` bug), how the public key is parsed, how a possibly non-canonical signature is parsed "laxly", and finally ECDSA verification on secp256k1 — or Schnorr verification for Taproot. Each of these has been the site of a consensus-relevant subtlety: BIP66 was a soft fork to remove OpenSSL's parsing from consensus; the `SIGHASH_SINGLE` bug lets a signature commit to nothing; high-S normalization is why libsecp256k1 accepts what historical blocks contain. ([`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp), [`pubkey.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp), [BIP66](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0066.mediawiki), [BIP143](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0143.mediawiki), [BIP340](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0340.mediawiki))

This mission transcribes that layer end to end — the encoding checks, `FindAndDelete`, both signature hashes, `CPubKey::Verify` with the lax DER parser and normalization, the secp256k1 verification equations for ECDSA and Schnorr, the checker's lock-time methods, and the byte-level script parser — and proves what the rest of validation needs: the strict-DER test is exactly the canonical layout, the signature hashes depend on what they should and nothing else, the checker's outcomes are characterized, and the Script mission's abstract P2PKH theorem instantiates to the concrete cryptography.

## Keys, signatures, hashes, and the checker

**secp256k1** is the curve $y^2 = x^3 + 7$ over the prime field of order $p$, with group order $n$ and generator $G$. Points are affine pairs or infinity; addition and scalar multiplication are the textbook formulas with Fermat inverses. A **public key** is parsed as `secp256k1_eckey_pubkey_parse`: compressed (`02`/`03`, square root by $(p+1)/4$ with parity selection), uncompressed (`04`) or hybrid (`06`/`07`), with coordinates below $p$ and on the curve. A **signature** reaches verification through `ecdsa_signature_parse_der_lax`, which tolerates long-form lengths and leading zeros, ignores trailing bytes, and substitutes the zero signature on overflow; its S value is normalized to the low half; the message is the 32-byte hash reduced modulo $n$; and `secp256k1_ecdsa_sig_verify` accepts iff $r, s \in [1, n)$, $R = e s^{-1} G + r s^{-1} Q \ne \infty$ and $R_x \equiv r \pmod n$. **Schnorr** verification is BIP340 with tagged hashes and `lift_x`.

The **signature hash** of input $nIn$ under hash type $t$ is, for legacy scripts, SHA-256d of the `CTransactionSignatureSerializer` output — version, the inputs (only the signed one under `ANYONECANPAY`; other inputs' scripts blanked, their sequences zeroed under `SINGLE`/`NONE`), the outputs (none under `NONE`, truncated to $nIn+1$ with blanked others under `SINGLE`), lock time — followed by $t$ as four bytes, except that `SINGLE` with no output at $nIn$ yields the constant $1$; for witness v0 it is the BIP143 construction with `hashPrevouts`, `hashSequence`, `hashOutputs`, the script code and the amount.

The **encoding checks** are `IsValidSignatureEncoding` (the fourteen BIP66 tests), low-S, the key-shape tests and the hash-type test, assembled by `CheckSignatureEncoding`/`CheckPubKeyEncoding` under the flags (`DERSIG` is the only one mainnet consensus enables). The **checker** (`EvalChecksigPreTapscript`) deletes the signature push from the script code (legacy only), applies the encoding checks as script errors, and returns `CheckECDSASignature`'s verdict: a valid key, a non-empty signature whose last byte is the hash type, and `CPubKey::Verify` on the signature hash. The **lock-time checks** are `CheckLockTime` and `CheckSequence`. The **oracle** packages all of this, with Core's hashes, into the abstract `Oracle` of the legacy Script interpreter.

## Formalization targets

### Goal — the strict-DER characterization
$$
\mathrm{IsValidSignatureEncoding}(sig) \iff sig = \mathtt{30}\,L\,\mathtt{02}\,|r|\,r\,\mathtt{02}\,|s|\,s\,ht \text{ with } r, s \text{ minimal positive big-endian integers and } |r|+|s| \le 66.
$$
This is `BitcoinSig.derEncode_complete` together with its converse `derEncode_valid`: the byte-indexed test of the source is exactly the canonical layout, in both directions. It is the content of BIP66 as a statement about byte strings rather than a procedure.

### Supporting milestones
1. **`SIGHASH_SINGLE` bug** (`sigHash_single_bug`): the hash is $1$ when there is no output at the input's index.
2. **What signatures commit to** (`sigHashLegacy_skeleton`, `sigHashWitnessV0_skeleton`): both hashes ignore scriptSigs and witnesses; (`sigHashLegacy_anyoneCanPay`): with the flag, only the signed input matters.
3. **Keys and S values** (`pubkeyValid_iff`, `normalizeS_low`, `overflow_rejected`).
4. **The checker** (`checkSig_empty`, `checkSig_dersig`, `checkSig_base_iff`): an empty signature is a clean `false`; with `DERSIG` a malformed one is a script error; the legacy verdict is ECDSA on the legacy sighash of the signature-deleted script code.
5. **Byte-level parsing** (`parseScript_p2pkh`): the P2PKH bytes parse to the interpreter's P2PKH instructions.
6. **The concrete P2PKH theorem** (`p2pkh_concrete`): the Script mission's `p2pkh_correct`, instantiated with Core's hashes and checker.

## What the result establishes

With this mission the signature-related rules of the pinned source are kernel-checked semantics rather than prose: what shape a signature must have, what it signs, and what accepting it means in terms of the curve equations. The characterization of strict DER removes a class of malleability by construction. The sighash theorems are the facts that transaction malleability arguments and the segregated-witness design rest on. The concrete P2PKH theorem closes the loop the Script mission opened: the template is correct with the real cryptography, modulo nothing but the mathematics of the curve.

What is deliberately not claimed: that the curve operations are constant-time, that the group law holds (the verifier is a function; its correctness as a signature scheme is a cryptographic, not a consensus, property), or anything about `OP_CODESEPARATOR` positions, which the legacy interpreter of the Script mission does not track (the oracle's script code is the executed script, exact for separator-free scripts). Signature caching, the precomputed-transaction-data caches and the sighash midstate cache are optimizations with the same result and are not modeled.

Status: all statements are open with intentional placeholder proofs. The definitions have been checked by evaluation against the BIP340 test vectors, the BIP143 worked example, independently generated ECDSA signatures, and a reference implementation of the legacy serializer.

## Where the obvious argument fails

The strict-DER characterization is byte-index chasing: the source reads `sig[4]`, `sig[5 + lenR]`, `sig[lenR + 7]`, and the proof must relate these to the slices $r$ and $s$ and show the three leading-zero rules are exactly minimality of the big-endian integers. The converse direction needs the cuts at $4$, $4 + |r|$, $6 + |r|$ and the end to reassemble the string. The sighash theorems look definitional but require relating `getD` on the input list to the projected skeleton under `ANYONECANPAY` (one input), `SINGLE` (outputs truncated) and the blanking rules. The checker characterization has to split the signature into body and hash-type byte in both directions.

## Formalization scope

Field and scalar arithmetic are on `Nat` modulo $p$ and $n$, with inverses by Fermat and explicit fuel for exponentiation and scalar multiplication. Byte strings are `List (BitVec 8)`; the transaction type is the serialization mission's. Policy flags (`LOW_S`, `STRICTENC`, `WITNESS_PUBKEYTYPE`, `NULLFAIL`, `CONST_SCRIPTCODE`) are carried where they shape the control flow but are off in block validation. Tapscript signature checking (BIP341/342 sighash, `OP_CHECKSIGADD`) belongs to the Taproot mission.

A trivializing formalization would define the strict-DER test by the layout, or the sighash by what it should depend on; here both are the source's procedures and the layout and dependence are theorems. No Mathlib is required; the development imports only `Std`.

## Selected references

- Bitcoin Core contributors. *`script/interpreter.cpp`*, *`pubkey.cpp`*, *`script/script.cpp`*, and libsecp256k1 `eckey_impl.h`, `ecdsa_impl.h`, `modules/schnorrsig/main_impl.h` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/tree/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src)
- Pieter Wuille. *BIP66: Strict DER signatures*, 2015. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0066.mediawiki)
- Johnson Lau, Pieter Wuille. *BIP143: Transaction Signature Verification for Version 0 Witness Program*, 2016. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0143.mediawiki)
- Pieter Wuille, Jonas Nick, Tim Ruffing. *BIP340: Schnorr Signatures for secp256k1*, 2020. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0340.mediawiki)
- Certicom Research. *SEC 2: Recommended Elliptic Curve Domain Parameters*, v2.0, 2010. [Standard](https://www.secg.org/sec2-v2.pdf)
