SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, "
       "IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), "
       "EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; "
       "GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; "
       "secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); "
       "BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7")
TAGS = ["bitcoin", "consensus", "ecdsa", "schnorr", "sighash", "der", "secp256k1", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinSig",
    "definition_title": "Signature encodings, signature hashes, secp256k1 ECDSA and Schnorr verification, and the transaction signature checker",
    "natural_language_statement": r"""**secp256k1.** $p = 2^{256} - 2^{32} - 977$, the order $n$, the generator $G$; `powMod` is square-and-multiply with explicit fuel, `finv`/`ninv` are Fermat inverses; a `Point` is an affine pair or infinity; `padd` is affine addition with the doubling and inverse cases; `pmul` is double-and-add. `liftXParity` is `secp256k1_ge_set_xo_var` (square root by $(p+1)/4$, parity selection); `parsePubkey` is `secp256k1_eckey_pubkey_parse` (33-byte `02`/`03`, 65-byte `04`/`06`/`07` with coordinates below $p$, on-curve and, for hybrid, parity check); `pubkeyValid` is `CPubKey::IsValid` (the header byte announces the length). `isHighS` is $s > n/2$, `normalizeS` replaces a high $s$ by $n - s$.

**Signatures.** `parseDerLax` is `ecdsa_signature_parse_der_lax` with its exact control flow: `none` where it returns $0$ (missing tags, length overruns, a long-form length of 4 or more significant bytes), `some (0,0)` where an integer has more than 32 significant bytes or a value at or above $n$ (the "correctly parsed but invalid" signature), trailing bytes ignored. `ecdsaVerifyRaw` is `secp256k1_ecdsa_sig_verify`: $r, s \in [1, n)$, $u_1 = e s^{-1}$, $u_2 = r s^{-1}$, $R = u_1 G + u_2 Q \ne \infty$ and $R_x \bmod n = r$. `pubkeyVerify` is `CPubKey::Verify`: valid and parsable key, lax-parsed signature, $s$ normalized, message reduced modulo $n$. `checkLowS` is `CPubKey::CheckLowS`. `schnorrVerify` is BIP340 / `secp256k1_schnorrsig_verify` with `taggedHash`.

**Byte-level scripts.** `getOp` is `GetScriptOp` (direct pushes, `PUSHDATA1/2/4`, `none` on a truncated push); `parseScript` parses a whole script; `pushBytes` is `CScript() << vch`; `findAndDelete` is `FindAndDelete` (occurrences removed at instruction boundaries, count returned); `serScriptCode` is `SerializeScriptCode` (`OP_CODESEPARATOR`s dropped, length-prefixed).

**Signature hashes.** `serSigTx` is `CTransactionSignatureSerializer` (`ANYONECANPAY` keeps only the signed input, other inputs' scripts blanked, their sequences zeroed under `SINGLE`/`NONE`, outputs truncated under `SINGLE`, dropped under `NONE`); `sigHashLegacy` is `SignatureHash` for `SigVersion::BASE` with the `SIGHASH_SINGLE` bug returning `uint256::ONE`; `sigHashWitnessV0` is the BIP143 algorithm (hashPrevouts, hashSequence, hashOutputs under the same flags, the amount, the script code).

**Encoding checks and the checker.** `isValidSignatureEncoding` is the strict-DER test (BIP66) byte for byte; `isLowDERSignature`, `isCompressedOrUncompressedPubKey`, `isCompressedPubKey`, `isDefinedHashtypeSignature`, `checkSignatureEncoding`, `checkPubKeyEncoding` under `SigFlags` (`dersig` is the only mainnet consensus flag; `lowS`, `strictenc`, `witnessPubkeyType` are policy and carried for fidelity). `checkECDSASignature` is the checker's method (hash type = last byte, witness v0 needs a non-negative amount); `checkSigPreTapscript` is `EvalChecksigPreTapscript` (`FindAndDelete` of the signature push for legacy scripts, encoding checks as `none`, verdict as `some`). `checkLockTime`/`checkSequence` are the checker's lock-time methods (`LOCKTIME_THRESHOLD`, `SEQUENCE_FINAL`, BIP68 masks). `legacyOracle` assembles Core's hashes, the checker and the lock-time checks into the `BitcoinScript.Oracle` of the legacy interpreter for a given script code.

**Auxiliary.** `p2pkhBytes` is the P2PKH output script as bytes; `sameSkeleton` relates transactions differing only in scriptSigs and witnesses; `minimalInt` and `derEncode` describe the DER layout.

**Formalization Note.** The script code handed to the oracle is the executed script, which is exact for scripts without `OP_CODESEPARATOR`. Field and scalar arithmetic are on `Nat` modulo $p$ and $n$; no claim about libsecp256k1's constant-time implementation is made, only about its mathematical semantics. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinSig.sigHash_single_bug": dict(title="The SIGHASH_SINGLE bug returns the hash 1",
    nl=r"""For every script code, transaction, input index $nIn$ and hash type with $(\text{hashType} \,\&\, \mathtt{0x1f}) = \mathtt{SIGHASH\_SINGLE}$ and $|\mathrm{vout}| \le nIn$: the legacy signature hash is `uint256::ONE` — the historical quirk by which such a signature commits to nothing.""",
    ms=("SignatureHash — the SIGHASH_SINGLE bug", "Immediate from the first test of SignatureHash.")),
"BitcoinSig.sigHashLegacy_skeleton": dict(title="The legacy sighash ignores scriptSigs and witnesses",
    nl=r"""For every script code, index and hash type, two transactions with the same version, outputs, lock time, and the same prevouts and sequence numbers in order have the same legacy signature hash. Signatures therefore never sign other signatures.""",
    ms=("SignatureHash — independence of scriptSigs", "The serializer reads only prevouts, sequences, the script code, outputs, version and lock time.")),
"BitcoinSig.sigHashLegacy_anyoneCanPay": dict(title="ANYONECANPAY signs only the signed input",
    nl=r"""With the `SIGHASH_ANYONECANPAY` bit set, the legacy hash of two transactions that agree on version, outputs, lock time and on the prevout and sequence of the signed input is the same, whatever their other inputs.""",
    ms=("SignatureHash — ANYONECANPAY", "One input is serialized, and it is the signed one.")),
"BitcoinSig.sigHashWitnessV0_skeleton": dict(title="The BIP143 sighash ignores scriptSigs and witnesses",
    nl=r"""For every script code, index, hash type and amount, two transactions with the same skeleton have the same BIP143 signature hash.""",
    ms=("BIP143 — independence of scriptSigs", "The prevout, sequence and output hashes are over the skeleton.")),
"BitcoinSig.pubkeyValid_iff": dict(title="CPubKey::IsValid characterized",
    nl=r"""A byte string is a valid `CPubKey` iff it has 33 bytes with header `02`/`03`, or 65 bytes with header `04`/`06`/`07`.""",
    ms=("CPubKey::IsValid — characterization", "Case analysis on the header byte.")),
"BitcoinSig.normalizeS_low": dict(title="Normalization yields a low S",
    nl=r"""For every $s < n$, `isHighS (normalizeS s) = false`: after normalization $s \le n/2$.""",
    ms=("secp256k1 — S normalization", "Arithmetic on the odd order.")),
"BitcoinSig.overflow_rejected": dict(title="An overflowed lax parse never verifies",
    nl=r"""If `parseDerLax sig = some (0, 0)` — the zero signature that the lax parser substitutes on overflow — then `pubkeyVerify pk hash sig = false` for every key and hash.""",
    ms=("CPubKey::Verify — overflow", "r = 0 is rejected by secp256k1_ecdsa_sig_verify.")),
"BitcoinSig.checkSig_empty": dict(title="An empty signature is a clean failure",
    nl=r"""With the public-key encoding check passing, `checkSigPreTapscript … [] pk = some false`: an empty signature passes `CheckSignatureEncoding` and makes `CheckECDSASignature` return `false` — a script-level `false`, not a script error.""",
    ms=("EvalChecksig — empty signature", "The empty case of CheckSignatureEncoding and the checker.")),
"BitcoinSig.checkSig_dersig": dict(title="With DERSIG a non-DER signature is a script error",
    nl=r"""If the `DERSIG` flag is set, a non-empty signature failing `IsValidSignatureEncoding` makes `checkSigPreTapscript` return `none` (the script fails), for every transaction, key and script code.""",
    ms=("EvalChecksig — BIP66 enforcement", "The DER test precedes the checker.")),
"BitcoinSig.checkSig_base_iff": dict(title="The legacy checker unfolded",
    nl=r"""`checkSigPreTapscript f tx nIn amount BASE scriptCode sig pk = some true` iff `CheckSignatureEncoding` and `CheckPubKeyEncoding` pass, the key is valid, and $sig = sig' ++ [ht]$ with `pubkeyVerify pk (sigHashLegacy (FindAndDelete scriptCode ⟨sig⟩) tx nIn ht) sig'`: the signature check is ECDSA verification of the legacy sighash of the signature-deleted script code, under the hash type given by the last byte.""",
    ms=("EvalChecksigPreTapscript — characterization", "Unfold the checker; the last byte is the hash type.")),
"BitcoinSig.parseScript_p2pkh": dict(title="The P2PKH bytes parse to the interpreter's P2PKH script",
    nl=r"""For every 20-byte $h$: `parseScript (p2pkhBytes h) = some (p2pkhScript h)` — the byte-level `GetScriptOp` parse of `76 a9 14 <h> 88 ac` is the instruction list the Script mission's theorems are stated on.""",
    ms=("GetScriptOp — P2PKH", "Five instructions, one 20-byte push.")),
"BitcoinSig.derEncode_valid": dict(title="Strict DER accepts the canonical layout",
    nl=r"""For minimal big-endian integers $r, s$ (non-empty, top bit clear, no leading zero unless needed) with $|r| + |s| \le 66$ and any hash-type byte, `isValidSignatureEncoding (derEncode r s ht) = true`.""",
    ms=("IsValidSignatureEncoding — soundness", "Evaluate the fourteen tests on the layout.")),
"BitcoinSig.derEncode_complete": dict(title="Strict DER accepts only the canonical layout",
    nl=r"""Every signature `IsValidSignatureEncoding` accepts is `derEncode r s ht` for minimal $r, s$ with $|r| + |s| \le 66$. Together with soundness this characterizes BIP66's strict encoding: exactly the sequences `30 L 02 |r| r 02 |s| s ht` with minimal positive integers and at most 73 bytes.

**Formalization Note.** The characterization is the goal because it is what every later layer consumes: the DERSIG rule is "the signature has this shape", and with it the lax parser and the strict test agree on their accepted values.""",
    ms=None),
}
ORDER = ["BitcoinSig.sigHash_single_bug","BitcoinSig.sigHashLegacy_skeleton","BitcoinSig.sigHashLegacy_anyoneCanPay","BitcoinSig.sigHashWitnessV0_skeleton",
         "BitcoinSig.pubkeyValid_iff","BitcoinSig.normalizeS_low","BitcoinSig.overflow_rejected","BitcoinSig.checkSig_empty","BitcoinSig.checkSig_dersig",
         "BitcoinSig.checkSig_base_iff","BitcoinSig.parseScript_p2pkh","BitcoinSig.derEncode_valid","BitcoinSig.derEncode_complete","BitcoinSig.p2pkh_concrete"]
THEOREMS["BitcoinSig.p2pkh_concrete"] = dict(title="P2PKH is correct against Core's concrete signature checker",
    nl=r"""For every flag setting, transaction, input index, amount and signature version, and every signature, key and hash within the 520-byte push limit:
$$\mathrm{verifyScriptPlain}\big(\mathrm{legacyOracle}(tx, nIn, \text{p2pkhBytes}(h)),\ [\langle sig\rangle, \langle pk\rangle],\ \mathtt{DUP\ HASH160}\ \langle h\rangle\ \mathtt{EQUALVERIFY\ CHECKSIG}\big) = \mathtt{true}$$
$$\iff \mathrm{Hash160}(pk) = h \;\wedge\; \mathrm{checkSigPreTapscript}(tx, nIn, \text{p2pkhBytes}(h), sig, pk) = \mathrm{some}\ \mathtt{true},$$
where the oracle is Core's RIPEMD-160∘SHA-256 and the pre-tapscript checker. Composed with `checkSig_base_iff`, the right-hand side is: valid encodings, a valid key, and ECDSA verification of the legacy sighash. This instantiates the Script mission's abstract P2PKH theorem with the concrete cryptography and sighash of the pinned source.""",
    ms=("P2PKH — concrete instantiation", "Instantiate BitcoinScript.p2pkh_correct with the legacy oracle."))
