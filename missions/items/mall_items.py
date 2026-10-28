SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript (SCRIPT_ERR_WITNESS_MALLEATED, SCRIPT_ERR_WITNESS_MALLEATED_P2SH), "
       "src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; "
       "CTransaction::ComputeHash, SerializeTransaction (primitives/transaction.h, transaction.cpp); CheckInputScripts (validation.cpp); BIP141 (Transaction ID)")
TAGS = ["bitcoin", "consensus", "segwit", "bip141", "malleability", "txid", "lightning", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinMalleability",
    "definition_title": "Transaction intent: the signature-free content of a transaction, and spends of native witness programs",
    "natural_language_statement": r"""Three names over the serialization mission's `Tx`, the block mission's ledger, and the VerifyScript mission's `isWitnessProgram`; nothing is re-transcribed.

**`Intent`** — a record of a version, a list of (outpoint, sequence number) pairs, a list of outputs, and a lock time: what the sender decides. `scriptSig`s and witnesses are not part of it.

**`intentOf tx`** — the intent of a transaction: its version, the (prevout, `nSequence`) of each input in order, its outputs, its lock time.

**`ofIntent t`** — the canonical transaction of an intent: the same fields, every `scriptSig` empty, every witness empty.

**`SpendsWitnessPrograms u tx`** — every input of `tx` spends, in the ledger `u`, an output whose `scriptPubKey` is a native witness program (`CScript::IsWitnessProgram`: `OP_0` or `OP_1`..`OP_16` followed by a single push of 2 to 40 bytes).

**Formalization Note.** `txid` is the serialization mission's double SHA-256 of the witness-stripped serialization; `inputScriptsOk` is the block mission's `CheckInputScripts` (the complete `VerifyScript` for every input against the spent outputs); `verifyScript` is the VerifyScript mission's dispatch. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinMalleability.native_scriptSig_empty": dict(title="An input spending a native witness program has an empty scriptSig when its script verifies",
    nl=r"""For script flags with `WITNESS` set, a ledger $u$ and a transaction whose `CheckInputScripts` succeeds: every input whose spent output is a native witness program has `scriptSig = []`. (`VerifyScript` returns `SCRIPT_ERR_WITNESS_MALLEATED` otherwise; the VerifyScript mission's `native_witness_malleated` lifted to the block mission's per-input loop.)""",
    ms=("SCRIPT_ERR_WITNESS_MALLEATED at the block level", "From the published `native_witness_malleated` and the index of the input in `CheckInputScripts`.")),
"BitcoinMalleability.txid_of_intent": dict(title="For native-SegWit spends the txid is the txid of the intent's canonical transaction",
    nl=r"""For flags with `WITNESS`, a ledger $u$, and a transaction whose scripts verify and whose inputs all spend native witness programs: `txid tx = txid (ofIntent (intentOf tx))`. The txid hashes the witness-stripped serialization; with every `scriptSig` forced empty, nothing chosen by a signer or a third party remains in the hashed bytes.""",
    ms=("The stripped transaction is the canonical one", "`txid_strip` of the serialization mission, and the stripped transaction equals `ofIntent (intentOf tx)` when every `scriptSig` is empty.")),
"BitcoinMalleability.txid_determined": dict(title="Non-malleability: same intent, verifying scripts, native witness programs — same txid",
    nl=r"""For flags with `WITNESS`, a ledger $u$ and two transactions with the same intent (same version, prevouts, sequence numbers, outputs and lock time), both of whose scripts verify against $u$, where the inputs spend native witness programs: `txid tx = txid tx'`. No choice of signatures or witnesses — by the signer, or by a third party re-encoding them — changes the identifier of a valid spend. This is the BIP141 property that second-layer protocols (payment channels) rely on to refer to unconfirmed transactions by txid.""",
    ms=None),
"BitcoinMalleability.p2sh_wrapped_scriptSig": dict(title="A P2SH-wrapped witness spend has the single push of its witness program as scriptSig",
    nl=r"""For `VerifyScript` with the `P2SH` and `WITNESS` flags, a P2SH `scriptPubKey`, a non-empty witness and a `scriptSig` on which it succeeds: the `scriptSig` evaluates to a stack whose top element `redeem` is a witness program, and the `scriptSig` is exactly the single push of `redeem` (`SCRIPT_ERR_WITNESS_MALLEATED_P2SH` otherwise). The `scriptSig` of a wrapped witness spend is therefore determined by the redeem script the output's hash commits to.""",
    ms=("SCRIPT_ERR_WITNESS_MALLEATED_P2SH", "Case analysis on the P2SH branch of `VerifyScript`: a P2SH script is not a witness program, push-only, the redeem script's witness-program test, and the exact-push test.")),
}
ORDER = ["BitcoinMalleability.native_scriptSig_empty", "BitcoinMalleability.txid_of_intent",
         "BitcoinMalleability.txid_determined", "BitcoinMalleability.p2sh_wrapped_scriptSig"]
