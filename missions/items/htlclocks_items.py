SRC = ("BOLT #3, HTLC-Timeout and HTLC-Success Transactions (locktime = cltv_expiry), Received HTLC Outputs: "
       "https://github.com/lightning/bolts/blob/master/03-transactions.md#htlc-timeout-and-htlc-success-transactions; "
       "Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsFinalTx (src/consensus/tx_verify.cpp) as the block mission's `isFinalTx`, "
       "ContextualCheckBlock (src/validation.cpp), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp); BIP65")
TAGS = ["bitcoin", "lightning", "bolt3", "htlc", "locktime", "bip65", "finality", "consensus", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinHtlcLocks",
    "definition_title": "Revocation spends and height-locked transactions",
    "natural_language_statement": r"""Two names over the HTLC and block missions.

**`RevocationSpend c script revHash pk sig`** — in verification context $c$ (transaction, input index, amount, flags), the witness's public key hashes (`hash160`) to the revocation hash and the signature verifies for it under the signature mission's `checkSigPreTapscript` with the witness-v0 sighash on `script`: the revocation path of an HTLC output.

**`HeightLocked tx`** — the transaction's `nLockTime` is nonzero and below `LOCKTIME_THRESHOLD` (500,000,000), i.e. a block height, as for a BOLT #3 HTLC-timeout transaction whose lock time is `cltv_expiry`.

**Formalization Note.** `isFinalTx`, `LOCKTIME_THRESHOLD`, `SEQUENCE_FINAL` are the block mission's (`BitcoinBlockV2`); `receivedBytes`, `ReceivedSpend` the HTLC mission's; `verifyScript`, `Ctx` the verification mission's. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinHtlcLocks.isFinalTx_height": dict(title="IsFinalTx for a height-locked transaction with a non-final input",
    nl=r"""For a transaction with `HeightLocked tx` and some input $i$ (in range) whose `nSequence` is not `0xffffffff`: `isFinalTx tx height blockTime = true ↔ tx.nLockTime < height`. The lock time is enforced as a block height, and the non-final input blocks the `SEQUENCE_FINAL` bypass.""", ms=None),
"BitcoinHtlcLocks.presigned_timeout_height": dict(title="A pre-signed HTLC-timeout transaction confirms only above the expiry height",
    nl=r"""For $0 < {\rm expiry} < 500{,}000{,}000$, a transaction with `nLockTime = expiry` and an in-range input whose `nSequence` is not final: `isFinalTx tx height blockTime = true` implies `expiry < height`. BOLT #3's HTLC-timeout transaction, which spends an offered HTLC with the 2-of-2 signatures, is built exactly so.""", ms=None),
"BitcoinHtlcLocks.received_spend_height": dict(title="A received HTLC cannot be timed out before its expiry at the consensus level",
    nl=r"""For a context $c$ with the `WITNESS` and `CHECKLOCKTIMEVERIFY` flags, keys and hashes of at most 520 bytes, $0 < {\rm expiry} < 500{,}000{,}000$, and $c$'s input index in range: if `verifyScript` accepts the two-element witness `[sig, pk]` for the pay-to-witness-script-hash output of `receivedBytes revHash remoteKey localKey payHash expiry`, and $c$'s transaction is final at `height` (`isFinalTx c.tx height blockTime = true`, which `ContextualCheckBlock` requires of every transaction in a block at that height), then either `RevocationSpend c (receivedBytes …) revHash pk sig`, or `expiry < height`. The HTLC mission's script conditions and the block mission's finality rule compose: besides the revocation key, the only two-element witness is the timeout path, whose `OP_CHECKLOCKTIMEVERIFY` forces `nLockTime ≥ expiry` and a non-final input, and finality then forces `nLockTime < height`.""",
    ms=None),
}
ORDER = ["BitcoinHtlcLocks.isFinalTx_height", "BitcoinHtlcLocks.presigned_timeout_height", "BitcoinHtlcLocks.received_spend_height"]
