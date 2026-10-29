SRC = ("BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': "
       "https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; "
       "Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, "
       "OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime "
       "(src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147")
TAGS = ["bitcoin", "lightning", "bolt3", "htlc", "script", "cltv", "bip65", "checkmultisig", "p2wsh", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinHtlc",
    "definition_title": "The Lightning offered and received HTLC witness scripts and their spending conditions",
    "natural_language_statement": r"""Names over the script, signature, verification and `to_local` missions; nothing of Core is re-transcribed.

**`offeredScript revHash remoteKey localKey payHash`** / **`offeredBytes …`** — the BOLT #3 offered-HTLC witness script `OP_DUP OP_HASH160 <revHash> OP_EQUAL OP_IF OP_CHECKSIG OP_ELSE <remoteKey> OP_SWAP OP_SIZE 32 OP_EQUAL OP_NOTIF OP_DROP 2 OP_SWAP <localKey> 2 OP_CHECKMULTISIG OP_ELSE OP_HASH160 <payHash> OP_EQUALVERIFY OP_CHECKSIG OP_ENDIF OP_ENDIF`, parsed and as `CScript` serializes it (`2` as `OP_2`, `32` as the one-byte push `0x20`).

**`receivedScript … expiry`** / **`receivedBytes …`** — the received-HTLC script, whose inner branches are `OP_IF OP_HASH160 <payHash> OP_EQUALVERIFY 2 OP_SWAP <localKey> 2 OP_CHECKMULTISIG OP_ELSE OP_DROP <expiry> OP_CHECKLOCKTIMEVERIFY OP_DROP OP_CHECKSIG OP_ENDIF`, the expiry encoded by the `to_local` mission's `numInstr`/`numBytes`.

**`CltvPasses f o expiry`** — what `OP_CHECKLOCKTIMEVERIFY` lets through: the flag is off, or `expiry` is non-negative and the oracle's `checkLockTime expiry` holds.

**`OfferedSpend f o revHash remoteKey localKey payHash st`** — for a witness stack `st` (top first): the revocation path `[pk, sig]` with `hash160 pk = revHash` and `sig` valid for `pk`; the preimage path `[preimage, sig]` with `hash160 preimage ≠ revHash`, a 32-byte preimage hashing to `payHash`, and `sig` valid for `remoteKey`; or the timeout path `[x, localSig, remoteSig, dummy]` with `hash160 x ≠ revHash`, `x` not 32 bytes, the 2-of-2 `multisigLoop o [localSig, remoteSig] [localKey, remoteKey]` passing, and an empty dummy when `NULLDUMMY` is enforced.

**`ReceivedSpend … expiry st`** — the revocation path as above; the success path `[preimage, localSig, remoteSig, dummy]` (32-byte preimage hashing to `payHash`, not to `revHash`, the 2-of-2 passing, dummy as above); or the timeout path `[x, sig]` with `hash160 x ≠ revHash`, `x` not 32 bytes, `CltvPasses`, and `sig` valid for `remoteKey`.

**Formalization Note.** `multisigLoop`, `Flags`, `Oracle`, `evalScript` are the script mission's; `legacyOracle`, `checkLockTime`, `parseScript` the signature mission's; `verifyScript`, `topTrue` the verification mission's; `numInstr`, `inputSequence` the `to_local` mission's. The two 20-byte hashes are free parameters. Only `Std` is imported.""",
}

B = "For pushed strings of at most 520 bytes"
THEOREMS = {
"BitcoinHtlc.cltv_step": dict(title="OP_CHECKLOCKTIMEVERIFY on a serialized number passes exactly when CltvPasses holds",
    nl=r"""For a state whose stack top is `serialize expiry` with $|{\rm expiry}| < 2^{32}$: `execOp f o true OP_CHECKLOCKTIMEVERIFY s = if CltvPasses f o expiry then some s else none`.""", ms=None),
"BitcoinHtlc.multisig_two": dict(title="A 2-of-2 CHECKMULTISIG loop passes iff each signature matches its key in order",
    nl=r"""`multisigLoop o [s₁, s₂] [k₁, k₂] = some true ↔ o.checkSig s₁ k₁ = some true ∧ o.checkSig s₂ k₂ = some true`. With two signatures and two keys the interpreter's matching loop cannot skip a key.""", ms=None),
"BitcoinHtlc.offered_revocation": dict(title="Offered HTLC, revocation path", nl=B + r""" and `hash160 pk = revHash`: `evalScript f o [pk, sig] (offeredScript …) = (o.checkSig sig pk).map (fun ok => [boolBytes ok])`.""", ms=None),
"BitcoinHtlc.offered_preimage": dict(title="Offered HTLC, preimage path", nl=B + r""", `hash160 preimage ≠ revHash` and a 32-byte preimage: the script leaves the remote-key signature check if `hash160 preimage = payHash`, and fails otherwise.""", ms=None),
"BitcoinHtlc.offered_timeout": dict(title="Offered HTLC, timeout path (2-of-2)", nl=B + r""", `hash160 x ≠ revHash` and `x` not 32 bytes: on `[x, localSig, remoteSig, dummy]` the script fails if the 2-of-2 loop errors, fails if `NULLDUMMY` is on and the dummy is nonempty, and otherwise leaves the loop's verdict.""",
    ms=("The three offered paths in closed form", "Symbolic execution through the nested conditionals, with the skipped branches' instructions shown inert.")),
"BitcoinHtlc.offered_spends_iff": dict(title="Offered HTLC: the three spending conditions, for any witness stack", nl=B + r""" and any stack `st`: there is a result of `evalScript f o st (offeredScript …)` with exactly one element that is true, iff `OfferedSpend f o … st`. No other stack shape, and no stack beyond the 1000-element limit, succeeds.""", ms=None),
"BitcoinHtlc.received_revocation": dict(title="Received HTLC, revocation path", nl=r"""As `offered_revocation`, for the received script.""", ms=None),
"BitcoinHtlc.received_success": dict(title="Received HTLC, success path (preimage and 2-of-2)", nl=B + r""", $|{\rm expiry}| < 2^{32}$, `hash160 preimage ≠ revHash` and a 32-byte preimage: on `[preimage, localSig, remoteSig, dummy]` the script fails unless `hash160 preimage = payHash`, then behaves as the offered timeout path's 2-of-2 check.""", ms=None),
"BitcoinHtlc.received_timeout": dict(title="Received HTLC, timeout path (CLTV)", nl=B + r""", `hash160 x ≠ revHash` and `x` not 32 bytes: on `[x, sig]` the script fails unless `CltvPasses f o expiry`, then leaves the remote-key signature check.""",
    ms=("The three received paths in closed form", "As for the offered script, with `cltv_step` at the lock-time check.")),
"BitcoinHtlc.received_spends_iff": dict(title="Received HTLC: the three spending conditions, for any witness stack", nl=B + r""", $|{\rm expiry}| < 2^{32}$ and any stack `st`: the witness-v0 success condition holds iff `ReceivedSpend f o … expiry st`.""", ms=None),
"BitcoinHtlc.parseScript_offered": dict(title="The offered script's byte form parses to its instruction form", nl=B + r""": `parseScript (offeredBytes …) = some (offeredScript …)`.""", ms=None),
"BitcoinHtlc.parseScript_received": dict(title="The received script's byte form parses to its instruction form", nl=B + r""" and $|{\rm expiry}| < 2^{32}$: `parseScript (receivedBytes …) = some (receivedScript …)`.""", ms=None),
"BitcoinHtlc.offered_p2wsh_spend": dict(title="The offered HTLC output under VerifyScript", nl=r"""For a context with the `WITNESS` flag and pushed strings of at most 520 bytes, any witness `ws`: `verifyScript tap c [] (witnessBytes 0 (sha256 (offeredBytes …))) (ws ++ [offeredBytes …]) = true` iff the program is a true value, every witness element is at most 520 bytes, and `OfferedSpend` holds for the flags of $c$ and the signature mission's `legacyOracle` of $c$'s transaction on the reversed witness. So the output is spent only by the revocation key, by the remote key with the payment preimage, or by both HTLC keys on the timeout transaction.""", ms=None),
"BitcoinHtlc.received_p2wsh_spend": dict(title="The received HTLC output under VerifyScript", nl=r"""As `offered_p2wsh_spend` for the received script with $|{\rm expiry}| < 2^{32}$: the output is spent only by the revocation key, by both HTLC keys with the payment preimage on the success transaction, or by the remote key after the lock time. Together with the `to_local` mission this covers every script of a BOLT #3 commitment transaction (non-anchor form).""", ms=None),
"BitcoinHtlc.cltv_concrete": dict(title="With CLTV active, the operand check is the transaction's CheckLockTime", nl=r"""For `f.cltv = true` and $0 \le {\rm expiry}$: `CltvPasses f (legacyOracle sf tx nIn amount v sc) expiry ↔ checkLockTime tx nIn expiry = true`.""", ms=None),
"BitcoinHtlc.checkLockTime_iff": dict(title="CheckLockTime for a block-height expiry", nl=r"""For $0 \le {\rm expiry} < 500{,}000{,}000$: `checkLockTime tx nIn expiry = true` iff the transaction's `nLockTime` is also a block height (below 500,000,000), `expiry ≤ nLockTime`, and the input's `nSequence` is not `0xffffffff`. BIP65 as `GenericTransactionSignatureChecker::CheckLockTime` implements it.""", ms=None),
}
ORDER = ["BitcoinHtlc.cltv_step", "BitcoinHtlc.multisig_two", "BitcoinHtlc.offered_revocation", "BitcoinHtlc.offered_preimage",
         "BitcoinHtlc.offered_timeout", "BitcoinHtlc.offered_spends_iff", "BitcoinHtlc.received_revocation",
         "BitcoinHtlc.received_success", "BitcoinHtlc.received_timeout", "BitcoinHtlc.received_spends_iff",
         "BitcoinHtlc.parseScript_offered", "BitcoinHtlc.parseScript_received", "BitcoinHtlc.offered_p2wsh_spend",
         "BitcoinHtlc.received_p2wsh_spend", "BitcoinHtlc.cltv_concrete", "BitcoinHtlc.checkLockTime_iff"]
