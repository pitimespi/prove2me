SRC = ("BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: "
       "https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; "
       "Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), "
       "GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141")
TAGS = ["bitcoin", "lightning", "bolt3", "anchors", "htlc", "script", "csv", "bip112", "p2wsh", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinAnchors",
    "definition_title": "The Lightning anchor-output scripts (to_remote, anchor, CSV-1 HTLCs) and their spending conditions",
    "natural_language_statement": r"""Names over the script, signature, verification, `to_local` and HTLC missions; nothing of Core is re-transcribed. These are the BOLT #3 scripts with `option_anchors`, the form every modern channel uses.

**`toRemoteScript remoteKey`** / **`toRemoteBytes`** — `<remote_pubkey> OP_CHECKSIGVERIFY 1 OP_CHECKSEQUENCEVERIFY`. **`anchorScript fundingKey`** / **`anchorBytes`** — `<funding_pubkey> OP_CHECKSIG OP_IFDUP OP_NOTIF 16 OP_CHECKSEQUENCEVERIFY OP_ENDIF`. **`offeredScript …`**, **`receivedScript … expiry`** / their byte forms — the HTLC mission's scripts with `1 OP_CHECKSEQUENCEVERIFY OP_DROP` inserted after the inner `OP_ENDIF`, inside the outer `OP_ELSE`.

**`ToRemoteSpend f o remoteKey st`** — `st = [sig]` with `sig` valid for `remoteKey` and `CsvPasses f o 1`. **`AnchorSpend f o fundingKey st`** — `st = [sig]` and either `sig` valid for `fundingKey` (the key holder, at any time) or the check returns a clean `false` (as for the empty signature) and `CsvPasses f o 16` (anyone, after 16 blocks). **`OfferedSpend`**, **`ReceivedSpend`** — the HTLC mission's three paths each, with `CsvPasses f o 1` added to the two non-revocation paths.

**Formalization Note.** `CsvPasses`, `numInstr`, `inputSequence` are the `to_local` mission's; `CltvPasses`, `multisigLoop` the HTLC and script missions'; `legacyOracle`, `checkSequence`, `parseScript` the signature mission's; `verifyScript` the verification mission's. The 20-byte hashes are parameters. Only `Std` is imported.""",
}

B = "For pushed strings of at most 520 bytes"
T = {}
T["to_remote_spends_iff"] = ("to_remote: the spending condition, for any witness stack", B + r""" and any stack `st`: the witness-v0 success condition for `toRemoteScript remoteKey` holds iff `ToRemoteSpend f o remoteKey st`. `OP_CHECKSIGVERIFY` fails the script on anything but a passing check; the `1` pushed for the delay is the value left.""")
T["to_remote_eval"] = ("to_remote on its witness", r"""`evalScript f o [sig] (toRemoteScript k) = if o.checkSig sig k = some true ∧ CsvPasses f o 1 then some [[1]] else none`.""")
T["anchor_spends_iff"] = ("Anchor: the two spending conditions, for any witness stack", B + r""" and any stack: the success condition for `anchorScript fundingKey` holds iff `AnchorSpend f o fundingKey st`.""")
T["anchor_eval"] = ("Anchor on its witness, closed form", r"""`evalScript f o [sig] (anchorScript k)` is `none` if the check rejects the signature's encoding, `some [[1]]` if it passes (`OP_IFDUP` keeps the true, `OP_NOTIF` skips the delay), and `if CsvPasses f o 16 then some [[16]] else none` if it returns a clean `false`.""")
T["anchor_holder"] = ("Anchor, key-holder path", r"""If `o.checkSig sig k = some true` then `evalScript f o [sig] (anchorScript k) = some [[1]]`: the funding-key holder spends the anchor at any time.""")
T["anchor_anyone"] = ("Anchor, anyone-can-spend path", r"""If `o.checkSig sig k = some false` then `evalScript f o [sig] (anchorScript k) = if CsvPasses f o 16 then some [[16]] else none`: with a clean false (the empty signature), the anchor is spendable exactly after the 16-block delay.""")
T["offered_revocation"] = ("Offered HTLC (anchors), revocation path", r"""As the HTLC mission's: the revocation branch skips the delay suffix.""")
T["offered_preimage"] = ("Offered HTLC (anchors), preimage path", B + r""", `hash160 preimage ≠ revHash`, 32-byte preimage: `if hash160 preimage = payHash ∧ CsvPasses f o 1 then (checkSig sig remoteKey).map … else none`.""")
T["offered_timeout"] = ("Offered HTLC (anchors), timeout path", B + r""", `hash160 x ≠ revHash`, `x` not 32 bytes: on `[x, localSig, remoteSig, dummy]`, `if CsvPasses f o 1 then` the HTLC mission's 2-of-2 result `else none`.""")
T["offered_spends_iff"] = ("Offered HTLC (anchors): the three spending conditions, for any witness stack", B + r""" and any stack: the success condition holds iff `OfferedSpend f o … st`.""")
T["received_revocation"] = ("Received HTLC (anchors), revocation path", r"""As the HTLC mission's.""")
T["received_success"] = ("Received HTLC (anchors), success path", B + r""", $|{\rm expiry}| < 2^{32}$, 32-byte preimage not hashing to `revHash`: `if hash160 preimage = payHash ∧ CsvPasses f o 1 then` the 2-of-2 result `else none`.""")
T["received_timeout"] = ("Received HTLC (anchors), timeout path", B + r""", `hash160 x ≠ revHash`, `x` not 32 bytes: `if CltvPasses f o expiry ∧ CsvPasses f o 1 then (checkSig sig remoteKey).map … else none`.""")
T["received_spends_iff"] = ("Received HTLC (anchors): the three spending conditions, for any witness stack", B + r""", $|{\rm expiry}| < 2^{32}$ and any stack: the success condition holds iff `ReceivedSpend f o … expiry st`.""")
T["parseScript_toRemote"] = ("to_remote byte form parses", r"""`parseScript (toRemoteBytes k) = some (toRemoteScript k)` for a key of at most 520 bytes.""")
T["parseScript_anchor"] = ("Anchor byte form parses", r"""`parseScript (anchorBytes k) = some (anchorScript k)` for a key of at most 520 bytes.""")
T["parseScript_offered"] = ("Offered HTLC (anchors) byte form parses", B + r""": `parseScript (offeredBytes …) = some (offeredScript …)`.""")
T["parseScript_received"] = ("Received HTLC (anchors) byte form parses", B + r""" and $|{\rm expiry}| < 2^{32}$: `parseScript (receivedBytes …) = some (receivedScript …)`.""")
T["to_remote_p2wsh_spend"] = ("The to_remote output under VerifyScript", r"""With the `WITNESS` flag and a key of at most 520 bytes, any witness `ws`: `verifyScript` accepts `ws ++ [toRemoteBytes k]` for the P2WSH program of `toRemoteBytes k` iff the program is true, every element is at most 520 bytes, and `ToRemoteSpend` holds for the context's flags and `legacyOracle` on `ws.reverse`. The remote balance is spendable by the remote key only after one block (the CSV that makes anchors' fee-bumping safe).""")
T["anchor_p2wsh_spend"] = ("The anchor output under VerifyScript", r"""As above with `AnchorSpend`: the anchor is spent by the funding-key holder at any time, or by anyone with a clean-false signature after the delay.""")
T["offered_p2wsh_spend"] = ("The offered HTLC output (anchors) under VerifyScript", r"""As above with `OfferedSpend`.""")
T["received_p2wsh_spend"] = ("The received HTLC output (anchors) under VerifyScript", r"""As above with `ReceivedSpend` and $|{\rm expiry}| < 2^{32}$. With the `to_local` and HTLC missions this covers every script of a BOLT #3 commitment transaction in both the legacy and the anchors form.""")
T["anchor_anyone_concrete"] = ("Anyone can spend the anchor after the delay: the empty-signature witness under the concrete checker", r"""With the `WITNESS` and `CHECKSEQUENCEVERIFY` flags and a funding key of at most 520 bytes: `verifyScript tap c [] (witnessBytes 0 (sha256 (anchorBytes k))) [[], anchorBytes k] = true ↔ castToBool (sha256 (anchorBytes k)) = true ∧ checkSequence c.tx c.nIn 16 = true`. The empty signature is a clean false under consensus flags (the signature mission's `checkSig_empty`; no pubkey-encoding hypothesis is needed since `WITNESS_PUBKEYTYPE` is policy), so the spend reduces to Core's `CheckSequence` with operand 16.""")
T["anchor_anyone_delay"] = ("Anyone can spend the anchor after 16 blocks, in transaction terms", r"""Additionally for an input with flag-free `nSequence` below $2^{16}$: the empty-signature witness verifies iff the program is true, the transaction is version 2 or later, and `nSequence ≥ 16`. The anchor's "anyone can sweep it after 16 blocks" property, as consensus enforces it.""")
THEOREMS = {f"BitcoinAnchors.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinAnchors.anchor_spends_iff"]["ms"] = ("The anchor's two paths", "`OP_IFDUP` keeps a true verdict so `OP_NOTIF` skips the delay; a clean false is popped and the pushed 16 is checked and left.")
THEOREMS["BitcoinAnchors.received_spends_iff"]["ms"] = ("The CSV-1 suffix on every non-revocation path", "The HTLC mission's walks extended by `1 OP_CHECKSEQUENCEVERIFY OP_DROP` after the inner `OP_ENDIF`; the revocation branch skips it.")
ORDER = ["BitcoinAnchors." + k for k in ["to_remote_eval", "to_remote_spends_iff", "anchor_eval", "anchor_holder", "anchor_anyone", "anchor_spends_iff",
  "offered_revocation", "offered_preimage", "offered_timeout", "offered_spends_iff", "received_revocation", "received_success", "received_timeout",
  "received_spends_iff", "parseScript_toRemote", "parseScript_anchor", "parseScript_offered", "parseScript_received",
  "to_remote_p2wsh_spend", "anchor_p2wsh_spend", "offered_p2wsh_spend", "received_p2wsh_spend", "anchor_anyone_concrete", "anchor_anyone_delay"]]
