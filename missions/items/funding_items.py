SRC = ("BOLT #3, Funding Transaction Output: https://github.com/lightning/bolts/blob/master/03-transactions.md#funding-transaction-output; "
       "Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKMULTISIG), ExecuteWitnessScript, VerifyWitnessProgram "
       "(src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP141, BIP147")
TAGS = ["bitcoin", "lightning", "bolt3", "funding", "multisig", "checkmultisig", "p2wsh", "bip147", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinFunding",
    "definition_title": "The Lightning funding output script and its spending condition",
    "natural_language_statement": r"""Names over the script, verification and `to_local` missions.

**`fundingScript pubkey1 pubkey2`** / **`fundingBytes`** — the BOLT #3 funding witness script `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`, parsed and as `CScript` serializes it (`2` as `OP_2`).

**`FundingSpend f o pubkey1 pubkey2 st`** — for a witness stack `st` (top first): `st = [sig2, sig1, dummy]` with `sig1` valid for `pubkey1`, `sig2` valid for `pubkey2` (the oracle's `checkSig`), and an empty dummy when `NULLDUMMY` is enforced. In `CScriptWitness` order this is BOLT #3's `0 <signature_for_pubkey1> <signature_for_pubkey2>`.

**Formalization Note.** `numInstr`, `numBytes` are the `to_local` mission's; `multisigLoop`, `Flags`, `Oracle`, `evalScript` the script mission's; `verifyScript`, `topTrue` the verification mission's. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinFunding.funding_witness": dict(title="The funding script on the BOLT #3 witness", nl=r"""For keys of at most 520 bytes: `evalScript f o [sig2, sig1, dummy] (fundingScript pubkey1 pubkey2)` is the 2-of-2 loop's verdict `multisigLoop o [sig2, sig1] [pubkey2, pubkey1]` as a single stack element, `none` if the loop errors or if `NULLDUMMY` is on and the dummy is nonempty.""", ms=None),
"BitcoinFunding.funding_spends_iff": dict(title="The funding output's single spending condition, for any witness stack", nl=r"""For keys of at most 520 bytes and any stack `st`: the witness-v0 success condition for `fundingScript pubkey1 pubkey2` holds iff `FundingSpend f o pubkey1 pubkey2 st`. The HTLC mission's `multisig_two` turns the loop verdict into the two signature checks in order; any other stack shape fails.""", ms=None),
"BitcoinFunding.parseScript_funding": dict(title="The funding script's byte form parses to its instruction form", nl=r"""For keys of at most 520 bytes: `parseScript (fundingBytes pubkey1 pubkey2) = some (fundingScript pubkey1 pubkey2)`.""", ms=None),
"BitcoinFunding.funding_p2wsh_spend": dict(title="The funding output under VerifyScript: the channel's funds move only with both signatures", nl=r"""For a context with the `WITNESS` flag, keys of at most 520 bytes and any witness `ws`: `verifyScript tap c [] (witnessBytes 0 (sha256 (fundingBytes pubkey1 pubkey2))) (ws ++ [fundingBytes pubkey1 pubkey2]) = true` iff the program is a true value, every witness element is at most 520 bytes, and `FundingSpend` holds for the context's flags and the signature mission's `legacyOracle` of its transaction on `ws.reverse`. With the `to_local`, HTLC and anchor missions this completes the script set of a Lightning channel's on-chain life: funding, commitment outputs, HTLCs, anchors.""", ms=None),
}
ORDER = ["BitcoinFunding.funding_witness", "BitcoinFunding.funding_spends_iff", "BitcoinFunding.parseScript_funding", "BitcoinFunding.funding_p2wsh_spend"]
