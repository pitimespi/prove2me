## The claim

A transaction's identifier is the hash of its serialization without witnesses, and that serialization still contains every `scriptSig`. Before SegWit, anyone could take a valid transaction, re-encode a signature inside a `scriptSig` (a different DER length byte, a negated S value, an extra push), and broadcast a transaction that was equally valid and had a different txid. Any protocol that referred to an unconfirmed transaction by its txid — a refund signed against a funding transaction, which is how payment channels start — could be broken this way. BIP141 fixed it by moving signatures into the witness, which the txid does not hash, and by requiring the `scriptSig` of a native witness spend to be empty.

This mission proves that the fix does what it claims, against the published `VerifyScript` and `CheckInputScripts`: for a transaction whose inputs spend native witness programs and whose scripts verify, the txid is a function of the sender's *intent* — version, prevouts, sequence numbers, outputs, lock time — and of nothing else.

## What is proved

- **`native_scriptSig_empty`** — under `CheckInputScripts` with `WITNESS`, every input spending a native witness program has an empty `scriptSig` (`SCRIPT_ERR_WITNESS_MALLEATED`, lifted from the VerifyScript mission's `native_witness_malleated`).
- **`txid_of_intent`** — for such a transaction, `txid tx = txid (ofIntent (intentOf tx))`: the identifier of the canonical transaction with empty `scriptSig`s and witnesses.
- **`txid_determined`** (goal) — two transactions with the same intent, both verifying against the same ledger, with native witness-program inputs, have the same txid.
- **`p2sh_wrapped_scriptSig`** — for a P2SH output spent with witness data, `VerifyScript` succeeds only if the `scriptSig` is exactly the single push of the witness program it evaluates to (`SCRIPT_ERR_WITNESS_MALLEATED_P2SH`); the `scriptSig` of a wrapped spend is determined by the redeem script.

## What this rests on

The serialization mission's `txid_strip` (the txid ignores witnesses), the VerifyScript mission's `native_witness_malleated`, and the block mission's `CheckInputScripts`. The statements are about the executable `VerifyScript`; no assumption about hash functions or signatures is needed, because the theorems say nothing about whether a valid spend exists, only that its identifier is fixed once it does. ([`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp), [`transaction.h`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/primitives/transaction.h), [BIP141](https://github.com/bitcoin/bips/blob/master/bip-0141.mediawiki))
