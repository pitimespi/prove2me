## The claim

A Lightning commitment transaction pays the local node's balance to a `to_local` output whose witness script (BOLT #3) reads

```
OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CHECKSEQUENCEVERIFY OP_DROP <local_delayedpubkey> OP_ENDIF OP_CHECKSIG
```

The channel's security rests on two claims about this script: the counterparty can spend it at any time with the revocation key, and the local node can spend it with its delayed key only after `to_self_delay` blocks, and nobody can spend it any other way. This mission proves both, and the "no other way", against the script interpreter as the script, signature and verification missions transcribed it from Bitcoin Core.

## What is proved

- **The interpreter run** (`eval_cons`, `csv_step`, `serialize_length`): the script on any stack `b :: tl` of admissible size fails unless `tl` is a single element, and otherwise leaves the result of the selected signature check; the `OP_CHECKSEQUENCEVERIFY` step passes exactly under `CsvPasses`.
- **The spending conditions** (`spends_iff`): for any stack whatsoever, the witness-v0 success condition (one element left, and true) holds iff the stack is `[b, sig]` and either `b` is true and `sig` verifies for the revocation key, or `b` is false, the sequence check passes, and `sig` verifies for the delayed key.
- **The output** (`parseScript_toLocal`, `p2wsh_spend`, the goal): the byte form of the script parses as intended, and `VerifyScript` accepts a witness for the pay-to-witness-script-hash output exactly when the witness is `[sig, b, script]` and the selected branch's conditions hold for the spending transaction's own signature checker and sequence check.
- **The delay** (`csv_concrete`, `checkSequence_iff`, `lightning_delay`): with the `CHECKSEQUENCEVERIFY` flag active, the sequence check is Core's `CheckSequence`, which for a 16-bit delay and a flag-free `nSequence` (as Lightning sets it) is exactly "version ≥ 2 and `nSequence` ≥ `to_self_delay`".

## What this rests on and what it does not say

The signature checks are the signature mission's `checkSigPreTapscript` with the witness-v0 sighash; nothing here says who holds the keys or how they are derived (BOLT #3's key derivation and the revocation secret are outside the script). The P2WSH program must be a true value, which `VerifyScript` requires of every witness program and which is a fact about one SHA-256 output the model cannot evaluate symbolically. `MINIMALIF` is policy, so under consensus any true selector opens the revocation branch; the relative lock time itself (whether the spending transaction may enter a block) is the block mission's BIP68 check, not the script's. ([BOLT #3](https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output), [`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp))
