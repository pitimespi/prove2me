## The claim

The script mission's interpreter, reviewed twice and tested against Core's 994 vectors, is exact except at two documented limits: L1, the signature script code does not restart after an executed `OP_CODESEPARATOR` (a handful of historical transactions), and L10, `OP_CHECKMULTISIG` deletes only the checked signature from the script code instead of all of them (constructed test cases). Those nine vectors disagreed. This mission closes both limits with a second interpreter that tracks Core's `pbegincodehash` and performs Core's `FindAndDelete`s itself, and proves that the two interpreters agree wherever the limits do not bite, so that every published theorem about `verifyScript` carries over unchanged to the exact rule.

## What is proved

- **The script code** (`stepV2_codesep`, `stepV2_keeps`, `codesep_tracks`): after an executed `OP_CODESEPARATOR` at byte position $p$ the script code is the script from $p+1$; nothing else changes it.
- **The deletions** (`checksig_deletes_one`, `fadAll_base`, `fadAll_witness`, `multisigSigs_eq`, `multisig_deletes_all`): `OP_CHECKSIG` checks against the code with its own signature deleted; `OP_CHECKMULTISIG` against the code with all its signatures deleted, before any check, in `SigVersion::BASE` only.
- **Equivalence outside the limits** (`legacyOracle_eq`, `annotate_parse`, `annotate_suffix`, `annotate_op_suffix`, `stepV2_agree`, `eval_agree`, `evalBytes_agree`, `runOk_of_static`, `runOk_witness`, `evalOk_of_static`, `evalOk_witness`, `verify_agree`, the goal): under the side condition that no executed `OP_CODESEPARATOR` and no multisig self-signature push occurs (statically implied by the absence of the two opcodes; in witness v0 only the separator matters), `verifyScriptV2 = verifyScript`.

## Vectors

`verifyScriptV2` agrees with Core on all 793 script tests and all 201 transaction tests of the pinned revision; the nine cases that disagreed with the published interpreter (seven L1, two L10) now agree, and no previously agreeing case changed (`tests/CoreV2*.lean`, `REVIEW_V2.md`).

## What this rests on and what it does not say

The side condition for L10 is semantic (it depends on the signatures actually on the stack), so `EvalOk` is stated along the run, with static sufficient conditions. Policy flags (`CONST_SCRIPTCODE` and the rest) remain off as in the published model; the Taproot handler is unchanged. ([`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp))
