# Differential testing against Bitcoin Core's test vectors

Scope: the Lean transcription of `VerifyScript` (`BitcoinTaproot.verifyScriptFull`, i.e.
`BitcoinVerify.verifyScript` with the Taproot branch), `BitcoinSer.readTx` and
`BitcoinBlockV2.checkTransaction`, run against Bitcoin Core's own vectors
`src/test/data/script_tests.json`, `tx_valid.json`, `tx_invalid.json` at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. Nothing under `Definitions/`, `Theorems/`, `Solutions/`
or the pre-existing tests was modified.

## Files

| File | Role |
|---|---|
| `tests/reference/core_script_tests.py` | parses `script_tests.json` (Core's `ParseScript` assembly, the harness transactions, the Taproot placeholders), applies the inclusion rule, emits `tests/CoreScriptTests1..5.lean` |
| `tests/reference/core_tx_tests.py` | parses `tx_valid.json` / `tx_invalid.json`, emits `tests/CoreTxTests.lean` |
| `tests/reference/core_tx_mismatches.py` | emits `tests/CoreTxMismatches.lean`, the root-cause diagnostics for the nine tx mismatches |
| `tests/reference/core_*_tests.index.json` | per-test metadata (id, flags, expected result, comment) in `#eval` order, for mapping output lines back to tests |
| `tests/CoreScriptTests1..5.lean`, `tests/CoreTxTests.lean`, `tests/CoreTxMismatches.lean` | one `#eval` per test printing `true` iff the Lean verdict equals Core's |

Run: `python3 -I tests/reference/core_script_tests.py <script_tests.json> tests 160`,
`python3 -I tests/reference/core_tx_tests.py <tx_valid.json> <tx_invalid.json> tests`, then
`lake env lean tests/<file>.lean` in a workspace where `Definitions` is built. Wall-clock per file
(Lean 4.33.1 interpreter): CoreScriptTests1–3 ≈ 2–3 s each, CoreScriptTests4 ≈ 9 s, CoreScriptTests5
≈ 27 s, CoreTxTests ≈ 49 s, CoreTxMismatches ≈ 12 s.

## Method

### script_tests.json

Each entry is `[[witness hex..., amount BTC]?, scriptSig, scriptPubKey, flags, expected_scripterror, comment]`.
The generator reproduces `src/test/script_tests.cpp`:

* **Assembly** (`ParseScript`, `core_read.cpp`): decimal numbers go through `CScript << int64_t`
  (`OP_0`, `OP_1NEGATE`, `OP_1..OP_16`, otherwise the minimal push of `CScriptNum::serialize`);
  `0x..` tokens are raw bytes inserted as-is (so `0x4c 0x01 0x07` is a literal `OP_PUSHDATA1`);
  `'...'` strings are pushed as data (minimal push opcode, `''` is `OP_0`); every other token is an
  opcode name with or without the `OP_` prefix, from the `GetOpName` table of `script/script.cpp`
  restricted as `ParseOpCode` does (`OP_RESERVED`, and `OP_NOP` … `OP_CHECKSIGADD`; the names
  `0`, `-1`, `1..16` are numbers).
* **Witness**: hex elements; the three Tapscript placeholders of the newest tests are reproduced:
  `#SCRIPT# <assembly>` is the parsed script pushed as a witness element, `#CONTROLBLOCK#` is the
  control block of a one-leaf Taproot tree over the preceding element with leaf version `0xc0` and
  internal key `XOnlyPubKey::NUMS_H` (`TaprootBuilder().Add(0, script, 0xc0).Finalize(NUMS_H)`), and
  `#TAPROOTOUTPUT#` in the scriptPubKey is the hex of the tweaked output key. The last array element
  is the amount in BTC (`AmountFromValue`, parsed as an exact decimal).
* **Transactions** (`BuildCreditingTransaction` / `BuildSpendingTransaction`): crediting tx = version 1,
  one input with null prevout (`0…0:0xffffffff`), scriptSig `OP_0 OP_0` (`CScript() << CScriptNum(0) << CScriptNum(0)`
  = `00 00`), nSequence `0xffffffff`, one output `(amount, scriptPubKey)`, locktime 0; spending tx =
  version 1, one input `(txid(credit), 0)` with the scriptSig and witness, nSequence `0xffffffff`, one
  output `(amount, empty)`, locktime 0. The crediting txid is computed in Python (SHA-256d of the
  witness-stripped serialization) and embedded; the many tests with real ECDSA signatures (P2PK, P2PKH,
  P2SH, P2WPKH, P2WSH, multisig) pass, which cross-checks the txid, the harness transactions and the
  Lean signature hashes at once.
* **Evaluation**: `verifyScriptFull [⟨amount, scriptPubKey⟩] ⟨flags, spendingTx, 0, amount⟩ scriptSig scriptPubKey witness == (expected == "OK")`,
  i.e. `VerifyScript(scriptSig, scriptPubKey, &witness, flags, TransactionSignatureChecker(spend, 0, amount))`
  compared on success/failure only. Core's `DoTest` additionally re-runs every test under random
  flag supersets/subsets; see the inclusion rule.

### tx_valid.json / tx_invalid.json

Each entry is `[[[prevout hash (display order), index, scriptPubKey assembly, amount?]…], tx hex, flags]`.
The generator reproduces `src/test/transaction_tests.cpp` / `CheckTxScripts`:

* prevout hashes are byte-reversed (`Txid::FromHex`), the index is cast to `uint32_t` (the `-1` of the
  coinbase-style entries becomes `0xffffffff`), the scriptPubKey goes through `ParseScript`, the amount
  is the integer satoshi value or `0` when absent (`map_prevout_values.count(...) ? ... : 0`);
* the transaction is deserialized with witness (`readTx true`; trailing bytes ignored, as
  `CTransaction(deserialize, TX_WITH_WITNESS, stream)` does), `checkTransaction` is run, then every
  input is verified with `verifyScriptFull spent ⟨flags, tx, i, amount_i⟩ scriptSig_i spk_i witness_i`;
* the Lean harness returns a four-valued verdict `R` (`badSer`, `badTx`, `scriptFail`, `ok`); a
  tx_valid entry expects `.ok`, a `BADTX` entry expects `.badTx` (Core's harness asserts that exactly
  the `BADTX` entries fail `CheckTransaction`; a deserialization failure would be a harness error, so
  `.badSer` is never expected), every other tx_invalid entry expects `.scriptFail`;
* **flags**: in tx_valid the listed flags are the *excluded* ones (Core verifies with
  `~verify_flags`), so the Lean flags are `consensus − excluded`; in tx_invalid they are the flags to
  use (`NONE` = no flags).

## Inclusion rule and counts

The Lean model implements only the consensus flags `P2SH, WITNESS, TAPROOT, DERSIG, CHECKLOCKTIMEVERIFY,
CHECKSEQUENCEVERIFY, NULLDUMMY`; every policy flag (`STRICTENC, LOW_S, SIGPUSHONLY, MINIMALDATA,
DISCOURAGE_UPGRADABLE_NOPS, CLEANSTACK, MINIMALIF, NULLFAIL, DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM,
WITNESS_PUBKEYTYPE, CONST_SCRIPTCODE, DISCOURAGE_*`) is always off.

Rule: a test is included iff **its flag set is a subset of the consensus flags, or its expected result
is OK**; expected-failure tests with a policy flag are skipped. Justification: every script-verification
flag only *adds* failure conditions (each flag is consulted only in `return set_error(...)` guards, and
`DISCOURAGE_*`/`CLEANSTACK`/`MINIMALIF`/`NULLFAIL`/… are pure rejections), so a script that succeeds
under a flag set also succeeds under any subset; Core's own harness asserts exactly this (`DoTest`
re-verifies every passing test under 16 random flag subsets, and `tx_valid` re-verifies with each flag
removed). Hence an OK test under `P2SH,STRICTENC` must be OK under `P2SH` alone, which is what the Lean
is asked. Conversely a failing test under `P2SH,STRICTENC` may fail only because of `STRICTENC`, so it
cannot be used (the subset of such tests whose failure is flag-independent would need per-test
analysis; they are skipped wholesale). The only non-monotone corner is the harness-level requirement
that `WITNESS` implies `P2SH` and `CLEANSTACK` implies both; no included flag set violates it.

| Vector file | entries | included | skipped | why skipped |
|---|---|---|---|---|
| script_tests.json | 1263 | **793** = 688 OK (165 with consensus-only flags, 523 with policy flags) + 105 expected failures with consensus-only flags | 470 | expected failure with a policy flag: `P2SH,STRICTENC` 308, `MINIMALDATA` 75, `P2SH,WITNESS,MINIMALIF` 32, `STRICTENC` 18, `P2SH,WITNESS,WITNESS_PUBKEYTYPE` 11, `P2SH,DISCOURAGE_UPGRADABLE_NOPS` 10, `CONST_SCRIPTCODE` 4, `DERSIG,NULLFAIL` 3, `SIGPUSHONLY` 2, `CLEANSTACK,P2SH` 2, `LOW_S` 1, `DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM,P2SH,WITNESS` 1, `CHECKLOCKTIMEVERIFY,MINIMALDATA` 1, `CHECKSEQUENCEVERIFY,MINIMALDATA` 1, `DERSIG,NULLFAIL,NULLDUMMY` 1 |
| tx_valid.json | 122 | **122** | 0 | (all expected OK; verified with `consensus − excluded`) |
| tx_invalid.json | 93 | **79** (9 `BADTX`, 70 script failures) | 14 | flags include a policy flag: `CONST_SCRIPTCODE` 11 (#181–#195, #199), `P2SH,CONST_SCRIPTCODE` 1 (#197), `P2SH,WITNESS,DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM` 2 (#131, #157) |

Of the 793 included script tests, 85 carry a witness (of 117), including all 7 Tapscript tests
(`#CONTROLBLOCK#`/`#TAPROOTOUTPUT#`) and the P2WPKH/P2WSH/P2SH-wrapped families; the 105 included
expected failures cover `SIG_DER` 28, `EVAL_FALSE` 26, `CLEANSTACK` 10 (witness scripts must leave one
element: consensus), `UNSATISFIED_LOCKTIME` 8, `INVALID_STACK_OPERATION` 6, `WITNESS_PROGRAM_MISMATCH` 4,
`STACK_SIZE` 3, `WITNESS_UNEXPECTED` 3, `WITNESS_MALLEATED` 3, `EQUALVERIFY` 2, `SIG_NULLDUMMY` 2,
`NEGATIVE_LOCKTIME` 2, `TAPSCRIPT_MINIMALIF` 2, `OP_COUNT` 1, `SIG_PUSHONLY` 1 (P2SH scriptSig push-only:
consensus), `WITNESS_PROGRAM_WRONG_LENGTH` 1, `WITNESS_PROGRAM_WITNESS_EMPTY` 1, `WITNESS_MALLEATED_P2SH` 1,
`TAPSCRIPT_EMPTY_PUBKEY` 1. The `MAX_SCRIPT_SIZE`, element-size, stack-size, op-count and
`MAX_PUBKEYS_PER_MULTISIG` tests that carry consensus-only flags are included and pass (the flag-bearing
ones, e.g. `SCRIPT_SIZE`/`PUSH_SIZE`/`PUBKEY_COUNT`/`SIG_COUNT` under `P2SH,STRICTENC`, are among the
skipped expected failures).

## Results

| Lean file | #eval | agree | disagree |
|---|---|---|---|
| CoreScriptTests1..5.lean | 793 | **793** | 0 |
| CoreTxTests.lean (tx_valid) | 122 | 114 | 8 |
| CoreTxTests.lean (tx_invalid) | 79 | 78 | 1 |
| **total** | **994** | **985** | **9** |

Every disagreement is in the two documented limits of the model; no genuine discrepancy was found.
`tests/CoreTxMismatches.lean` re-derives each of the nine from the C++ semantics by running
`BitcoinSig.checkECDSASignature` on the signature(s) involved against the scriptCode Core uses and
against the one the Lean uses; all 30 of its `#eval`s print the value their comment predicts.

### Mismatch table

Ids are `<file>#<index into the JSON array>`; the same id is in the `#eval` comment of
`tests/CoreTxTests.lean`. Lean flags are `consensus − excluded` (tx_valid) or as listed (tx_invalid).

| # | Test (id, Core comment) | Lean | Core | Root cause |
|---|---|---|---|---|
| 1 | `valid#79` — "Hashed data starts at the CODESEPARATOR"; scriptPubKey `<pk> CODESEPARATOR CHECKSIG` (excluded `CONST_SCRIPTCODE,LOW_S`) | `.scriptFail` | valid | **L1**. Core's `CHECKSIG` hashes `scriptCode = CScript(pbegincodehash, pend) = "ac"`; the Lean hashes the whole script with `OP_CODESEPARATOR` stripped (`21<pk> ac`). Diagnostic: the signature verifies with scriptCode `ac` (true) and not with `21<pk>abac` (false). |
| 2 | `valid#81` — "But only if execution has reached it"; `<pk> CHECKSIGVERIFY CODESEPARATOR <pk> CHECKSIGVERIFY CODESEPARATOR 1`, scriptSig `<sig1> <sig2>` | `.scriptFail` | valid | **L1**. The first `CHECKSIGVERIFY` (sig2) hashes the whole script in both (true in both, as the stripped whole script coincides); the second (sig1) hashes `21<pk> ad ab 51` in Core (true) but the whole script in the Lean (false). |
| 3 | `valid#85` — "As above, with the IF block executed"; `IF CODESEPARATOR ENDIF <pk> CHECKSIGVERIFY CODESEPARATOR 1`, scriptSig `<sig> 1` | `.scriptFail` | valid | **L1**. The `OP_1` makes the `IF` branch execute, so Core's scriptCode is `68 21<pk> ad ab 51` (signature true); the Lean uses the whole script (false). The sibling `valid#83` (unexecuted IF block) agrees, because there Core's scriptCode is the whole script too. |
| 4 | `valid#96` — "CHECKMULTISIG removes all signatures prior to hashing the script containing those signatures … including a signature of the digest 0x01 … and a normal SIGHASH_ALL signature" (mainnet P2SH 2-of-3; redeemScript `2 <sigA> <pk> <pk> 3 CHECKMULTISIG`, scriptSig `0 <sigA> <sigB> <redeem>`) | `.scriptFail` | valid | **L10**. Core deletes *every* signature (`sigA`, `sigB`) from the scriptCode before any check, so `sigB` (SIGHASH_ALL, checked first against key 3) is verified against `52 21<pk> 21<pk> 53 ae` (true). The Lean deletes only the signature being checked; `sigB` is not in the script, so `sigA` stays embedded and `sigB` fails (false), the loop then exhausts the keys. (`sigA`, SIGHASH_SINGLE with no matching output, hashes the constant `1` and is true under both.) Input 0 (P2PKH) alone passes. |
| 5 | `valid#222` — "BIP143 example: P2WSH with OP_CODESEPARATOR and out-of-range SIGHASH_SINGLE"; witnessScript `<pk1> CHECKSIGVERIFY CODESEPARATOR <pk2> CHECKSIG` (input 1) | `.scriptFail` | valid | **L1** (witness v0). `CHECKSIGVERIFY` hashes the whole witnessScript (true in both); `CHECKSIG` after the separator hashes `21<pk2> ac` in Core (true) and the whole script in the Lean (false). Input 0 (P2PK) alone passes. |
| 6 | `valid#224` — "BIP143 example: P2WSH with unexecuted OP_CODESEPARATOR and SINGLE\|ANYONECANPAY"; input 0 `0 IF CODESEPARATOR ENDIF <pk> CHECKSIG`, input 1 `1 IF CODESEPARATOR ENDIF <pk> CHECKSIG` | `.scriptFail` | valid | **L1**. Input 0 (unexecuted separator) passes in the Lean; input 1 executes the separator, Core's scriptCode is `68 21<pk> ac` (signature true), the Lean's is the whole script (false). |
| 7 | `valid#226` — "Same as the previous example with input-output pairs swapped" | `.scriptFail` | valid | **L1**, as #6 with the inputs swapped (input 1 passes, input 0 fails for the same reason). |
| 8 | `valid#244` — "multisig version of the FindAndDelete tests … Script is 2 CHECKMULTISIGVERIFY <sig1> <sig2> DROP" (P2SH; scriptSig `0 <sig1> <sig2> 2 <key1> <key2> <redeem>`) | `.scriptFail` | valid | **L10**. Core deletes both signatures, scriptCode `52 af 75`, and both signatures verify (true, true; the comment's "correct sighash (with FindAndDelete)"); the Lean checks `sig2` first with only `sig2` deleted, i.e. against `52 af 48<sig1> 75` (false). |
| 9 | `invalid#62` — "Inverted versions of tx_valid CODESEPARATOR IF block tests: CODESEPARATOR in an unexecuted IF block does not change what is hashed"; same script as `valid#85`, scriptSig `<sig'> 1` (flags NONE) | `.ok` | must fail | **L1**, in the other direction. Here the `IF` block *is* executed (`OP_1`), so Core hashes `68 21<pk> ad ab 51`, against which `sig'` is invalid (false, hence Core's expected failure); `sig'` was made over the whole script, which is exactly what the Lean hashes, so the Lean accepts it (true). |

Classification summary: L1 (legacy/witness-v0 `OP_CODESEPARATOR` does not restart the scriptCode) —
7 tests (`valid#79, #81, #85, #222, #224, #226`, `invalid#62`); L10 (`OP_CHECKMULTISIG` FindAndDelete
removes only the signature being checked, not all of them) — 2 tests (`valid#96, #244`);
harness/translation bugs on my side — 0 remaining (two were found and fixed while building the harness:
the prevout index `-1` must be cast to `uint32_t`, and negative literals in the `Prev` structure needed
an `Int` ascription); genuine discrepancies — **0**.

Note on L1's reach: the Lean's legacy scriptCode is the whole script with every `OP_CODESEPARATOR`
removed, which is exactly Core's `SerializeScriptCode` output *whenever no separator has executed
before the check*; the witness-v0 scriptCode is the whole witnessScript unstripped, again Core's choice
when none has executed. So the only inputs affected are those where a `CHECKSIG`/`CHECKMULTISIG`
follows an executed `OP_CODESEPARATOR`, which is what the seven tests exercise (and `valid#83`,
`valid#81`'s first check, and the unexecuted-branch inputs of `#224/#226` confirm the agreement in the
other case).

## What the agreement covers

The 985 agreeing cases exercise, with Core's own expectations: `CScriptNum` encoding and the
4-byte/5-byte limits, every stack/arithmetic/logic opcode, `OP_IF`/`OP_NOTIF`/`OP_ELSE`/`OP_ENDIF`
nesting and the unbalanced/`OP_VERIF` rules, disabled and reserved opcodes in executed and unexecuted
branches, push sizes (`OP_PUSHDATA1/2/4`, `MAX_SCRIPT_ELEMENT_SIZE`), `MAX_SCRIPT_SIZE`,
`MAX_OPS_PER_SCRIPT` (including the multisig key count), `MAX_STACK_SIZE`, `MAX_PUBKEYS_PER_MULTISIG`,
the hash opcodes, `OP_CHECKLOCKTIMEVERIFY`/`OP_CHECKSEQUENCEVERIFY` with and without their flags
(including BIP68 type/disable bits and `nSequence`/`nLockTime` edge cases from tx_valid/tx_invalid),
`NULLDUMMY`, `DERSIG` (strict DER acceptance/rejection incl. the lax-DER mainnet signatures of
tx_valid), ECDSA verification with all hash types, the SIGHASH_SINGLE bug, legacy `FindAndDelete` of the
checked signature (`valid#76, #83, #89, #91, #236, #253`, `invalid#11, #17, #167, #169, #176, #178` agree, including
the CVE-2024-38365 opcode-boundary case and the unexecuted-CODESEPARATOR cases), P2SH (push-only scriptSig, redeemScript
evaluation, `WITNESS_MALLEATED_P2SH`), witness v0 programs (P2WPKH, P2WSH, wrong lengths, mismatch,
empty witness, unexpected witness, stack-size/element-size limits, BIP143 hashes with all hash types
and amounts), unknown witness versions and P2A, Taproot key-path and the seven Tapscript tests
(`OP_SUCCESS` scan, `MINIMALIF`, empty pubkey, altstack), `CheckTransaction` (`BADTX`: empty
vin/vout, oversized, negative/overflowing values, duplicate inputs, coinbase script length,
null prevout), and the BIP144 transaction parser including the witness-flag and witness-stack cases of
tx_valid/tx_invalid.
