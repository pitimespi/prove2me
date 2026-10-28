# Spots 8 and 9: the Taproot branch, Tapscript, `SignatureHashSchnorr` and the tweak versus `BitcoinTaproot`

Core: [`interpreter.cpp:1927`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1927)
(`VerifyWitnessProgram`, version-1 branch), [`:1842`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1842)
(`ExecuteWitnessScript`), [`:417`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L417)
(`EvalScript`, the `TAPSCRIPT` cases), [`:357`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L357)
(`EvalChecksigTapscript`), [`:1745`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1745)
(`CheckSchnorrSignature`), [`:1493`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1493)
(`SignatureHashSchnorr`), [`:1882`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1882)
(`ComputeTapleafHash`, `ComputeTapbranchHash`, `ComputeTaprootMerkleRoot`, `VerifyTaprootCommitment`),
[`pubkey.cpp:236`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L236)
(`VerifySchnorr`, `ComputeTapTweakHash`, `CheckTapTweak`), [`script.cpp:365`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L365)
(`IsOpSuccess`), libsecp256k1 `secp256k1_xonly_pubkey_tweak_add_check`. Lean: `Definitions/Def_BitcoinTaproot.lean`.
Read-back: `missions/readbacks/taproot/readback_Def_BitcoinTaproot.md`.

## Verdict

Agreement throughout. Policy flags (`DISCOURAGE_OP_SUCCESS`, `DISCOURAGE_UPGRADABLE_TAPROOT_VERSION`,
`DISCOURAGE_UPGRADABLE_PUBKEYTYPE`) are off. Confirmed end to end by 65 vectors in which a Python
reference (BIP340 signing, the tweak, the BIP341 sighash, written from the BIPs) spends real P2TR
outputs through the Lean handler.

## The version-1 branch — `taprootHandler`

| Core | Lean | Agree |
|---|---|---|
| `TAPROOT` flag off → success (tested in `VerifyWitnessProgram`, spot 7) | `BitcoinVerify.verifyWitnessProgram` | yes |
| empty witness → fail | `witness.isEmpty → false` | yes |
| annex: `size ≥ 2 ∧ back non-empty ∧ back[0] = 0x50` → pop; `m_annex_hash = SHA256(CompactSize ‖ annex)` (single SHA-256 of the serialized vector) | `hasAnnex`, `sha256 (serBytes a)` | yes |
| one element left → `CheckSchnorrSignature(sig, program, TAPROOT, execdata)` | `checkSchnorrSignature … false ed0` (`ext_flag` 0, no leaf, code separator `0xFFFFFFFF` unused) | yes |
| else pop `control`, pop `script`; `33 ≤ size ≤ 33 + 32·128` and `(size − 33) % 32 = 0` | identical | yes |
| `tapleaf_hash = TapLeaf(control[0] & 0xfe ‖ CompactSize(script) ‖ script)` | `tapleafHash` | yes |
| `VerifyTaprootCommitment(control, program, tapleaf_hash)` fails → fail | identical | yes |
| leaf version `0xc0`: `m_validation_weight_left = GetSerializeSize(witness.stack) + 50` on the **original** witness (annex, script and control included); `ExecuteWitnessScript(…, TAPSCRIPT)` on the remaining elements | `witnessSerializedSize witness + 50` on the full witness; `executeTapscript … stack.reverse` | yes |
| other leaf versions → success | `true` | yes |

## The commitment — `verifyTaprootCommitment`, `checkTapTweak`, `xonlyTweakAddCheck`

`ComputeTapbranchHash` orders the children by `std::lexicographical_compare` (equal children in
either order give the same bytes); `ComputeTaprootMerkleRoot` folds from the leaf over the 32-byte
nodes after byte 33; `VerifyTaprootCommitment` takes the internal key from `control[1..33]`, the
parity from `control[0] & 1`, and calls `CheckTapTweak`: parse the internal key (`x < p`, liftable),
`tweak = TapTweak(internal ‖ root)`, then `secp256k1_xonly_pubkey_tweak_add_check`: tweak scalar
below `n`, `Q = P + t·G` not infinity, `x(Q)` equal to the 32 program bytes, parity of `y(Q)` equal
to the bit. The Lean's `lexLt`, `controlNodes`/`taprootMerkleRoot`, `tapTweakHash`, `checkTapTweak`
and `xonlyTweakAddCheck` are these, step for step; the program bytes are compared as bytes, never
parsed as a key, in both.

## `ExecuteWitnessScript`, `SigVersion::TAPSCRIPT` — `executeTapscript`

Scan with `GetOp`: parse failure → fail; an `OP_SUCCESSx` (`IsOpSuccess`: 80, 98, 126–129, 131–134,
137–138, 141–142, 149–153, 187–254) → success before any other test; then the initial stack at most
1000 elements; every element at most 520 bytes; `EvalScript`; exactly one element, true. Identical,
including that the scan precedes the size tests (a 600-byte element with `OP_SUCCESS80` succeeds).

## `EvalScript` under `TAPSCRIPT` — `tapStep`, `tapExecOp`, `evalChecksigTapscript`

| Core | Lean | Agree |
|---|---|---|
| no `MAX_SCRIPT_SIZE` test, no operation count | none | yes |
| push size, disabled-opcode test (every disabled opcode is an `OP_SUCCESSx`, so unreachable after the scan), execute-or-skip, stack size after every instruction, `opcode_pos` incremented per instruction | identical | yes |
| `OP_IF`/`OP_NOTIF` when executed: `MINIMALIF` is consensus: element longer than one byte, or one byte other than `0x01` → fail | identical | yes |
| `OP_CHECKSIG`/`VERIFY`: `EvalChecksigTapscript`: `success = sig non-empty`; if so `weight −= 50`, negative → fail; empty key → fail; 32-byte key: `success` and `CheckSchnorrSignature` fails → fail; other key sizes → `success` unchanged | identical | yes |
| `OP_CHECKSIGADD`: `sig = top(−3)`, `num = CScriptNum(top(−2))` (4 bytes, parsed before the check), `key = top(−1)`; push `num + success` | `pubkey :: numv :: sig :: rest`, `toNum false 4`, `serialize (num + …)` | yes |
| `OP_CHECKMULTISIG`/`VERIFY` → fail | `none` | yes |
| `OP_CODESEPARATOR`: `m_codeseparator_pos = opcode_pos` (0-based index of the instruction, pushes counted), only when executed | `codeseparatorPos := opcodePos` in `tapExecOp` | yes |
| every other opcode: the `BASE` behaviour (the Script mission's `execOp`), with `0xba` handled before it and `0xbb..0xfe` caught by the scan; `0xff` fails when executed | identical | yes |

## `CheckSchnorrSignature` — `checkSchnorrSignature`

64 or 65 bytes; 65 → the last byte is the hash type, which must not be `0`; `SignatureHashSchnorr`
returning false → fail; `VerifySchnorr` (spot 6). Identical.

## `SignatureHashSchnorr` — `sigHashSchnorr`

| Core | Lean | Agree |
|---|---|---|
| `ext_flag` 0 for `TAPROOT`, 1 for `TAPSCRIPT`; `key_version` 0 | `tapscript` flag | yes |
| hash type must be `≤ 3` or `0x81..0x83`, else false | first test | yes |
| `output_type = hash_type = 0 ? ALL : hash_type & 3`; `input_type = hash_type & 0x80` | identical | yes |
| `TapSighash` tagged hash of: epoch `0`, hash type, version, locktime; unless `ANYONECANPAY`: single SHA-256 of all prevouts, of all spent amounts (`int64`), of all spent scripts (with CompactSize), of all sequences; if `ALL`: single SHA-256 of all outputs; `spend_type = 2·ext_flag + annex`; if `ANYONECANPAY`: prevout, spent output, sequence, else `in_pos` as `uint32`; annex hash if present; if `SINGLE`: fail when `in_pos ≥ vout.size()`, else single SHA-256 of `vout[in_pos]`; if `TAPSCRIPT`: tapleaf hash, `0x00`, code-separator position as `uint32` | identical field by field; the precomputed "single hashes" are single SHA-256 (`m_*_single_hash`), and the Lean uses `sha256` | yes |

## Vectors (`tests/TapscriptVectors.lean`, generator `tests/reference/taproot_reference.py`)

28 sighash values for hash types `0,1,2,3,0x81,0x82,0x83` × key path/Tapscript × with/without annex,
plus the two undefined types; then, through `taprootHandler` on real tweaked outputs: key path with
`SIGHASH_DEFAULT`, `ALL`, `SINGLE|ANYONECANPAY`, with an annex committed and not committed, a
65-byte signature with hash type `0`, the internal key offered as the output key, the empty witness;
a single-leaf script path with the right and wrong key, an empty signature, the wrong parity bit, an
extra path node, a malformed control size; a two-leaf tree spent through each leaf and with the
wrong path; a five-leaf tree exercising `OP_CHECKSIGADD` 2-of-2 and 1-of-2 (empty signatures count
zero, a non-empty invalid one fails the script), `MINIMALIF` (`[01]` yes, `[02]` and `[01 00]` no,
`[]` takes `ELSE`), `OP_CODESEPARATOR` (a signature over position 0 verifies, one over
`0xFFFFFFFF` does not), `OP_SUCCESS80` with a 600-byte element, leaf version `0xc2` succeeding and
the same leaf under `0xc0` failing the commitment; and the validation-weight budget with one
signature duplicated by `OP_DUP`: ten checks (cost 500, budget 503) pass, eleven (cost 550, budget
538) fail. All 65 agree. Together with the BIP341 wallet test vectors in `tests/TaprootVectors.lean`
(script trees, control blocks, tweaks, key-path sighashes from the BIP), every branch above is
covered by at least one vector whose expected value was not produced by the Lean.
