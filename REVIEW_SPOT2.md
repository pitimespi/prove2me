# Spot 2: `SignatureHash` (legacy and BIP143), `FindAndDelete`, `CheckECDSASignature` versus `BitcoinSig`

Core: [`interpreter.cpp:1610`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1610)
(`SignatureHash`), [`:1263`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1263)
(`CTransactionSignatureSerializer`), [`:239`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L239)
(`FindAndDelete`), [`:331`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L331)
(`EvalChecksigPreTapscript`), [`:1700`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1700)
(`CheckECDSASignature`), [`script.cpp:313`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L313)
(`GetScriptOp`). Lean: `Definitions/Def_BitcoinSig.lean` (`findAndDelete`, `serScriptCode`, `serSigTx`,
`sigHashLegacy`, `sigHashWitnessV0`, `checkECDSASignature`, `checkSigPreTapscript`). Read-back:
`missions/readbacks/sig/readback_Def_BitcoinSig.md`. Spot 3 (BIP143) is covered here as well, since
the two live in one function.

## Verdict

Agreement on every field, flag and quirk, confirmed by 24 independently computed vectors. One
remark (R1) about a case that cannot change a verdict. The two known limits L1 and L10 concern
*which* script code reaches these functions, not what they do with it.

## `CTransactionSignatureSerializer` (legacy) — `serSigTx`, `serSigInput`, `serSigOutput`

| Core | Lean | Agree |
|---|---|---|
| flags from `nHashType`: `fAnyoneCanPay = ht & 0x80`, `fHashSingle = (ht & 0x1f) == 3`, `fHashNone = (ht & 0x1f) == 2` | identical masks | yes |
| `version` as `uint32` | `ser32 tx.version` | yes |
| `nInputs = fAnyoneCanPay ? 1 : vin.size()`, CompactSize | identical | yes |
| `SerializeInput`: with `ANYONECANPAY` the one input is `nIn`; prevout; script code for `nIn` else empty `CScript` (one byte `00`); sequence `0` for other inputs under `SINGLE`/`NONE`, else the input's | identical, `serBytes []` for the empty script | yes |
| `nOutputs = NONE ? 0 : SINGLE ? nIn + 1 : vout.size()` | identical | yes |
| `SerializeOutput`: under `SINGLE`, outputs other than `nIn` are `CTxOut()` = value −1, empty script (`ffffffffffffffff 00`) | `serTxOut ⟨-1, []⟩`; `serInt64` encodes −1 as eight `ff` | yes |
| `nLockTime` as `uint32`, then `nHashType` as `int32` appended by `SignatureHash` | `ser32 nLockTime`, `ser32 hashType` (the type is one byte, so signed/unsigned does not matter) | yes |
| `HashWriter::GetHash` = SHA-256d | `hash256` | yes |

## `SerializeScriptCode` — `serScriptCode`

Core counts `OP_CODESEPARATOR` instructions with `GetOp`, writes `CompactSize(size − count)`, then
the script bytes with each `OP_CODESEPARATOR` *instruction* removed (bytes equal to `0xab` inside
push data are kept). Lean removes the `op OP_CODESEPARATOR` instructions and prefixes the length
of what remains. Identical whenever the script code parses to the end.

**R1 (remark).** When the script code ends in a truncated push, `GetOp` fails after advancing past
the opcode and size bytes; Core then writes only up to that point while its length prefix still
counts every byte, whereas Lean writes every remaining byte. This cannot change a `VerifyScript`
verdict: such a script code is the script being executed (or its tail after a code separator), and
`EvalScript` fails with `SCRIPT_ERR_BAD_OPCODE` when it reaches the truncated push, whatever the
signature check returned. It does mean `sigHashLegacy` is not byte-for-byte `SignatureHash` on
malformed script codes; no theorem depends on that case.

## `SignatureHash`, `SigVersion::BASE` — `sigHashLegacy`

| Core | Lean | Agree |
|---|---|---|
| `(ht & 0x1f) == SINGLE && nIn >= vout.size()` → `uint256::ONE` (the SIGHASH_SINGLE bug), checked *before* anything else and only outside `WITNESS_V0` | `if … then uint256One`; `uint256One = 01 00…00` in serialized order | yes |
| otherwise SHA-256d of serializer output ‖ `int32 ht` | identical | yes |
| `assert(nIn < vin.size())` | `getD` default input | unreachable (the interpreter only calls with a real input) |

## `SignatureHash`, `SigVersion::WITNESS_V0` (BIP143) — `sigHashWitnessV0`

| Core | Lean | Agree |
|---|---|---|
| `hashPrevouts` = SHA-256d of all prevouts unless `ANYONECANPAY`, else zero | identical | yes |
| `hashSequence` = SHA-256d of all sequences unless `ANYONECANPAY`, `SINGLE` or `NONE`, else zero | identical | yes |
| `hashOutputs` = SHA-256d of all outputs unless `SINGLE`/`NONE`; under `SINGLE` with `nIn < vout.size()` the SHA-256d of `vout[nIn]`; else zero | identical | yes |
| no `uint256::ONE` quirk | none | yes |
| fields: version, hashPrevouts, hashSequence, prevout, `scriptCode` with CompactSize prefix, `amount` as `int64`, sequence, hashOutputs, locktime, `int32 ht` | identical order and encodings (`serBytes`, `serInt64`) | yes |
| `GetPrevoutsSHA256` etc. are single SHA-256 then `SHA256Uint256` | `hash256` | yes |

## `FindAndDelete` — `findAndDelete`

| Core | Lean | Agree |
|---|---|---|
| empty pattern → nothing | `b.isEmpty → (script, 0)` | yes |
| at each instruction boundary, strip every consecutive occurrence of `b` by raw byte comparison, then advance one instruction with `GetOp` | `strip` then `getOp` | yes |
| a match inside push data is not a boundary and is kept | the same (`getOp` skips the whole push) | yes |
| `GetOp` failure ends the loop; the remainder from the last boundary is kept | `none → (acc ++ s, found)` | yes |
| the pattern is `CScript() << vchSig`, the canonical push; for an empty signature that is `OP_0` (`00`), so an empty signature deletes `OP_0` instructions from the script code | `pushBytes []` is `[0]`, same effect | yes |

## `EvalChecksigPreTapscript` and `CheckECDSASignature` — `checkSigPreTapscript`, `checkECDSASignature`

| Core | Lean | Agree |
|---|---|---|
| `FindAndDelete` of the signature push in `BASE` only (`CONST_SCRIPTCODE` is policy) | identical | yes (L10 for multisig) |
| `CheckSignatureEncoding`, `CheckPubKeyEncoding` → script error | `none` | yes (spot 5) |
| `NULLFAIL` | policy, off | yes |
| `CPubKey::IsValid`: size > 0 and the header-determined length (33 for `02`/`03`, 65 for `04`/`06`/`07`) | `pubkeyValid` | yes |
| empty signature → `false` (no script error) | `getLast? = none → false` | yes |
| hash type = last byte; signature without it | identical | yes |
| `WITNESS_V0 && amount < 0` → `HandleMissingData` | `false` | unreachable in block validation (the amount comes from the coin) |
| `VerifyECDSASignature` = `CPubKey::Verify` | `pubkeyVerify` | spot 4 |

## Vectors (`tests/SighashVectors.lean`, generator `tests/reference/sighash_reference.py`)

The Python reference implements the serializer from the Core source above, independently of the
Lean. A three-input, two-output transaction, a script code containing an `OP_CODESEPARATOR` and a
push, hash types `ALL`, `NONE`, `SINGLE` with and without `ANYONECANPAY`, inputs 0 and 2 (input 2
has no matching output): 24 hashes, all equal. Plus the `uint256::ONE` cases, five `FindAndDelete`
boundary cases, and the code-separator stripping of `serScriptCode`. Together with the earlier
BIP143 example from the BIP and the Python-signed spends in `tests/SigVectors.lean`, every branch of
the two serializers is exercised by at least one vector whose expected value was not produced by the
Lean.
