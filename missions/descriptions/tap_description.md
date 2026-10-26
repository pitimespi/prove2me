## Why Taproot is consensus

Since block 709,632 (BIP341 activation, November 2021) every version-1 witness program with a 32-byte payload is a Taproot output. Spending it means either a key-path spend — one Schnorr signature by the output key — or a script-path spend that reveals a leaf script together with a control block proving that the leaf is committed to by the output key, and then runs the leaf under the Tapscript rules of BIP342. Both paths are evaluated by the version-1 branch of `VerifyWitnessProgram`, which the published VerifyScript mission left as a parameter (`TaprootHandler`). This mission supplies that parameter from the source and closes the script-validation layer. ([`VerifyWitnessProgram`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp), [BIP341](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0341.mediawiki), [BIP342](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0342.mediawiki))

The transcription covers the tagged hashes (`TapLeaf`, `TapBranch`, `TapTweak`, `TapSighash`), the merkle path of a control block, the key tweak check through the x-only tweak-add of libsecp256k1, the BIP341 signature hash with all its hash types and the annex, `CheckSchnorrSignature`, and the Tapscript interpreter rules: the `OP_SUCCESSx` scan, `MINIMALIF` as consensus, `OP_CHECKSIGADD`, the ban on `OP_CHECKMULTISIG`, the validation-weight budget, `OP_CODESEPARATOR` positions, and the absence of an operation count.

## The two spending paths

**Key path.** The witness, after removing an annex (a final element starting with `0x50` when at least two elements are present), is a single element: a 64-byte BIP340 signature under `SIGHASH_DEFAULT`, or 65 bytes whose last byte is a non-zero hash type. The message is the BIP341 signature hash computed from the transaction, the spent outputs, the input index, the hash type and the annex; the key is the 32-byte program itself.

**Script path.** The last element is the control block (33 + 32k bytes, k ≤ 128); the one before it is the leaf script; the control byte's low bit is the parity of the output key and its other bits the leaf version. `VerifyTaprootCommitment` recomputes the merkle root from the leaf hash and the path nodes, hashes it with the internal key into the tweak, and checks that the internal key plus tweak·G has the output key's x-coordinate and the stated parity. Leaf version `0xc0` runs the script under Tapscript with the weight budget |serialized witness| + 50; other leaf versions succeed (upgrade hook).

**Tapscript.** Builds on the published Script mission's interpreter: each non-signature opcode is the same `execOp`; `OP_CHECKSIG`, `OP_CHECKSIGVERIFY` and `OP_CHECKSIGADD` go through `EvalChecksigTapscript` (an empty signature is a clean false, 32-byte keys are checked with BIP340, other key lengths are upgradable and succeed, each passed signature costs 50 weight); `OP_IF`/`OP_NOTIF` require `[]` or `[1]`; `OP_CHECKMULTISIG(VERIFY)` fail; `OP_SUCCESSx` anywhere in the script makes it succeed before execution.

## Formalization targets

1. **Branch hash symmetry** (`tapbranch_comm`) and **merkle paths** (`merkleRoot_base`, `merkleRoot_snoc`): the merkle root is a left fold of the symmetric branch hash along the control block's nodes.
2. **Tapscript rules** (`opsuccess_accepts`, `checkmultisig_rejected`, `minimalif_rejects`, `sigops_budget`, `checksig_empty`): the five BIP342 rules that differ from legacy script, as universal statements about the transcription.
3. **BIP341 sighash guards** (`sighash_type_invalid`, `sighash_single_missing`).
4. **Key path** (`keypath_handler`, `keypath_annex`, `checkSchnorr_iff`) culminating in the goal, **`keypath_correct`**: a key-path spend verifies iff the witness is a BIP340 signature by the output key of the BIP341 hash under the encoded hash type.
5. **Script path** (`scriptpath_commitment`): a verifying script-path spend carries a valid commitment of the revealed leaf to the output key.

## What the result establishes

With the Script, Signature and VerifyScript missions, the goal theorem reduces the acceptance of a Taproot key-path spend to one BIP340 verification of one BIP341 hash, for every flag set, transaction and amount. `verifyScriptFull` is the complete `VerifyScript` of the source, with no parameter left: every output type that has ever been spendable on mainnet now has its validation rule transcribed in Lean. The script-path theorem fixes the commitment structure that the Tapscript execution sits behind; the Tapscript rule theorems make the BIP342 differences from legacy script facts about the definitions.

Policy flags (`DISCOURAGE_*`) are off, as in block validation. The definitions were checked by evaluation against the full BIP341 wallet test vectors (script trees, tweaks, control blocks, key-path signature hashes and signatures) and the BIP340 vectors.

## Where the obvious argument fails

`CheckSchnorrSignature` distinguishes three signature lengths and reads the hash type from the last byte: the characterization needs the 65-byte case decomposed as body ++ [b] with `dropLast`/`getLast?` reasoning, and the converse direction must rule out a 64-byte body being presented as a 65-byte signature. The merkle step theorem requires the chunking of a control block to commute with appending a node, an induction over the node count with the natural-number division (length − 33)/32. The annex is detected by `getLast?` on the raw witness but popped by `dropLast`; the script-path theorem threads the witness through two pops in `CScriptWitness` order (last element on top) before reaching the commitment check.

## Formalization scope

The handler is instantiated for the spent outputs of the transaction (needed by the BIP341 hash); the context is the VerifyScript mission's `Ctx`. Tapscript opcode positions and `OP_CODESEPARATOR` are tracked here (the Tapscript sighash commits to the position). No Mathlib is required; the development imports only `Std`.

A trivializing formalization would define the key path as "a Schnorr signature verifies"; here `taprootHandler` is the source's control flow, and the key-path statement is a theorem about it.

## Selected references

- Bitcoin Core contributors. *`VerifyWitnessProgram`, `ExecuteWitnessScript`, `EvalScript`, `EvalChecksigTapscript`, `SignatureHashSchnorr`, `VerifyTaprootCommitment`*, `src/script/interpreter.cpp`; *`XOnlyPubKey::CheckTapTweak`*, `src/pubkey.cpp`; *`secp256k1_xonly_pubkey_tweak_add_check`*, `src/secp256k1`, at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp)
- Pieter Wuille, Jonas Nick, Tim Ruffing. *BIP340: Schnorr Signatures for secp256k1*, 2020. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0340.mediawiki)
- Pieter Wuille, Jonas Nick, Anthony Towns. *BIP341: Taproot: SegWit version 1 spending rules*, 2020. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0341.mediawiki)
- Pieter Wuille, Jonas Nick, Anthony Towns. *BIP342: Validation of Taproot Scripts*, 2020. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0342.mediawiki)
