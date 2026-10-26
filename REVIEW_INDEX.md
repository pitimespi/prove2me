# Correspondence index: Lean definitions and the Core functions they transcribe

Generated from the docstrings of `Definitions/Def_*.lean`. Each row names a Lean declaration and the first line of its docstring, which cites the Bitcoin Core symbol at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. Undocumented helpers (constants, structure fields, recursion helpers) are listed without a citation. Use this as the master list for ticking off the review in `REVIEW.md`.


## `Def_BitcoinSer.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `Byte` |  |
| `Bytes` |  |
| `MAX_SIZE` | `serialize.h`: `MAX_SIZE = 0x02000000`, the bound `ReadCompactSize` enforces by default. |
| `leBytes` | `k` little-endian bytes of `n` (truncated modulo `2^(8k)`). |
| `leVal` | The little-endian value of a byte list. |
| `readLE` | Read `k` bytes as a little-endian number. |
| `beBytes` | `k` big-endian bytes of `n`. |
| `ser8` | `ser_writedata8/16/32/64`. |
| `ser16` |  |
| `ser32` |  |
| `ser64` |  |
| `serInt64` | Signed 64-bit (`CAmount`) as two's complement little-endian. |
| `serInt32` | Signed 32-bit (`int32_t nVersion`). |
| `readInt64` |  |
| `readInt32` |  |
| `writeCompactSize` | `WriteCompactSize`. |
| `readCompactSize` | `ReadCompactSize(is, range_check)`: `none` on a short read, a non-canonical encoding, or (with `rangeCheck`) a value above `MAX_SIZE`. |
| `serList` | `Serialize(vector<T>)`: `WriteCompactSize(size)` then the elements. |
| `readN` | Read exactly `n` elements with `f`. |
| `readList` | `Unserialize(vector<T>)`: a range-checked `ReadCompactSize`, then that many elements. |
| `serBytes` | A byte vector (`CScript`, a witness stack element, `prevector`): length then raw bytes. |
| `readBytes` |  |
| `readHash` | `uint256`: 32 raw bytes. |
| `OutPoint` | `COutPoint { uint256 hash; uint32_t n; }`. |
| `TxIn` | `CTxIn`; `witness` is `scriptWitness.stack`, serialized only through the transaction. |
| `TxOut` | `CTxOut { CAmount nValue; CScript scriptPubKey; }`. |
| `Tx` | `CTransaction` data: `uint32_t version`, `vin`, `vout`, `uint32_t nLockTime`. |
| `Tx.hasWitness` | `CTransaction::HasWitness`: some input has a non-empty witness stack. |
| `Tx.stripWitness` | The transaction with every witness stack cleared (what `TX_NO_WITNESS` reading yields). |
| `serOutPoint` |  |
| `serTxIn` |  |
| `serTxOut` |  |
| `serTx` | `SerializeTransaction(tx, s, params)` with `params.allow_witness = allowWitness`. |
| `readOutPoint` |  |
| `readTxIn` |  |
| `readTxOut` |  |
| `attachWitness` | Attach witness stacks to inputs, in order. |
| `readWitnesses` | Read one witness stack per input. |
| `readTx` | `UnserializeTransaction(tx, s, params)` with `params.allow_witness = allowWitness`. |
| `Header` | `CBlockHeader`: `int32_t nVersion`, `uint256 hashPrevBlock`, `uint256 hashMerkleRoot`, `uint32_t nTime`, `uint32_t nBits`, `uint32_t nNonce`. |
| `serHeader` |  |
| `readHeader` |  |
| `Block` | `CBlock`: the header followed by `vtx`. |
| `serBlock` |  |
| `readBlock` |  |
| `OutPoint.wf` |  |
| `TxIn.wf` |  |
| `TxOut.wf` |  |
| `Tx.wf` |  |
| `Header.wf` |  |
| `Block.wf` |  |
| `rotr` |  |
| `Ch` |  |
| `Maj` |  |
| `Sigma0` |  |
| `Sigma1` |  |
| `sigma0` |  |
| `sigma1` |  |
| `sha256K` |  |
| `Sha256State` |  |
| `sha256Init` |  |
| `sha256Round` | One round: `t1 = h + Σ1(e) + Ch(e,f,g) + k + w`, `t2 = Σ0(a) + Maj(a,b,c)`. |
| `be32Words` | Big-endian 32-bit words of a byte list (4 bytes each). |
| `sha256Schedule` | Message schedule: `w[t] = σ1(w[t-2]) + w[t-7] + σ0(w[t-15]) + w[t-16]` for `16 ≤ t < 64`. |
| `sha256Compress` |  |
| `chunks64Aux` | Split into 64-byte chunks (the input length is a multiple of 64); `fuel` bounds the recursion. |
| `chunks64` |  |
| `mdPad` | MD padding: `0x80`, zeros to 56 mod 64, then the bit length as 8 bytes (big-endian for SHA-256/SHA-1, little-endian for RIPEMD-160). |
| `be32Bytes` |  |
| `le32Bytes` |  |
| `sha256` | `CSHA256().Write(msg).Finalize()`. |
| `rol` |  |
| `rf1` |  |
| `rf2` |  |
| `rf3` |  |
| `rf4` |  |
| `rf5` |  |
| `le32Words` | Little-endian 32-bit words of a byte list. |
| `ripemdRL` | Message-word selection and rotation amounts of the left and right lines. |
| `ripemdRR` |  |
| `ripemdSL` |  |
| `ripemdSR` |  |
| `R5` |  |
| `ripemdInit` |  |
| `ripemdFL` | Left line: `f1..f5` with constants `0, 5A827999, 6ED9EBA1, 8F1BBCDC, A953FD4E`. |
| `ripemdKL` |  |
| `ripemdFR` | Right line: `f5..f1` with constants `50A28BE6, 5C4DD124, 6D703EF3, 7A6D76E9, 0`. |
| `ripemdKR` |  |
| `ripemdStep` | `Round`: `a = rol(a + f + x + k, r) + e; c = rol(c, 10)`, then the register rotation. |
| `ripemdLine` |  |
| `ripemdCompress` |  |
| `ripemd160` | `CRIPEMD160().Write(msg).Finalize()`. |
| `sha1F` |  |
| `sha1K` |  |
| `sha1Schedule` |  |
| `sha1Compress` |  |
| `sha1` |  |
| `hash256` | `Hash(x)` = SHA-256d. |
| `hash160` | `Hash160(x)` = RIPEMD-160 ∘ SHA-256. |
| `txid` | `CTransaction::ComputeHash`: SHA-256d of the witness-stripped serialization. |
| `wtxid` | `CTransaction::ComputeWitnessHash`: equals `txid` when there is no witness. |
| `headerHash` | `CBlockHeader::GetHash`. |
| `WITNESS_SCALE_FACTOR` |  |
| `MAX_BLOCK_WEIGHT` |  |
| `MAX_BLOCK_SERIALIZED_SIZE` |  |
| `txWeight` | `GetTransactionWeight`: `\|TX_NO_WITNESS\| * 3 + \|TX_WITH_WITNESS\|`. |
| `blockWeight` | `GetBlockWeight`. |
| `genesisScriptSig` | `CScript() << 486604799 << CScriptNum(4) << "The Times 03/Jan/2009 Chancellor on brink of second bailout for banks"`. |
| `genesisOutputScript` | `CScript() << 04678afd…11d5f << OP_CHECKSIG`. |
| `genesisCoinbase` |  |
| `genesisHeader` | `CreateGenesisBlock(1231006505, 2083236893, 0x1d00ffff, 1, 50 * COIN)`; the merkle root of a single-transaction block is that transaction's txid. |
| `genesisBlock` |  |
| `genesisHash` | `consensus.hashGenesisBlock = 000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f` (byte order as serialized, i.e. reversed display order). |
| `genesisMerkleRoot` | `genesis.hashMerkleRoot == 4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b`. |

## `Def_BitcoinScript.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `Byte` |  |
| `Bytes` |  |
| `MAX_SCRIPT_ELEMENT_SIZE` | `script/script.h`: `MAX_SCRIPT_ELEMENT_SIZE = 520`. |
| `MAX_OPS_PER_SCRIPT` | `script/script.h`: `MAX_OPS_PER_SCRIPT = 201`. |
| `MAX_PUBKEYS_PER_MULTISIG` | `script/script.h`: `MAX_PUBKEYS_PER_MULTISIG = 20`. |
| `MAX_STACK_SIZE` | `script/script.h`: `MAX_STACK_SIZE = 1000`. |
| `nDefaultMaxNumSize` | `CScriptNum::nDefaultMaxNumSize = 4`. |
| `leNat` | Little-endian value of a byte list. |
| `topBit` | The sign bit `0x80` of the last byte, if any. |
| `clearTop` | Clear the sign bit of the last byte: `result & ~(0x80ULL << (8 * (vch.size() - 1)))`. |
| `setVch` | `CScriptNum::set_vch`: little-endian magnitude with the top bit as the sign; `0` for empty. |
| `natBytes` | Little-endian bytes of a natural number, no trailing zero bytes: the `while (absvalue)` loop. |
| `setTop` | Set the sign bit of the last byte: `result.back() \|= 0x80`. |
| `serialize` | `CScriptNum::serialize`. |
| `nonMinimal` | The minimal-encoding test of the `CScriptNum(vch, fRequireMinimal)` constructor: the last byte has no value bits, and the previous byte does not need the sig… |
| `toNum` | `CScriptNum(vch, fRequireMinimal, nMaxNumSize)`: `none` where the constructor throws. |
| `castToBool` | `CastToBool`: some byte is nonzero, except that a negative zero (`0x80` as the last byte after zero bytes) is false. |
| `vchTrue` | `vchTrue` and `vchFalse`. |
| `vchFalse` |  |
| `boolBytes` |  |
| `Instr` | One parsed instruction: a data push (any of `OP_0`, direct pushes, `OP_PUSHDATAn`), or a non-push opcode given by its byte. `GetOp` only ever yields `op c` w… |
| `Script` |  |
| `OP_1NEGATE` | Opcode bytes used below (`script/script.h`). |
| `OP_RESERVED` |  |
| `OP_1` |  |
| `OP_16` |  |
| `OP_NOP` |  |
| `OP_IF` |  |
| `OP_NOTIF` |  |
| `OP_ELSE` |  |
| `OP_ENDIF` |  |
| `OP_VERIFY` |  |
| `OP_RETURN` |  |
| `OP_TOALTSTACK` |  |
| `OP_FROMALTSTACK` |  |
| `OP_2DROP` |  |
| `OP_2DUP` |  |
| `OP_3DUP` |  |
| `OP_2OVER` |  |
| `OP_2ROT` |  |
| `OP_2SWAP` |  |
| `OP_IFDUP` |  |
| `OP_DEPTH` |  |
| `OP_DROP` |  |
| `OP_DUP` |  |
| `OP_NIP` |  |
| `OP_OVER` |  |
| `OP_PICK` |  |
| `OP_ROLL` |  |
| `OP_ROT` |  |
| `OP_SWAP` |  |
| `OP_TUCK` |  |
| `OP_CAT` |  |
| `OP_SUBSTR` |  |
| `OP_LEFT` |  |
| `OP_RIGHT` |  |
| `OP_SIZE` |  |
| `OP_INVERT` |  |
| `OP_AND` |  |
| `OP_OR` |  |
| `OP_XOR` |  |
| `OP_EQUAL` |  |
| `OP_EQUALVERIFY` |  |
| `OP_1ADD` |  |
| `OP_1SUB` |  |
| `OP_2MUL` |  |
| `OP_2DIV` |  |
| `OP_NEGATE` |  |
| `OP_ABS` |  |
| `OP_NOT` |  |
| `OP_0NOTEQUAL` |  |
| `OP_ADD` |  |
| `OP_SUB` |  |
| `OP_MUL` |  |
| `OP_DIV` |  |
| `OP_MOD` |  |
| `OP_LSHIFT` |  |
| `OP_RSHIFT` |  |
| `OP_BOOLAND` |  |
| `OP_BOOLOR` |  |
| `OP_NUMEQUAL` |  |
| `OP_NUMEQUALVERIFY` |  |
| `OP_NUMNOTEQUAL` |  |
| `OP_LESSTHAN` |  |
| `OP_GREATERTHAN` |  |
| `OP_LESSTHANOREQUAL` |  |
| `OP_GREATERTHANOREQUAL` |  |
| `OP_MIN` |  |
| `OP_MAX` |  |
| `OP_WITHIN` |  |
| `OP_RIPEMD160` |  |
| `OP_SHA1` |  |
| `OP_SHA256` |  |
| `OP_HASH160` |  |
| `OP_HASH256` |  |
| `OP_CODESEPARATOR` |  |
| `OP_CHECKSIG` |  |
| `OP_CHECKSIGVERIFY` |  |
| `OP_CHECKMULTISIG` |  |
| `OP_CHECKMULTISIGVERIFY` |  |
| `OP_NOP1` |  |
| `OP_CHECKLOCKTIMEVERIFY` |  |
| `OP_CHECKSEQUENCEVERIFY` |  |
| `OP_NOP4` |  |
| `OP_NOP10` |  |
| `isDisabled` | The fifteen opcodes disabled since CVE-2010-5137; rejected even in an unexecuted branch. |
| `Flags` | The consensus script-verification flags that affect legacy execution. `MINIMALDATA`, `NULLFAIL`, `CONST_SCRIPTCODE`, `DISCOURAGE_UPGRADABLE_NOPS` and `MINIMA… |
| `Oracle` | The primitives the interpreter calls out to. `checkSig sig pubkey` is `EvalChecksig` for `SigVersion::BASE`: `none` when a signature or public-key encoding c… |
| `SEQUENCE_LOCKTIME_DISABLE_FLAG` | `CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG = (1U << 31)`. |
| `State` | The interpreter's mutable state: main stack, alt stack, the condition stack `vfExec`, and `nOpCount`. Stacks hold the top element first. |
| `State.initial` |  |
| `allTrue` | `vfExec.all_true()`. |
| `pushNum` | The numeric result of an opcode, pushed as `bn.getvch()`. |
| `eraseAt` | Remove the element at index `i` (0 = top). |
| `multisigLoop` | The `CHECKMULTISIG` matching loop: signatures and keys top-first, the keys consumed in order, each signature matched against successive keys; fails when more… |
| `execOp` | Execute one non-push opcode that is being executed (or is a conditional), as the `switch` of `EvalScript`. `none` is script failure. |
| `step` | One iteration of the `for (; pc < pend; …)` loop of `EvalScript`. |
| `run` | The loop over the instructions, followed by the unbalanced-conditional check. |
| `evalScript` | `EvalScript(stack, script, flags, checker, SigVersion::BASE)`: the resulting main stack. |
| `verifyScriptPlain` | `VerifyScript` for a `scriptPubKey` that is neither pay-to-script-hash nor a witness program: evaluate `scriptSig`, then `scriptPubKey` on the same stack, an… |
| `p2pkhScript` | The pay-to-public-key-hash output script `DUP HASH160 <h> EQUALVERIFY CHECKSIG`. |
| `p2pkScript` | The pay-to-public-key output script `<pubkey> CHECKSIG`. |
| `opsIn` | Number of instructions `nOpCount` counts: non-push opcodes above `OP_16`. |

## `Def_BitcoinSig.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `p` | The field prime `p = 2^256 - 2^32 - 977`. |
| `n` | The group order `n`. |
| `Gx` |  |
| `Gy` |  |
| `powModAux` | Square-and-multiply modular exponentiation with explicit fuel. |
| `powMod` |  |
| `finv` | Field inverse by Fermat (`0` maps to `0`). |
| `ninv` | Scalar inverse modulo the group order. |
| `Point` | An affine point, or the point at infinity. |
| `onCurve` |  |
| `padd` | Affine addition on secp256k1 (`y^2 = x^3 + 7`). |
| `pmulAux` | Double-and-add scalar multiplication with explicit fuel. |
| `pmul` |  |
| `G` |  |
| `beVal` |  |
| `liftXParity` | `secp256k1_ge_set_xo_var`: the point with abscissa `x` and the given parity of `y`, if any. |
| `parsePubkey` | `secp256k1_eckey_pubkey_parse`: compressed (`02`/`03`, 33 bytes), uncompressed (`04`) and hybrid (`06`/`07`, 65 bytes, parity of `y` must match). Coordinates… |
| `pubkeyLen` | `CPubKey::GetLen` and `CPubKey::IsValid`: the header byte announces the length. |
| `pubkeyValid` |  |
| `isHighS` | `secp256k1_scalar_is_high`: `s > n/2`. |
| `normalizeS` | `secp256k1_ecdsa_signature_normalize`: replace a high `s` by `n - s`. |
| `scalarOf` | The scalar read of a big-endian value (`secp256k1_scalar_set_b32`, overflow flagged). |
| `parseDerLax` | `ecdsa_signature_parse_der_lax`: `none` where the parser returns `0`; `some (0, 0)` where an integer overflows (the "correctly-parsed but invalid" signature)… |
| `ecdsaVerifyRaw` | `secp256k1_ecdsa_sig_verify` on a parsed key, a message scalar and a (normalized) signature. |
| `pubkeyVerify` | `CPubKey::Verify(hash, vchSig)`: key validity and parsing, lax DER parsing, S normalization, then `secp256k1_ecdsa_verify` with the message reduced modulo `n`. |
| `checkLowS` | `CPubKey::CheckLowS`. |
| `taggedHash` | `tagged_hash(tag, m) = SHA256(SHA256(tag) \|\| SHA256(tag) \|\| m)`. |
| `ascii` |  |
| `liftX` | `lift_x` of BIP340: the point with abscissa `x` and even `y`. |
| `schnorrVerify` | `secp256k1_schnorrsig_verify(sig64, msg, pk32)`. |
| `OP_PUSHDATA1` |  |
| `OP_PUSHDATA2` |  |
| `OP_PUSHDATA4` |  |
| `getOp` | `GetScriptOp`: one instruction and the remaining bytes, `none` where it returns `false`. |
| `parseScriptAux` | Parse a whole script; `none` on a malformed push (`SCRIPT_ERR_BAD_OPCODE`). |
| `parseScript` |  |
| `pushBytes` | `CScript() << vch`: the canonical push of a byte string. |
| `findAndDeleteAux` | `FindAndDelete(script, b)`: at every instruction boundary remove every occurrence of `b`; returns the result and the number found. |
| `findAndDelete` |  |
| `scriptCodeBytesAux` | `SerializeScriptCode`: the script code with every `OP_CODESEPARATOR` instruction removed, written as a byte string. |
| `serScriptCode` |  |
| `SIGHASH_ALL` |  |
| `SIGHASH_NONE` |  |
| `SIGHASH_SINGLE` |  |
| `SIGHASH_ANYONECANPAY` |  |
| `uint256One` | `uint256::ONE` in serialized byte order. |
| `serSigInput` | `CTransactionSignatureSerializer::SerializeInput`. |
| `serSigOutput` | `CTransactionSignatureSerializer::SerializeOutput`. |
| `serSigTx` | `CTransactionSignatureSerializer::Serialize`. |
| `sigHashLegacy` | `SignatureHash(scriptCode, tx, nIn, nHashType, amount, SigVersion::BASE)`: the SIGHASH_SINGLE bug returns `uint256::ONE`; otherwise SHA-256d of the serialize… |
| `sigHashWitnessV0` | `SignatureHash(..., SigVersion::WITNESS_V0)` (BIP143). |
| `isValidSignatureEncoding` | `IsValidSignatureEncoding` (strict DER with a trailing hash-type byte). |
| `isLowDERSignature` | `IsLowDERSignature`: strict DER and low S (of the signature without the hash-type byte). |
| `isCompressedOrUncompressedPubKey` |  |
| `isCompressedPubKey` |  |
| `isDefinedHashtypeSignature` |  |
| `SigFlags` | The `script_verify_flags` consulted by the signature layer. Only `dersig` is a consensus flag on mainnet; the others are relay policy and are carried for fid… |
| `checkSignatureEncoding` | `CheckSignatureEncoding`: `true` where the source returns `true`, `false` where it sets an error. |
| `SigVersion` |  |
| `checkPubKeyEncoding` | `CheckPubKeyEncoding`. |
| `checkECDSASignature` | `GenericTransactionSignatureChecker::CheckECDSASignature`. |
| `checkSigPreTapscript` | `EvalChecksigPreTapscript`: `FindAndDelete` of the signature push (legacy only), the two encoding checks (`none` = script error), then the checker's verdict. |
| `LOCKTIME_THRESHOLD` |  |
| `SEQUENCE_FINAL` |  |
| `SEQUENCE_LOCKTIME_DISABLE_FLAG` |  |
| `SEQUENCE_LOCKTIME_TYPE_FLAG` |  |
| `SEQUENCE_LOCKTIME_MASK` |  |
| `checkLockTime` | `GenericTransactionSignatureChecker::CheckLockTime(nLockTime)`. |
| `checkSequence` | `GenericTransactionSignatureChecker::CheckSequence(nSequence)`. |
| `legacyOracle` | The concrete oracle for the legacy interpreter: Core's hashes, the pre-tapscript signature check on `scriptCode` (the script being executed, for scripts with… |
| `p2pkhBytes` | The P2PKH output script as bytes: `OP_DUP OP_HASH160 <h> OP_EQUALVERIFY OP_CHECKSIG`. |
| `sameSkeleton` | Two transactions with the same version, outputs, lock time, and the same prevouts and sequence numbers in order (scriptSigs and witnesses may differ): what t… |
| `minimalInt` | The minimal big-endian positive integer encoding DER requires. |
| `derEncode` | The DER layout `30 len 02 \|r\| r 02 \|s\| s ht`. |

## `Def_BitcoinVerify.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `MAX_SCRIPT_SIZE` | `MAX_SCRIPT_SIZE = 10000`. |
| `WITNESS_V0_SCRIPTHASH_SIZE` |  |
| `WITNESS_V0_KEYHASH_SIZE` |  |
| `WITNESS_V1_TAPROOT_SIZE` |  |
| `scriptFlagsOf` | The interpreter flags carried by the consensus flag set. |
| `sigFlagsOf` | The signature-layer flags: `DERSIG` is the only consensus one; the policy flags are off. |
| `Ctx` | The context of one script verification: the spending transaction, the input index and the amount spent (`-1` where unknown, as for legacy inputs validated wi… |
| `evalBytes` | `EvalScript(stack, script, flags, checker, sigversion)` on a byte-level script: the `MAX_SCRIPT_SIZE` test, the `GetOp` parse, and the Script mission's inter… |
| `isPayToScriptHash` | `CScript::IsPayToScriptHash`: `OP_HASH160 <20 bytes> OP_EQUAL`, 23 bytes. |
| `decodeOpN` | `DecodeOP_N`. |
| `isWitnessProgram` | `CScript::IsWitnessProgram`: `OP_0`/`OP_1..OP_16`, a direct push of 2..40 bytes, nothing else. |
| `isPushOnlyAux` | `CScript::IsPushOnly`: every instruction parses and is a push or `OP_RESERVED`/`OP_1NEGATE`/`OP_n` (opcode at most `OP_16`). |
| `isPushOnly` |  |
| `isPayToAnchor` | `CScript::IsPayToAnchor(version, program)`. |
| `topTrue` | `CastToBool` of the top of a top-first stack; an empty stack is `false` (`SCRIPT_ERR_EVAL_FALSE`). |
| `executeWitnessScriptV0` | `ExecuteWitnessScript` for witness version 0: every witness element within `MAX_SCRIPT_ELEMENT_SIZE`, the script run with `SigVersion::WITNESS_V0`, exactly o… |
| `p2wpkhExec` | The implied P2WPKH script `OP_DUP OP_HASH160 <program> OP_EQUALVERIFY OP_CHECKSIG`. |
| `TaprootHandler` | A Taproot handler: given the witness stack (in `CScriptWitness` order, last element on top) and the 32-byte program, the verdict of the BIP341 branch. |
| `verifyWitnessProgram` | `VerifyWitnessProgram(witness, witversion, program, flags, checker, is_p2sh)`. The witness stack is in `CScriptWitness` order (last element on top). |
| `verifyScript` | `VerifyScript(scriptSig, scriptPubKey, witness, flags, checker)` with the consensus flags (`SIGPUSHONLY` and `CLEANSTACK` are policy and off). |
| `p2shBytes` | The P2SH output script `OP_HASH160 <h> OP_EQUAL`. |
| `witnessBytes` | A witness output script `OP_n <program>`. |
| `pushesBytes` | A push-only scriptSig: the canonical pushes of the given elements, in order. |

## `Def_BitcoinTaproot.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `TAPROOT_LEAF_MASK` |  |
| `TAPROOT_LEAF_TAPSCRIPT` |  |
| `TAPROOT_CONTROL_BASE_SIZE` |  |
| `TAPROOT_CONTROL_NODE_SIZE` |  |
| `TAPROOT_CONTROL_MAX_NODE_COUNT` |  |
| `TAPROOT_CONTROL_MAX_SIZE` |  |
| `ANNEX_TAG` |  |
| `VALIDATION_WEIGHT_OFFSET` |  |
| `VALIDATION_WEIGHT_PER_SIGOP_PASSED` |  |
| `SIGHASH_DEFAULT` |  |
| `OP_CHECKSIGADD` | `OP_CHECKSIGADD = 0xba` (BIP342). |
| `tagged` |  |
| `tapleafHash` | `ComputeTapleafHash(leaf_version, script)`. |
| `lexLt` | `std::lexicographical_compare` on byte strings. |
| `tapbranchHash` | `ComputeTapbranchHash(a, b)`: the lexicographically smaller first. |
| `controlNodes` | The path nodes of a control block: 32-byte chunks after the 33-byte base. |
| `taprootMerkleRoot` | `ComputeTaprootMerkleRoot(control, tapleaf_hash)`. |
| `tapTweakHash` | `XOnlyPubKey::ComputeTapTweakHash(&merkle_root)`. |
| `be32` | The 32-byte big-endian encoding of a coordinate. |
| `xonlyTweakAddCheck` | `secp256k1_xonly_pubkey_tweak_add_check(output32, parity, internal, tweak32)`: with `P` the even-`y` point of the internal key and `t` the tweak scalar (belo… |
| `checkTapTweak` | `XOnlyPubKey::CheckTapTweak(internal, merkle_root, parity)` on the output key `q`. |
| `verifyTaprootCommitment` | `VerifyTaprootCommitment(control, program, tapleaf_hash)`. |
| `ExecData` | `ScriptExecutionData` as far as the signature hash reads it. |
| `sigHashSchnorr` | `SignatureHashSchnorr(tx, in_pos, hash_type, sigversion, cache)`: `none` where it returns `false` (an undefined hash type, or `SIGHASH_SINGLE` without a matc… |
| `checkSchnorrSignature` | `CheckSchnorrSignature(sig, pubkey, sigversion, execdata)`: 64 or 65 bytes, an explicit hash type must not be `0`, the BIP341 hash, then BIP340 verification.… |
| `isOpSuccess` | `IsOpSuccess`. |
| `opSuccessScan` | The `OP_SUCCESSx` pre-scan of `ExecuteWitnessScript`: `some true` when a success opcode is reached, `some false` when the whole script parses without one, `n… |
| `TapCtx` | The context of a Tapscript execution. |
| `tapOracle` | The hash oracle for the non-signature opcodes (signature opcodes are handled by the Tapscript loop itself; the oracle's `checkSig` is never consulted). |
| `TapState` | The Tapscript execution state: the interpreter state, the validation weight left, the code-separator position, and the opcode position. |
| `evalChecksigTapscript` | `EvalChecksigTapscript`: `none` is a script error; otherwise the `success` flag and the new weight. |
| `tapExecOp` | One opcode of `EvalScript` under `SigVersion::TAPSCRIPT`, when executing or a conditional. |
| `tapStep` | One loop iteration of `EvalScript` under Tapscript: no operation count; the push-size test; the disabled-opcode test (never reached, every disabled opcode be… |
| `tapRun` |  |
| `executeTapscript` | `ExecuteWitnessScript(stack, script, flags, SigVersion::TAPSCRIPT, checker, execdata)`: the `OP_SUCCESSx` scan, the initial stack-size and element-size limit… |
| `witnessSerializedSize` | `GetSerializeSize(witness.stack)`. |
| `hasAnnex` | The annex: present when at least two elements remain and the last is non-empty and starts with `0x50`. |
| `taprootHandler` | The Taproot branch (version 1, 32-byte program, not P2SH, `TAPROOT` flag set), as a `BitcoinVerify.TaprootHandler`, for the given spent outputs. |
| `verifyScriptFull` | The complete `VerifyScript`, with the Taproot branch supplied. |
| `p2trBytes` | The output script `OP_1 <32-byte key>` of a Taproot output. |

## `Def_BitcoinActivation.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `BuriedDeployment` | `Consensus::BuriedDeployment`. |
| `deploymentHeight` | `Consensus::Params::DeploymentHeight` at mainnet values. |
| `activeAt` | `DeploymentActiveAt(index, dep) = index.nHeight >= DeploymentHeight(dep)`. |
| `activeAfter` | `DeploymentActiveAfter(pindexPrev, dep) = pindexPrev->nHeight + 1 >= DeploymentHeight(dep)`. |
| `ScriptFlags` | The consensus script-verification flags `GetBlockScriptFlags` can set. |
| `noFlags` | `SCRIPT_VERIFY_NONE`. |
| `baseFlags` | The default base `SCRIPT_VERIFY_P2SH \| SCRIPT_VERIFY_WITNESS \| SCRIPT_VERIFY_TAPROOT`. |
| `ScriptException` | `consensus.script_flag_exceptions`: the block is one of the two historical exceptions, or not. The BIP16 exception (`00000000000002dc…9c22`) maps to `SCRIPT_… |
| `exceptionBase` | The flags the exception table yields, or the default base. |
| `blockScriptFlags` | `GetBlockScriptFlags(block_index)` at mainnet: the base (default or exception), then `DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY` and `NULLDUMMY` a… |
| `ScriptFlags.le` | Pointwise inclusion of flag sets: every rule enforced by the first is enforced by the second. |
| `LOCKTIME_VERIFY_SEQUENCE` | `consensus/consensus.h`: `LOCKTIME_VERIFY_SEQUENCE = (1 << 0)`. |
| `lockTimeFlags` | The `nLockTimeFlags` of `ConnectBlock`: `LOCKTIME_VERIFY_SEQUENCE` once CSV is active at the block's height, else `0`. |

## `Def_BitcoinHeader.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `MAX_FUTURE_BLOCK_TIME` | `chain.h`: `MAX_FUTURE_BLOCK_TIME = 2 * 60 * 60`. |
| `nMedianTimeSpan` | `CBlockIndex::nMedianTimeSpan = 11`. |
| `BIP34Height` | `CMainParams`: `BIP34Height = 227931` (`DEPLOYMENT_HEIGHTINCB`). |
| `BIP66Height` | `CMainParams`: `BIP66Height = 363725` (`DEPLOYMENT_DERSIG`). |
| `BIP65Height` | `CMainParams`: `BIP65Height = 388381` (`DEPLOYMENT_CLTV`). |
| `timeWindow` | The window `GetMedianTimePast` sorts: the times of the block and its ancestors, at most `nMedianTimeSpan` of them. |
| `medianTimePast` | `GetMedianTimePast`: sort the window and take the element at index `size / 2`. The result is `0` for an empty chain, which the source never queries. |
| `Header` | A block header, reduced to the fields the contextual rules read. |
| `activeAfter` | `DeploymentActiveAfter(pindexPrev, dep)` for a buried deployment: `pindexPrev->nHeight + 1 >= DeploymentHeight(dep)`. |
| `versionOutdated` | The version floor of `ContextualCheckBlockHeader`: rejected when the version is below 2, 3 or 4 while BIP34, BIP66 or BIP65 respectively is active for the ne… |
| `contextualCheck` | `ContextualCheckBlockHeader` at mainnet parameters: `nBits` equals the required work, the time exceeds the previous block's median time past, the time is at … |

## `Def_BitcoinPow.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `width` | `2 ^ 256`, the modulus of `arith_uint256` arithmetic. |
| `powLimit` | `consensus.powLimit = uint256{"00000000ffff…ff"}`: `2 ^ 224 - 1`. |
| `targetTimespan` | `consensus.nPowTargetTimespan = 14 * 24 * 60 * 60`. |
| `targetSpacing` | `consensus.nPowTargetSpacing = 10 * 60`. |
| `difficultyAdjustmentInterval` | `Consensus::Params::DifficultyAdjustmentInterval() = nPowTargetTimespan / nPowTargetSpacing`. |
| `compactSize` | `int nSize = nCompact >> 24`. |
| `compactWord` | `uint32_t nWord = nCompact & 0x007fffff`. |
| `setCompact` | The value produced by `SetCompact`: the mantissa shifted right by `8 * (3 - nSize)` bytes when `nSize <= 3`, otherwise shifted left by `8 * (nSize - 3)` byte… |
| `compactNegative` | `*pfNegative = nWord != 0 && (nCompact & 0x00800000) != 0`. |
| `compactOverflow` | `*pfOverflow = nWord != 0 && ((nSize > 34) \|\| (nWord > 0xff && nSize > 33) \|\| (nWord > 0xffff && nSize > 32))`. |
| `specTarget` | The exact mathematical value `mantissa * 256 ^ (nSize - 3)` encoded by a compact word, with no 256-bit truncation (and floor division for `nSize <= 3`). |
| `bitLength` | `base_uint::bits()`: the bit length, `0` for `0`. |
| `getCompact` | `GetCompact(fNegative = false)` on a value below `2 ^ 256`. `GetLow64()` is the value modulo `2 ^ 64`; the assignment to the `uint32_t nCompact` reduces modu… |
| `deriveTarget` | `DeriveTarget`: the target, unless negative, zero, overflowing, or above `powLimit`. |
| `checkProofOfWork` | `CheckProofOfWorkImpl`: the header hash, read as a 256-bit number, is at most the derived target. |
| `clampTimespan` | The timespan clamp of `CalculateNextWorkRequired`: `nActualTimespan` (a signed difference of block times) is raised to `nPowTargetTimespan / 4` and lowered t… |
| `calculateNextWork` | `CalculateNextWorkRequired(pindexLast, nFirstBlockTime)` at mainnet parameters: decode the last target, multiply by the clamped timespan (modulo `2 ^ 256`), … |
| `permittedTransition` | `PermittedDifficultyTransition(params, height, old_nbits, new_nbits)` at mainnet parameters. |
| `nextWorkRequired` | `GetNextWorkRequired` at mainnet parameters, with the first block time of the period supplied by the caller. |

## `Def_BitcoinSubsidy.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `COIN` | `consensus/amount.h`: `COIN{100'000'000}`, the number of satoshis in one bitcoin. |
| `MAX_MONEY` | `consensus/amount.h`: `MAX_MONEY{21'000'000 * COIN}`, the consensus sanity bound on amounts. |
| `halvingInterval` | `kernel/chainparams.cpp`, `CMainParams`: `consensus.nSubsidyHalvingInterval = 210000`. |
| `coreSubsidy` | Transcription of `GetBlockSubsidy` (`validation.cpp`) at mainnet parameters. Block heights are nonnegative, and the `CAmount` right shift `nSubsidy >>= halvi… |
| `specSubsidy` | Declarative issuance schedule: fifty bitcoin, halved once per `halvingInterval` blocks. |
| `issuedBelow` | Total subsidy of all blocks at heights `0, 1, …, n - 1`, as `GetBlockSubsidy` computes it. |
| `intervalSum` | Sum of the per-interval subsidies for the first `m` intervals. |
| `zeroHeight` | The first height whose subsidy is zero: thirty-three halvings. |

## `Def_BitcoinMerkle.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `pairUp` | One level of the tree: hash adjacent pairs; an odd trailing element is hashed with itself, which is `hashes.push_back(hashes.back())` followed by `SHA256D64`. |
| `hasEqualPair` | The mutation test of one level: some aligned pair `(pos, pos + 1)` with `pos` even and `pos + 1 < size` consists of equal hashes. The duplicated trailing ele… |
| `rootLoop` | The `while (hashes.size() > 1)` loop with its running `mutation` flag. |
| `computeMerkleRoot` | `ComputeMerkleRoot(hashes, mutated)`: the root and the mutation flag. |

## `Def_BIP68_Model.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `Input` |  |
| `Context` |  |
| `int32Max` |  |
| `int64Max` |  |
| `specEnabled` |  |
| `specDisabled` |  |
| `specTimeBased` |  |
| `specDelay` |  |
| `inputSatisfied` |  |
| `satisfiesBIP68` |  |
| `expectedHeights` |  |
| `admissible` |  |
| `noOverflow` |  |

## `Def_BIP68_Core.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `coreEnabled` |  |
| `coreDisabled` |  |
| `coreTimeBased` |  |
| `coreDelay` |  |
| `coreSeconds` |  |
| `Accumulator` |  |
| `initial` |  |
| `coreStep` |  |
| `calculate` |  |
| `returnedHeights` |  |
| `evaluate` |  |
| `sequenceLocks` |  |

## `Def_BitcoinUtxo.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `COIN` | `consensus/amount.h`: `COIN{100'000'000}`. |
| `MAX_MONEY` | `consensus/amount.h`: `MAX_MONEY{21'000'000 * COIN}`. |
| `moneyRange` | `consensus/amount.h`: `MoneyRange(nValue) = (nValue >= 0 && nValue <= MAX_MONEY)`. |
| `COINBASE_MATURITY` | `consensus/consensus.h`: `COINBASE_MATURITY = 100`. |
| `OutPoint` | `COutPoint`: a transaction id and an output index. |
| `TxOut` | `CTxOut`, reduced to its value and to `scriptPubKey.IsUnspendable()`. |
| `Coin` | `Coin`: an unspent output with its creation height and coinbase flag. |
| `Tx` | `CTransaction`, reduced to what the accounting reads. `isCoinbase` stands for `IsCoinBase()`, i.e. a single null previous outpoint, which `CheckBlock` requir… |
| `UtxoSet` | The UTXO set: `(outpoint, coin)` entries, meant to have pairwise distinct outpoints. |
| `getCoin` | The entry for an outpoint, if present. |
| `haveCoin` | `HaveCoin`. |
| `keysNodup` | The outpoints are pairwise distinct. |
| `spendCoin` | `SpendCoin`: remove the entry for the outpoint. |
| `addCoin` | `AddCoin`: an unspendable output is not added; otherwise the entry replaces any entry with the same outpoint (`possible_overwrite`); the BIP30 check of `Conn… |
| `addCoinsFrom` | `AddCoins`: add the outputs `vout[i]` at outpoints `(txid, i)`, starting from index `i`. |
| `spendInputs` | `SpendCoin` on every input. |
| `updateCoins` | `UpdateCoins`: mark the inputs spent (not for a coinbase), then add the outputs. |
| `outputsLoop` | The output-value loop of `CheckTransaction`: each value non-negative, at most `MAX_MONEY`, and the running total in range; returns the total. |
| `sumValues` | The sum of a list of output values. |
| `valueOut` | `CTransaction::GetValueOut()`: the sum of the output values. |
| `valueIn` | `nValueIn`: the sum of the values of the coins at the given outpoints (zero for a missing coin). |
| `checkTransaction` | `CheckTransaction`, restricted to the context-free rules that concern values and inputs: non-empty inputs and outputs, the output-value loop, and no duplicat… |
| `haveInputs` | `HaveInputs`. |
| `inputsLoop` | The input loop of `CheckTxInputs`: for each input, the coin must exist, a coinbase coin must be mature (`nSpendHeight - coin.nHeight >= COINBASE_MATURITY`), … |
| `checkTxInputs` | `Consensus::CheckTxInputs`: returns the fee `txfee` on success. |
| `bip30Ok` | The BIP30 pre-check of `ConnectBlock`: no output of any transaction of the block may already exist as an unspent coin. |
| `checkBlockTxs` | The structural requirements `CheckBlock` places on the transactions: every transaction passes `CheckTransaction`, the first is a coinbase and no other is. |
| `connectLoop` | The per-transaction loop of `ConnectBlock`, restricted to accounting: for a non-coinbase transaction, `CheckTxInputs` must succeed and the accumulated fees m… |
| `connectBlock` | `ConnectBlock`, restricted to value accounting, at a height where BIP30 is enforced: the structural checks, the BIP30 pre-check, the transaction loop, and th… |
| `connectChain` | Connect a sequence of blocks at consecutive heights starting from `height`. |
| `totalValue` | The total value held in the UTXO set. |
| `subsidySum` | The sum of the subsidies at heights `h, h + 1, …, h + n - 1`. |

## `Def_BitcoinBlock.lean`

| Lean declaration | Docstring (Core symbol) |
|---|---|
| `MAX_BLOCK_WEIGHT` |  |
| `MAX_BLOCK_SIGOPS_COST` |  |
| `WITNESS_SCALE_FACTOR` |  |
| `LOCKTIME_THRESHOLD` |  |
| `SEQUENCE_FINAL` |  |
| `MINIMUM_WITNESS_COMMITMENT` |  |
| `BIP34_IMPLIES_BIP30_LIMIT` |  |
| `MAX_FUTURE_BLOCK_TIME` |  |
| `COINBASE_MATURITY` |  |
| `MAX_MONEY` |  |
| `moneyRange` | `MoneyRange`. |
| `bip34Hash` | Block hashes in serialized (internal) byte order: `consensus.BIP34Hash`. |
| `bip16ExceptionHash` | The `script_flag_exceptions` keys. |
| `taprootExceptionHash` |  |
| `bip30Repeat91842` | `IsBIP30Repeat`: the two blocks whose coinbases repeat earlier ones. |
| `bip30Repeat91880` |  |
| `bip30Unspendable91722` | `IsBIP30Unspendable`: the two blocks whose coinbases were overwritten. |
| `bip30Unspendable91812` |  |
| `isBIP30Repeat` |  |
| `isBIP30Unspendable` |  |
| `scriptException` | The `script_flag_exceptions` lookup by block hash. |
| `outPointNull` | `COutPoint::IsNull`. |
| `isCoinBase` | `CTransaction::IsCoinBase`: one input whose prevout is null. |
| `isUnspendable` | `CScript::IsUnspendable`: starts with `OP_RETURN`, or longer than `MAX_SCRIPT_SIZE`. |
| `sumValues` |  |
| `valueOut` | `CTransaction::GetValueOut`. |
| `outputsLoop` | The output loop of `CheckTransaction`: each value in `[0, MAX_MONEY]` and the running total in `MoneyRange`. |
| `checkTransaction` | `CheckTransaction`. |
| `isFinalTx` | `IsFinalTx(tx, nBlockHeight, nBlockTime)`. |
| `sigOpCountAux` | `CScript::GetSigOpCount(fAccurate)`: `CHECKSIG(VERIFY)` counts one, `CHECKMULTISIG(VERIFY)` counts the preceding `OP_n` when accurate, else 20; a parse failu… |
| `getSigOpCount` |  |
| `lastPushAux` | The last datum pushed by a push-only script (`vData` after the `GetOp` loop); `none` when some instruction fails to parse or is above `OP_16`. |
| `lastPush` |  |
| `p2shSigOpCount` | `CScript::GetSigOpCount(scriptSig)` on the output script: the accurate count of the output script unless it is P2SH, in which case the accurate count of the … |
| `witnessSigOps` | `WitnessSigOps`. |
| `countWitnessSigOps` | `CountWitnessSigOps(scriptSig, scriptPubKey, witness, flags)`. |
| `legacySigOpCount` | `GetLegacySigOpCount`. |
| `Coin` | `Coin`: an unspent output with its creation height and coinbase flag. |
| `dummyCoin` |  |
| `Ledger` | The UTXO set as an association list keyed by outpoint. |
| `getCoin` |  |
| `haveCoin` |  |
| `accessCoin` | `AccessCoin`: the coin, or a spent (dummy) coin. |
| `spendCoin` |  |
| `addCoin` | `AddCoin`: unspendable outputs are not stored; otherwise the entry replaces any existing one. |
| `addCoinsFrom` |  |
| `spendInputs` |  |
| `updateCoins` | `UpdateCoins(tx, view, undo, height)`: spend the inputs of a non-coinbase, then `AddCoins`. |
| `txUndo` | The `CTxUndo` of a transaction: the coins its inputs spend. |
| `BlockUndo` | `CBlockUndo`: one `CTxUndo` per non-coinbase transaction, in block order. |
| `Equiv` | Two ledgers with the same coins. |
| `keysNodup` | The pairwise-distinct-keys invariant. |
| `inputsLoop` |  |
| `checkTxInputs` | `Consensus::CheckTxInputs`: the fee on success. |
| `txSigOpCost` | `GetTransactionSigOpCost(tx, view, flags)`. |
| `sequenceLocksOk` | `SequenceLocks(tx, nLockTimeFlags, prevheights, *pindex)` through the BIP68 mission's transcription; `mtp h` is the median time past of the chain at height `h`. |
| `inputScriptsOk` | `CheckInputScripts`: every input's script verifies under the block's flags, with the complete `VerifyScript` (Taproot branch included) and the spent outputs … |
| `LoopState` | The accumulator of the `ConnectBlock` loop. |
| `connectLoop` | The transaction loop of `ConnectBlock`, in source order: `CheckTxInputs`, the fee range, `SequenceLocks`, the sigop budget, `CheckInputScripts`, `UpdateCoins`. |
| `ChainState` | A validated chain: its headers from the genesis to the tip, and the UTXO set. |
| `initialState` | Genesis initialization: the genesis header, and an empty UTXO set (the genesis coinbase is not spendable). |
| `ChainState.tipHeight` |  |
| `ChainState.tip` |  |
| `ChainState.tipHash` |  |
| `ChainState.nextHeight` | The height of the next block. |
| `ChainState.timesTo` | The times of the blocks at heights `0..h`, most recent first. |
| `ChainState.mtpAt` | `GetMedianTimePast` of the block at height `h`. |
| `ChainState.mtp` | The median time past of the tip. |
| `ChainState.mtpNat` | The `Context.mtp` function of the BIP68 mission (times are non-negative on any real chain). |
| `ChainState.requiredBits` | `GetNextWorkRequired(pindexLast, …)`: the first block of the period is the ancestor at `nHeight - 2015`. |
| `blockProof` | `GetBlockProof`: `(~target / (target + 1)) + 1` on 256-bit words, zero for an invalid target. |
| `ChainState.chainWork` | `nChainWork`. |
| `hashValue` | The hash of a block as a 256-bit number (`uint256` is little-endian). |
| `merkleCombine` |  |
| `zeroHash` |  |
| `blockMerkleRoot` | `BlockMerkleRoot(block, &mutated)`. |
| `blockWitnessMerkleRoot` | `BlockWitnessMerkleRoot`: the coinbase's witness hash is zero. |
| `checkHeaderPow` | `CheckProofOfWork(block.GetHash(), block.nBits)`. |
| `checkBlock` | `CheckBlock` with `fCheckPOW` and `fCheckMerkleRoot`, in source order. |
| `heightScript` | `CScript() << nHeight` for a non-negative height. |
| `isCommitmentOutput` | `GetWitnessCommitmentIndex`: the last coinbase output of at least 38 bytes starting with `6a 24 aa 21 a9 ed`. |
| `witnessCommitmentIndex` |  |
| `checkWitnessMalleation` | `CheckWitnessMalleation(block, expect_witness_commitment)`. |
| `contextualCheckBlock` | `ContextualCheckBlock(block, pindexPrev)`: finality against the lock-time cutoff, the BIP34 coinbase height, the witness commitment, and the weight limit. |
| `bip30Checked` | `fEnforceBIP30 \|\| nHeight >= BIP34_IMPLIES_BIP30_LIMIT`: the BIP30 scan is performed unless the block is one of the two repeats or the BIP34 activation blo… |
| `bip30Ok` | The BIP30 scan: no output of the block already exists as an unspent coin. |
| `connectBlock` | `ConnectBlock` after `CheckBlock`: the genesis shortcut, BIP30, the flags, the loop, the coinbase bound. Returns the new ledger and the undo data. |
| `Outcome` | The outcome of offering a block to a chain state: accepted with the new state and undo data; rejected as invalid; rejected only because its time is too far i… |
| `acceptHeader` | `AcceptBlockHeader` for a header on top of the tip: `CheckBlockHeader` (proof of work), the previous-block lookup, then `ContextualCheckBlockHeader` in sourc… |
| `validate` | The source-linked validation outcome `C(S, B, t)`: the header path, `CheckBlock`, `ContextualCheckBlock`, `ConnectBlock`. |
| `accepts` |  |
| `Reachable` | Reachability from the genesis state through accepted blocks. |
| `applyTxInUndo` | `ApplyTxInUndo`: restore a spent coin; `none` is `DISCONNECT_FAILED`, the flag is `fClean`. |
| `restoreInputs` | Restore the inputs of a transaction in reverse order. |
| `spendOutputs` | Spend the (spendable) outputs of a transaction, checking each against the block. |
| `disconnectTx` | Undo one transaction: its outputs, then (for a non-coinbase) its inputs. |
| `disconnectTxs` |  |
| `disconnectBlock` | `DisconnectBlock(block, pindex, view)`: the undo-count test, the two unspendable-coinbase exceptions, and the transactions in reverse order. |
| `TxSpec` | Transaction well-formedness, as a predicate. |
| `valueIn` | The sum of the values of the coins spent by the inputs. |
| `feeOf` | The fee of a transaction against a ledger. |
| `TxInputsSpec` | Admissibility of one non-coinbase transaction against the ledger `u` at `height`: every input spends an existing, mature coin of valid value; the total input… |
| `TxsSpec` | The transactions of a block, applied in order: each is admissible against the ledger produced by its predecessors, the accumulated fees and sigop cost stay w… |
| `applyTxs` | The ledger after applying the transactions in order. |
| `totalFees` | The total fees of a block's non-coinbase transactions, against the running ledger. |
| `applySpec` | The declarative state transition `ApplySpec(S, B)`. |
| `HeaderSpec` | The header rules as a predicate: a valid compact target met by the hash (the PoW mission's specification form), the tip as parent, the required difficulty, t… |
| `BlockSpec` | The context-free block rules as a predicate. |
| `ContextSpec` | The contextual block rules as a predicate. |
| `LedgerSpec` | The ledger rules as a predicate: BIP30 where it applies, the transaction sequence, and the coinbase bound against the specification subsidy. |
| `Valid` | Declarative admissibility `V(S, B, t)`. |
| `LedgerOk` | A ledger with distinct keys whose coins are spendable and were created above the genesis. |
| `WellFormed` | The well-formedness every reachable state enjoys: a non-empty header list starting at the genesis, distinct ledger keys, and spendable coins created at heigh… |
