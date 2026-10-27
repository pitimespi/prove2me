# Spot 1: `EvalScript` (SigVersion::BASE) versus `BitcoinScript.step` / `execOp` / `run`

Core: [`interpreter.cpp:417`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L417)
(`EvalScript`), [`script.h:227`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h#L227)
(`CScriptNum`), `interpreter.cpp:283` (`ConditionStack`), `interpreter.cpp:43` (`CastToBool`).
Lean: `Definitions/Def_BitcoinScript.lean`. Read-back: `missions/readbacks/script/readback_Def_BitcoinScript.md`.

Conventions that must be kept in mind throughout: Lean stacks are top-first lists (`stacktop(-1)` is
the head); a script is already parsed into `push data` / `op byte` instructions (the parse and the
10,000-byte limit live in `BitcoinSig.parseScript` and `BitcoinVerify.evalBytes`); policy flags
(`MINIMALDATA`, `MINIMALIF`, `NULLFAIL`, `CONST_SCRIPTCODE`, `DISCOURAGE_UPGRADABLE_NOPS`) are off,
so `fRequireMinimal = false` everywhere.

## Verdict

Agreement on every opcode and on the loop, with two deviations, both in how the signature checker
sees the script code (L1 and the new L10 below), and one representation difference that is
observationally equivalent (the condition stack). Opcode byte values in the Lean match the
`opcodetype` enum exactly (checked mechanically).

## The loop (`step`, `run`)

| Core (`EvalScript`) | Lean | Agree |
|---|---|---|
| `fExec = vfExec.all_true()` at the top of each iteration | `allTrue s.vfExec` | yes |
| `GetOp` failure → `SCRIPT_ERR_BAD_OPCODE` | parse failure is `parseScript = none` upstream | yes |
| `vchPushValue.size() > 520` → fail, *checked for every instruction, executed or not* | `step (.push data)`: `520 < data.length → none` before the `fExec` test; `op` instructions carry no data | yes |
| `opcode > OP_16 && ++nOpCount > 201` → fail; the count is incremented for skipped opcodes too | `counted := OP_16 < c`; fail if `201 < opCount + 1`; increment; done before the `fExec` test | yes |
| Disabled opcodes fail *even when not executed* | `isDisabled c → none` before the `fExec` test; the fifteen opcodes match CVE-2010-5137's list | yes |
| `CONST_SCRIPTCODE` test on `OP_CODESEPARATOR` | policy, off | yes |
| `fExec && opcode ≤ OP_PUSHDATA4` → push (`MINIMALDATA` off) | push only if `allTrue` | yes |
| `else if fExec \|\| (OP_IF ≤ opcode ≤ OP_ENDIF)` → the `switch` | same condition → `execOp` | yes |
| a non-executed, non-conditional opcode does nothing | `some s` | yes |
| `stack.size() + altstack.size() > 1000` after *every* iteration | checked in all three branches of `step` | yes |
| `scriptnum_error` → fail | `toNum = none → none` | yes |
| after the loop: `!vfExec.empty()` → fail | `run _ [] = if vfExec.isEmpty then some s else none` | yes |
| `OP_VERIF`/`OP_VERNOTIF` (0x65/0x66) are inside `OP_IF..OP_ENDIF`, so they fail even in an unexecuted branch; `OP_VER` (0x62) and `OP_RESERVED` (0x50) fail only when executed | `execOp` ends with `else none`; 0x65/0x66 enter it via the range test; 0x62/0x50 only when `fExec` | yes |

**Condition stack.** Core's `ConditionStack` stores only the size and the position of the first
`false`; `toggle_top` on a top that is not the first false leaves the stored state unchanged. The
Lean stores the actual booleans and toggles the top. The only observations Core makes are
`all_true`, `empty`, `push_back`, `pop_back`, `toggle_top`; under the invariant "`m_first_false_pos`
is the index of the first `false`, or `NO_FALSE`", the two representations agree on every
observation (toggling a top that is not the first false cannot change `all_true`, and after a later
`pop_back` reaching that position Core recomputes nothing but the position stays correct because
the first false was below). Agree, by this argument; a reviewer should reproduce it.

## Opcodes

Stack pictures are written top-first, as the Lean does. `n(x)` is `CScriptNum(x, false, 4)`.

| Opcode(s) | Core | Lean | Agree |
|---|---|---|---|
| `OP_1NEGATE`, `OP_1`…`OP_16` | push `n(opcode − 0x50)` | `pushNum (c − (OP_1 − 1))`; 0x4f gives −1 | yes |
| `OP_NOP`, `OP_NOP1`, `OP_NOP4`…`OP_NOP10` | nothing (`DISCOURAGE_UPGRADABLE_NOPS` off) | `some s` | yes |
| `OP_CHECKLOCKTIMEVERIFY` | flag off → nop; empty stack fail; `CScriptNum(top, false, 5)`; `< 0` fail; `checker.CheckLockTime` fail; leaves the stack | identical, `toNum false 5`, oracle `checkLockTime` | yes |
| `OP_CHECKSEQUENCEVERIFY` | as above, plus `(nSequence & (1<<31)) != 0` → nop before the checker | `n.toNat &&& 2^31 ≠ 0 → some s` (n ≥ 0 here, so `toNat` is exact) | yes |
| `OP_IF`/`OP_NOTIF` | if `fExec`: empty fail; `MINIMALIF` is Tapscript-only / policy; `CastToBool`, negate for `NOTIF`, pop, push; else push `false` | identical | yes |
| `OP_ELSE` | empty → fail; `toggle_top` | `(!b) :: rest` | yes (see above) |
| `OP_ENDIF` | empty → fail; pop | identical | yes |
| `OP_VERIFY` | empty fail; pop iff true else fail | identical | yes |
| `OP_RETURN` | fail | `none` | yes |
| `OP_TOALTSTACK`/`OP_FROMALTSTACK` | move the top between stacks | identical | yes |
| `OP_2DROP` | need 2, pop 2 | identical | yes |
| `OP_2DUP` | `a b … → a b a b …` | identical | yes |
| `OP_3DUP` | `a b d … → a b d a b d …` | identical | yes |
| `OP_2OVER` | `x4 x3 x2 x1 … → x2 x1 x4 x3 x2 x1 …` | identical | yes |
| `OP_2ROT` | erase the 5th and 6th, push them: `x6…x1 → x2 x1 x6 x5 x4 x3` | identical | yes |
| `OP_2SWAP` | `x4 x3 x2 x1 → x2 x1 x4 x3` | identical | yes |
| `OP_IFDUP` | dup iff `CastToBool` | identical | yes |
| `OP_DEPTH` | push `n(size)` | `pushNum s.stack.length` (altstack not counted) | yes |
| `OP_DROP`, `OP_DUP`, `OP_NIP`, `OP_OVER`, `OP_SWAP`, `OP_TUCK` | standard | identical | yes |
| `OP_PICK`/`OP_ROLL` | need 2; `n = getint(top)`; pop; `n < 0 \|\| n ≥ size` fail; take `stacktop(-n-1)`; `ROLL` erases it; push | `rest.isEmpty → none`; `toNum false 4`; `n < 0 ∨ rest.length ≤ n → none`; `rest[n]`; `eraseAt` for `ROLL` | yes (`getint` clamping is unreachable with 4-byte numbers) |
| `OP_ROT` | `x3 x2 x1 → x1 x3 x2` | identical | yes |
| `OP_SIZE` | push `n(top.size)`, keep top | identical | yes |
| `OP_EQUAL`/`OP_EQUALVERIFY` | byte equality; `VERIFY` pops the result iff equal else fail | identical | yes |
| `OP_1ADD` … `OP_0NOTEQUAL` | `n(top)`; result pushed as `getvch` (may be 5 bytes) | `toNum false 4`, unbounded `Int`, `serialize` | yes (int64 cannot overflow from 4-byte inputs) |
| `OP_ADD` … `OP_MAX` | `bn1 = n(top(-2))`, `bn2 = n(top(-1))`, both parsed before any arithmetic; `NUMEQUALVERIFY` pops the pushed result iff `CastToBool` | `n1 := toNum b`, `n2 := toNum a` for `a :: b`, both must parse; `r ≠ 0` | yes (`serialize 1 = [1]`, `serialize 0 = []`, so `CastToBool` of the result is `r ≠ 0`) |
| `OP_WITHIN` | `bn2 ≤ bn1 && bn1 < bn3` with `bn1 = top(-3)` | `n2 ≤ n1 ∧ n1 < n3` with `n1 := toNum d` for `a :: b :: d` | yes |
| hash opcodes | hash the top, replace | oracle hashes (concrete in `BitcoinSig.legacyOracle`) | yes |
| `OP_CODESEPARATOR` | `pbegincodehash = pc` | `some s` | **no: L1** |
| `OP_CHECKSIG`/`VERIFY` | sig = `top(-2)`, key = `top(-1)`; `EvalChecksig` false → script fails; else push/verify | `pubkey :: sig :: rest`; oracle `none` → fail | yes, given the oracle (`FindAndDelete` of this one signature, encoding checks, `CheckECDSASignature` on the script code from `pbegincodehash`, which is the whole script under L1) |
| `OP_CHECKSIGADD` | `BAD_OPCODE` in BASE | falls to `else none` | yes |
| `OP_CHECKMULTISIG`/`VERIFY` | see below | see below | **partial: L10** |
| anything else (`OP_VER`, `OP_RESERVED1/2`, 0xba–0xff, `OP_RESERVED`) | `BAD_OPCODE` when executed | `else none` | yes |

### `OP_CHECKMULTISIG` in detail

Stack, top-first: `nKeys, key_1 … key_M, nSigs, sig_1 … sig_N, dummy, …` (so `key_1` and `sig_1` are
the ones nearest the top).

| Core | Lean | Agree |
|---|---|---|
| empty → fail; `nKeys = getint(top)`; `0 ≤ nKeys ≤ 20` else fail | identical (`toNum false 4`) | yes |
| `nOpCount += nKeys; > 201 → fail` | `opCount := s.opCount + nKeys` (the `++` for the opcode itself already happened in `step`); `201 < opCount → none`; the new count is stored on success | yes |
| need `2 + nKeys` elements (keys and the sig count) | `keys.length ≠ nKeys → none`, then `match rest with [] => none` | yes |
| `0 ≤ nSigs ≤ nKeys` else fail | identical | yes |
| need `3 + nKeys + nSigs` elements, *including the dummy*, checked before any signature check | the dummy is required *after* `multisigLoop` | equivalent: both paths fail, and the loop is pure |
| `FindAndDelete` of **every** signature's push from `scriptCode` before the first check | the oracle deletes only the signature being checked | **no: L10** |
| loop: encoding checks for each examined `(sig, key)` pair (script error on failure); on match advance both, else advance the key; `nSigs > nKeys → false` | `multisigLoop`: `checkSig = none → none`; same advancing; `keys.length < sigs.length → false` after each step | yes |
| pop `2 + nKeys + nSigs` elements (`NULLFAIL` off), then the dummy: `NULLDUMMY` → non-empty dummy fails; pop; push result; `VERIFY` variant | identical | yes |

## Findings

**L1 (known, confirmed).** `OP_CODESEPARATOR` does not move the start of the script code in BASE
and WITNESS_V0. The oracle always receives the whole executed script. Exact for every script in
which no `OP_CODESEPARATOR` is *executed*; such scripts exist on mainnet (rare).

**L10 (new).** In `OP_CHECKMULTISIG`, Core removes the pushes of *all* `nSigs` signatures from the
script code before checking any of them; the model's oracle interface (`checkSig : sig → key →
Option Bool`) can only remove the signature it is given. The two differ exactly when the script
code (the scriptPubKey, redeem script or witness script being executed) contains a push of one of
the *other* signatures of the same `OP_CHECKMULTISIG` — a script whose own bytes embed a signature
that is also supplied on the stack. No standard template does this; Core's `script_tests.json`
contains deliberately constructed cases (search `FindAndDelete`). Fixing it means widening the
oracle to `checkSig : (allSigs : List Bytes) → sig → key → Option Bool` in the Script mission and
threading the signature list through `multisigLoop`, which changes a published definition and
therefore needs a new mission revision; the P2PKH goal and every current theorem would carry over.

Together, L1 and L10 are the complete list of places where `BitcoinVerify.evalBytes` under
`SigVersion::BASE` is known to differ from `EvalScript`. Under `WITNESS_V0`, `FindAndDelete` is not
applied (Core and Lean agree), so only L1 remains there; under `TAPSCRIPT` neither applies.

**Representation note.** The condition stack argument above should be reproduced by the reviewer;
it is the one place where the Lean does not mirror Core's data structure.

## Adversarial vectors worth adding to `tests/ScriptVectors.lean`

Each is a script where a plausible transcription slip would change the verdict. Expected verdicts
are what Core gives; evaluate with `evalScript` on an empty stack and compare.

1. 200 × `OP_NOP` then `OP_1`: succeeds (count 200). 201 × `OP_NOP` then `OP_1`: succeeds (201 is
   allowed). 202 × `OP_NOP`: fails. The same with `OP_16` interleaved: `OP_16` never counts.
2. `OP_0 OP_IF OP_CAT OP_ENDIF OP_1`: fails (disabled opcode in an unexecuted branch).
3. `OP_0 OP_IF OP_VER OP_ENDIF OP_1`: succeeds. `OP_0 OP_IF OP_VERIF OP_ENDIF OP_1`: fails.
4. `OP_1 OP_IF OP_ELSE OP_ELSE OP_1 OP_ENDIF` with a nested unexecuted branch: tests `toggle_top`
   when the first false is below the top.
5. 999 pushes of `OP_1` then `OP_TOALTSTACK OP_1 OP_1`: fails at 1001 total; without the altstack
   move it also fails at 1001; with 998 it succeeds.
6. `OP_1 OP_2 OP_3 2 OP_ROLL`: result `[1, 3, 2]` top-first (`x1` rolled to the top).
   `OP_1 OP_2 OP_3 OP_4 OP_5 OP_6 OP_2ROT`: `[2, 1, 6, 5, 4, 3]` top-first.
7. `0x80 OP_NOT`: `n([0x80]) = 0`, result `[1]`. `0x80 OP_IF OP_0 OP_ELSE OP_1 OP_ENDIF`: negative
   zero is false, result `[1]`.
8. `OP_1 OP_1 OP_1 OP_ADD` with a 5-byte push `0x0000000080`: fails (`toNum` 4-byte limit), while
   the same under `OP_CHECKLOCKTIMEVERIFY` with the flag parses (5 bytes).
9. `OP_1NEGATE OP_1 OP_WITHIN`-style boundary cases: `x min max` with `x = max` is false.
10. Multisig: a 2-of-3 with the signature order reversed on the stack fails; with a non-empty dummy
    it fails only when `NULLDUMMY` is set; `nKeys = 21` fails; `nSigs = 3 > nKeys = 2` fails; the
    sigop count `nOpCount + nKeys` crossing 201 fails.
