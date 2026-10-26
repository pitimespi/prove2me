## Why script dispatch is consensus

`EvalScript` decides what a script does; `VerifyScript` decides which scripts run, on what stack, under which signature version, and what counts as success. It is where pay-to-script-hash (BIP16), segregated witness (BIP141) and the hand-off to Taproot live: the output script is evaluated first, then — if it is a witness program — the witness is interpreted, or — if it is P2SH — the redeem script is extracted from the scriptSig and run, possibly revealing a wrapped witness program. Each of these steps carries anti-malleability rules (an empty scriptSig for native witness, exactly one push for wrapped witness, push-only scriptSigs for P2SH, a clean witness stack) and the future-compatibility rule that unknown witness versions succeed. ([`VerifyScript`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp), [BIP16](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0016.mediawiki), [BIP141](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0141.mediawiki))

This mission transcribes `VerifyScript`, `VerifyWitnessProgram` for version 0 and the unknown versions, `ExecuteWitnessScript`, and the script predicates, on top of the published interpreter and signature layer, and proves that the four spending templates that carry the chain's history behave as advertised — P2SH, native P2WPKH, native P2WSH, P2SH-wrapped P2WPKH — and that the malleability and compatibility rules hold as universal statements.

## Evaluations, stacks, and the dispatch

A **byte-level evaluation** parses a script with `GetOp`, rejects scripts over 10,000 bytes, and runs the Script mission's interpreter with the signature mission's concrete oracle for the given signature version (`BASE` or `WITNESS_V0`) and script code. Stacks are top-first; a `CScriptWitness` lists its elements first to last, the last being the top, so witness stacks are reversed before execution.

`VerifyScript` runs the scriptSig, keeps a copy of the resulting stack, runs the output script, and requires a true top. With `WITNESS`, an output that is a witness program (`OP_n` and one push of 2–40 bytes) must have an empty scriptSig and is handed to `VerifyWitnessProgram`. With `P2SH`, an output `OP_HASH160 <h> OP_EQUAL` requires a push-only scriptSig; the copied stack is restored, its top is the serialized redeem script, which is run on the remainder and must leave a true top; with `WITNESS`, a redeem script that is a witness program must be the scriptSig's only push and is handed to `VerifyWitnessProgram` as P2SH-wrapped. Finally, with `WITNESS`, a non-empty witness that no program consumed fails.

`VerifyWitnessProgram` for version 0 distinguishes a 32-byte program (P2WSH: the last witness element is the script, its SHA-256 must be the program) from a 20-byte one (P2WPKH: exactly two elements, the implied `DUP HASH160 <program> EQUALVERIFY CHECKSIG`); `ExecuteWitnessScript` requires every element within 520 bytes and exactly one true element at the end. Version 1 with a 32-byte program outside P2SH is Taproot, delegated to a handler parameter when the `TAPROOT` flag is on; pay-to-anchor and every other version/size combination succeed.

## Formalization targets

### Goal — native P2WPKH is correct
$$
\mathrm{verifyScript}([\,],\ \mathtt{OP\_0}\langle h\rangle,\ [sig, pk]) \iff \mathrm{castToBool}(h) \wedge \mathrm{Hash160}(pk) = h \wedge \mathrm{checkSig}_{\mathrm{V0}}(\text{p2pkh}(h), sig, pk)
$$
for every 20-byte $h$, every signature and key within the push limit, every transaction, amount and flag set with `WITNESS`. This is `BitcoinVerify.p2wpkh_correct`: the most common output type on the network today is correct against the full dispatch, the interpreter and the concrete BIP143 checker. The first conjunct is a genuine finding of the transcription: `OP_0 <h>` is evaluated as a script before the witness is consulted, so an all-zero program is unspendable.

### Supporting milestones
1. **Predicates** (`isPayToScriptHash_iff`, `isWitnessProgram_iff`): the byte tests are exactly the templates.
2. **Push-only scriptSigs** (`parseScript_pushes`, `isPushOnly_pushes`): canonical pushes parse back and are push-only.
3. **Malleability rules** (`native_witness_malleated`, `witness_unexpected`): non-empty scriptSig on a witness program fails; an unconsumed witness fails.
4. **Future compatibility** (`unknown_witness_version`): unknown versions succeed exactly when the program is a true script value.
5. **P2WSH** (`p2wsh_correct`): the witness script, hashed to the program, runs on the remaining elements and must leave one true element.
6. **P2SH** (`p2sh_correct`): hash match and redeem evaluation on the pushed arguments.
7. **P2SH-P2WPKH** (`p2sh_p2wpkh_correct`): the wrapped program through the P2SH path.

## What the result establishes

The template theorems are two-directional: they say what spends succeed *and* that nothing else does, for every oracle verdict. Combined with the signature mission they reduce the correctness of the four templates to Hash160 equalities and ECDSA verification of the appropriate sighash. The rule theorems make BIP141's malleability protections and its upgrade hooks universal facts about the transcription rather than test cases.

What is left to the Taproot mission: the version-1 branch (`TaprootHandler`) and Tapscript. What is policy and off: `SIGPUSHONLY`, `CLEANSTACK`, `MINIMALIF`, `DISCOURAGE_*`. Known modeling limit inherited from the Script mission: `OP_CODESEPARATOR` positions are not tracked, so the oracle's script code is the whole executed script (exact for scripts without the opcode).

Status: all statements are open with intentional placeholder proofs. The dispatch has been checked by evaluation against independently signed P2WPKH, P2SH-P2WPKH and legacy P2SH spends and their negative variants.

## Where the obvious argument fails

The base evaluation of a witness output is easy to forget: `OP_0 <h>` must itself evaluate to a true top before the witness is looked at, which produces the `castToBool h` conjunct and the all-zero exception. The P2SH path reasons about two stacks — the one after the scriptSig (restored and popped) and the one after the output script (only its top matters) — and about the parse of the scriptSig twice (as pushes, and as `IsPushOnly`). The unknown-version theorem needs the evaluation of `OP_n` for every $n$ in 1–16 through the interpreter's small-integer branch, with its count and disabled-opcode exemptions. Witness order (last element on top) must be threaded through `reverse`, `dropLast` and `getLast?` consistently.

## Formalization scope

Flags are the seven consensus flags of `GetBlockScriptFlags`. The amount is an integer (negative where unknown, as the source passes for legacy inputs). The Taproot branch is a parameter. No Mathlib is required; the development imports only `Std`.

A trivializing formalization would define `verifyScript` by cases on the templates; here it is the source's control flow and the templates are theorems.

## Selected references

- Bitcoin Core contributors. *`VerifyScript`, `VerifyWitnessProgram`, `ExecuteWitnessScript`*, `src/script/interpreter.cpp`, and *`CScript` predicates*, `src/script/script.cpp`, at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp)
- Gavin Andresen. *BIP16: Pay to Script Hash*, 2012. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0016.mediawiki)
- Eric Lombrozo, Johnson Lau, Pieter Wuille. *BIP141: Segregated Witness (Consensus layer)*, 2015. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0141.mediawiki)
- Johnson Lau, Pieter Wuille. *BIP143*, 2016. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0143.mediawiki)
