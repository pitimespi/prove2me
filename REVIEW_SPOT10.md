# Spot 10: `ConnectBlock` versus `BitcoinBlockV2.connectBlock` / `connectLoop`

Core: [`validation.cpp:2294`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2294)
(`ConnectBlock`), [`:6207`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L6207)
(`IsBIP30Repeat`), [`:2249`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249)
(`GetBlockScriptFlags`), [`:2060`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2060)
(`CheckInputScripts`), [`:1998`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1998)
(`UpdateCoins`), [`tx_verify.cpp:170`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L170)
(`CheckTxInputs`), [`:45`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45)
(`CalculateSequenceLocks`, `EvaluateSequenceLocks`), [`coins.cpp:80`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp#L80)
(`AddCoin`, `AddCoins`, `SpendCoin`). Lean: `Definitions/Def_BitcoinBlockV2.lean`. Read-back:
`missions/readbacks/block/readback_Def_BitcoinBlock.md`.

## Verdict

Agreement on the order of every test, on the BIP30 rule with its two repeat blocks and the BIP34
shortcut, on `CheckTxInputs`, on the BIP68 bridge, on the coinbase bound, and on the ledger update.
The sigop cost the loop consumes is spot 11, where a defect was found (F1).

## `ConnectBlock` — `connectBlock`

| Core | Lean | Agree |
|---|---|---|
| `CheckBlock` (skipped when `fChecked`) | `checkBlock` runs once in `validate`, before `contextualCheckBlock` and `connectBlock`, as `AcceptBlock` does | yes |
| `block_hash == hashGenesisBlock` → true, no coins | `hash = genesisHash → some (S.utxo, [])` | yes |
| assumed-valid: `fScriptChecks` may be false | always true (`-assumevalid=0`, limit L4) | by design |
| `fEnforceBIP30 = !IsBIP30Repeat(pindex)` (heights 91842 and 91880 with their hashes); `&& !(GetAncestor(BIP34Height) exists with hash == BIP34Hash)`; scan if `fEnforceBIP30 ‖ nHeight ≥ 1983702` | `bip30Checked`: `(!isBIP30Repeat ∧ !bip34Ancestor) ∨ 1983702 ≤ height`, with `bip34Ancestor` = `S.headers[227931]?` has hash `bip34Hash` | yes (`GetAncestor(227931)` of the parent exists iff the parent's height is at least 227931, iff the header list has an element at that index) |
| the scan: every output index of every transaction, `view.HaveCoin` → `bad-txns-BIP30` (the error is recorded, the loop breaks at its next iteration) | `bip30Ok` false → `none` | yes |
| `nLockTimeFlags = LOCKTIME_VERIFY_SEQUENCE` iff CSV active at the block's height | `lockTimeFlags height` | yes |
| `GetBlockScriptFlags(pindex)`: base `P2SH‖WITNESS‖TAPROOT` or the exception table by block hash; `DERSIG`, `CLTV`, `CSV`, `NULLDUMMY` by activation height | `blockScriptFlags height (scriptException hash)` (Activation mission) | yes |
| per transaction, in order: not coinbase → `CheckTxInputs` (fee), `MoneyRange(nFees)`, prevheights from the view, `SequenceLocks`; then for every transaction `nSigOpsCost += GetTransactionSigOpCost(tx, view, flags)` with the view *before* this transaction's update, `> 80000` → fail; then not coinbase → `CheckInputScripts`; then `UpdateCoins` | `connectLoop`: the same six steps in the same order on `st.utxo` | yes |
| `CheckInputScripts`: coinbase → true; for each input a `CScriptCheck` with the spent output, `VerifyScript` with the block flags and `CachingTransactionSignatureChecker(tx, i, amount, txdata)` (the spent outputs for BIP341) | `inputScriptsOk`: `verifyScriptFull spent ⟨flags, tx, i, amount⟩ scriptSig scriptPubKey witness` for every input index | yes (the script-execution cache only skips re-verification) |
| parallel script checks are collected and `control->Complete()` after the loop | sequential | yes: the verdict is the conjunction either way |
| after the loop: `vtx[0]->GetValueOut() > nFees + GetBlockSubsidy(nHeight)` → `bad-cb-amount` | identical with `coreSubsidy` | yes |
| `fJustCheck`, undo write, `SetBestBlock` | undo returned, headers appended in `validate` | by design |

## `CheckTxInputs` — `checkTxInputs`

`HaveInputs` (every prevout present; coinbase exempt, and the Lean only calls this for
non-coinbases); for each input: `coin.IsCoinBase() && nSpendHeight − coin.nHeight < 100` → fail;
`nValueIn += value`; `MoneyRange(value) ∧ MoneyRange(nValueIn)`; `nValueIn < GetValueOut()` → fail;
`MoneyRange(fee)`. Identical. The subtraction is `int` in Core and natural-number subtraction in
Lean; they agree whenever `coin.nHeight ≤ nSpendHeight`, which `reachable_wellFormed` guarantees for
every coin of a reachable state (coins are created at heights up to the tip, below the spend
height).

## `SequenceLocks` — `sequenceLocksOk`

`CalculateSequenceLocks(tx, flags, prevheights, *pindex)`: `fEnforceBIP68 = version ≥ 2 ∧ flags & 1`
with `version` an unsigned 32-bit value; per input the BIP68 mission's `coreStep` with
`GetAncestor(max(nCoinHeight − 1, 0))->GetMedianTimePast()` of the *new* block's index, i.e. the
chain's MTP at that height; `EvaluateSequenceLocks` against `pprev->GetMedianTimePast()` =
the MTP at the tip. The Lean builds the BIP68 `Context` as `⟨height, S.mtpNat⟩` with `mtpNat h` the
MTP over headers `0..h` (so `mtp (height − 1)` is the tip's), and the inputs as `(sequence, coin
height)` pairs from the ledger. Identical; `toNat` on the integer MTP is exact for non-negative
times.

## `UpdateCoins` / `AddCoins` / `AddCoin` / `SpendCoin` — `updateCoins`

Spend every input of a non-coinbase (the coin must exist; `assert(is_spent)`), then add each
output `(txid, i)` at `nHeight` with the coinbase flag; `AddCoin` returns without storing an
`IsUnspendable` script; with `possible_overwrite` (true for coinbases, which is what BIP30 is
about) an existing entry is replaced. Identical. The undo data (`txundo.vprevout`) is the list of
spent coins, as `txUndo` records before the spend.

## Vectors

`tests/Block170Test.lean` runs this path on real mainnet data (block 170 against block 9's
coinbase), including rejection of an altered signature and of an immature coinbase, and the clean
disconnect. The six branches without a vector — the two repeat blocks, the BIP34 shortcut, the
1,983,702 limit, the fee-range and sigop-budget failures — are decided by the comparison above and
by `bip30_history`, `connectLoop_iff` and `connectBlock_iff`, whose statements spell the branches
out.
