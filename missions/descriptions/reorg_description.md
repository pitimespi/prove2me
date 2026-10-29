## The claim

A Bitcoin node does not keep every chain it has seen; it keeps one UTXO set, and when a longer branch arrives it *reorganizes*: it disconnects blocks from its tip, restoring the coins each block spent from the undo data it wrote when it connected them, and then connects the blocks of the new branch. The claim a node relies on is that the state it ends up with is the same state it would hold had it validated the new branch directly — that the UTXO set is a function of the chain, not of the path by which the node arrived at it. If this failed, two honest nodes with the same chain could hold different coins.

The block mission proved that one block's undo data restores the ledger before it (`disconnect_connect`). This mission extends that to chains and states the reorganization property itself.

## What is proved

The relation `StateEquiv` identifies states with the same headers and the same coin at every outpoint (the ledger is an association list; its order is an artefact of the model). Then:

- **Congruence** (`updateCoins_equiv`, `connectBlock_equiv`, `validate_equiv`): every ledger read of validation goes through `getCoin`, so `validate` on equivalent states gives the same outcome and equivalent results with the same undo data. The header path reads only the headers.
- **One block from any equivalent ledger** (`disconnect_connect_equiv`): the block mission's undo theorem with its final ledger generalized.
- **Chains** (`connectChain_reachable`, `connectChain_equiv`): a chain connected to a reachable state visits reachable states; connecting to equivalent states gives equivalent results.
- **Multi-block undo** (`disconnectChain_connectChain`): a chain connected to a reachable state under the freshness conditions (distinct txids within a block, no pre-existing coin for a block's txids, not the genesis hash — the BIP30 conditions that BIP34 guarantees on mainnet) is disconnected by its undo data, tip first, cleanly, back to a state equivalent to the starting one.
- **Consistency** (`consistent_connectChain`): a state equivalent to a reachable one stays so under connection.
- **Goal** (`reorg_safety`): connect `bs` to a reachable `S`, disconnect it, connect any `cs`: the disconnect was clean, and the result is equivalent to the state that connecting `cs` directly to `S` produces, which is reachable, with the same undo data.

## What this rests on

The block mission's `validate`, `disconnectBlock`, `reachable_wellFormed`, `apply_spec`, `checkBlock_iff` and `checkTxInputs_iff`, and the lemmas of its undo proof, carried over. The freshness conditions are hypotheses, as in the block mission; proving that BIP34 implies them on the mainnet chain is a separate claim. The theorems are about the model's one-at-a-time reorganization; Core's `ActivateBestChainStep` performs exactly these `DisconnectTip` and `ConnectTip` steps. ([`validation.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp))
