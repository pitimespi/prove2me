SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, "
       "Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, "
       "src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; "
       "CCoinsViewCache (coins.cpp)")
TAGS = ["bitcoin", "consensus", "reorganization", "reorg", "undo", "utxo", "chainstate", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinReorg",
    "definition_title": "Chains of blocks connected and disconnected: state equivalence, connectChain, disconnectChain, the freshness conditions, consistency",
    "natural_language_statement": r"""Six names over the block mission's `BitcoinBlockV2`; nothing is re-transcribed.

**`StateEquiv S T`** — two chain states with the same header list whose ledgers hold the same coin at every outpoint (`getCoin` agrees everywhere; the association lists may differ in order).

**`connectChain S bs`** — connect the blocks of `bs` in order, each with its own clock reading, through the block mission's `validate`; `none` if any block is not accepted, else the final state and the list of the blocks' undo data (`CBlockUndo` of each, in connection order).

**`disconnectTip S b undo`** — `DisconnectBlock` on `S.utxo` at the tip's height with `b`'s hash and undo data, then the tip header popped; `none` is `DISCONNECT_FAILED`, the flag is `DISCONNECT_OK` (clean) versus `DISCONNECT_UNCLEAN`.

**`disconnectChain S l`** — `disconnectTip` for each (block, undo) pair of `l` in the order given (the tip first), the flags conjoined.

**`FreshChain S bs`** — the side conditions under which undo data restores a ledger exactly, continued along the states each accepted block produces: the txids within each block are distinct, no txid of the block already has a coin in the ledger it is connected to (the BIP30 condition, which `ConnectBlock` enforces only where its scan runs), and the block does not hash to the genesis hash.

**`Consistent S`** — `S` is `StateEquiv` to some state reachable from the genesis.

**Formalization Note.** `validate`, `disconnectBlock`, `Reachable`, `Equiv`, `updateCoins`, `connectBlock` are the block mission's. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinReorg.updateCoins_equiv": dict(title="UpdateCoins respects ledger equivalence",
    nl=r"""If two ledgers hold the same coin at every outpoint, so do the ledgers `UpdateCoins` produces from them for the same transaction and height.""",
    ms=("UpdateCoins reads the ledger only through getCoin", "The exact characterizations of `getCoin` after `spendInputs` and `addCoinsFrom`.")),
"BitcoinReorg.connectBlock_equiv": dict(title="ConnectBlock respects ledger equivalence",
    nl=r"""For two states with the same headers and equivalent ledgers, `connectBlock` on the same block either fails on both or succeeds on both with equivalent ledgers and the same undo data. Every ledger read of the transaction loop — `CheckTxInputs`, `SequenceLocks`, the sigop cost, `CheckInputScripts`, the undo record, the BIP30 scan — goes through `getCoin`.""",
    ms=("The ConnectBlock loop on equivalent ledgers", "Induction over the transactions: the step decisions coincide and `UpdateCoins` keeps the ledgers equivalent.")),
"BitcoinReorg.validate_equiv": dict(title="validate respects state equivalence",
    nl=r"""For `StateEquiv S T` and any block and clock reading, `validate` gives the same outcome on both (`invalid`, `futureTime`, `missingPrev`), or accepts both with `StateEquiv` results and the same undo data. The header path and `ContextualCheckBlock` read only the headers.""",
    ms=("The header path does not read the ledger", "`AcceptBlockHeader` and `ContextualCheckBlock` depend on the state only through its header list.")),
"BitcoinReorg.disconnect_connect_equiv": dict(title="Disconnect undoes connect, from any equivalent ledger",
    nl=r"""The block mission's `disconnect_connect` for any ledger with the same coins as the accepted state's: under its hypotheses (well-formed state, distinct and fresh txids, not the genesis hash), `disconnectBlock` on that ledger with the recorded undo data succeeds cleanly and yields a ledger equivalent to the state before the block.""",
    ms=("One block, up to ledger order", "The block mission's proof, with the final ledger generalized.")),
"BitcoinReorg.connectChain_reachable": dict(title="Every state along a connected chain is reachable",
    nl=r"""If `S` is reachable and `connectChain S bs = some (T, undos)`, then `T` is reachable: `connectChain` is iterated `validate`, and `Reachable` is closed under accepted blocks.""",
    ms=None),
"BitcoinReorg.connectChain_equiv": dict(title="connectChain respects state equivalence",
    nl=r"""Connecting the same chain to two `StateEquiv` states either fails on both or succeeds on both with `StateEquiv` results and the same undo data.""",
    ms=("Chains on equivalent states", "Induction over the chain with `validate_equiv`.")),
"BitcoinReorg.disconnectChain_connectChain": dict(title="Multi-block undo: a connected chain is disconnected back to its starting state",
    nl=r"""For a reachable `S`, a chain `bs` satisfying `FreshChain S bs`, and `connectChain S bs = some (T, undos)`: disconnecting from `T` the blocks of `bs` with their undo data, tip first, succeeds with every disconnect clean and yields a state `StateEquiv` to `S`. The undo data recorded over any number of blocks restores the chain state exactly, up to ledger order.""",
    ms=("Multi-block undo", "Induction over the chain: the tail is undone first by the induction hypothesis, then the first block by `disconnect_connect_equiv` from the equivalent ledger; the popped header is the appended one.")),
"BitcoinReorg.consistent_connectChain": dict(title="Connecting a chain to a consistent state gives a consistent state",
    nl=r"""If `S` is `StateEquiv` to a reachable state and `connectChain S cs` succeeds, the result is `StateEquiv` to a reachable state.""",
    ms=("Consistency is closed under connection", "`connectChain_equiv` and `connectChain_reachable`.")),
"BitcoinReorg.reorg_safety": dict(title="Reorganization safety: disconnect then connect yields a reachable state, up to ledger order",
    nl=r"""Let `S` be reachable, `bs` a chain with `FreshChain S bs` connected to `S` giving `T` with undo data `undos`; let the blocks of `bs` be disconnected from `T` with that undo data (tip first) giving `S'` with flag `clean`; and let any chain `cs` be connected to `S'` giving `U` with undo data `undos'`. Then `clean = true`, and connecting `cs` directly to `S` succeeds with the same undo data `undos'` and a state `U₀` such that `StateEquiv U U₀` and `U₀` is reachable from the genesis. The UTXO set a node holds after any reorganization is, up to the order of its ledger, the one it would hold had it validated the new branch directly: the state is a function of the chain, not of the path taken to it.""",
    ms=None),
}
ORDER = ["BitcoinReorg.updateCoins_equiv", "BitcoinReorg.connectBlock_equiv", "BitcoinReorg.validate_equiv",
         "BitcoinReorg.disconnect_connect_equiv", "BitcoinReorg.connectChain_reachable", "BitcoinReorg.connectChain_equiv",
         "BitcoinReorg.disconnectChain_connectChain", "BitcoinReorg.consistent_connectChain", "BitcoinReorg.reorg_safety"]
