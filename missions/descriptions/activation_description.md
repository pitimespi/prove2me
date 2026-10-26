## Why rule activation is part of consensus

Bitcoin's consensus rules are not a single ruleset but a history of them. Each soft fork — P2SH, strict DER signatures (BIP66), `CHECKLOCKTIMEVERIFY` (BIP65), sequence locks (BIP68/112/113), SegWit with `NULLDUMMY` (BIP141/147), Taproot — began enforcing at a particular block height, and a node validating the chain from genesis must apply to each block exactly the rules in force at its height. Bitcoin Core implements this with **buried deployments**: fixed activation heights in `CMainParams`, consulted by `DeploymentActiveAt`, and a function `GetBlockScriptFlags` that assembles the script-verification flags for a block. Two historical blocks are special-cased by hash: one that violated P2SH before the rule was enforced, and one that violated Taproot rules before activation; for these the flag set is replaced. ([`GetBlockScriptFlags`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249), [`deploymentstatus.h`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/deploymentstatus.h), [`CMainParams`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp))

A whole-chain correctness statement needs this table to be exact: which rules apply at which height, and precisely how the two exceptions deviate. This mission transcribes it and proves its structural properties: rules are only ever added as height increases, in a fixed order, and the exceptions only ever remove rules.

## Deployments, heights, and flags

A **buried deployment** is one of `HEIGHTINCB` (BIP34), `CLTV` (BIP65), `DERSIG` (BIP66), `CSV`, `SEGWIT`, with mainnet heights $227{,}931$, $388{,}381$, $363{,}725$, $419{,}328$, $481{,}824$. It is **active at** a block when the block's height is at least that height, and **active after** a previous block when the previous height plus one is.

A **flag set** records which of `P2SH`, `WITNESS`, `TAPROOT`, `DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY`, `NULLDUMMY` are enforced. The **base** is `P2SH | WITNESS | TAPROOT` for an ordinary block, `NONE` for the BIP16 exception block, and `P2SH | WITNESS` for the Taproot exception block. `GetBlockScriptFlags` adds `DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY` and `NULLDUMMY` to the base when `DERSIG`, `CLTV`, `CSV` and `SEGWIT` respectively are active at the block's height. Flag sets are compared by **inclusion**: every rule enforced by the first is enforced by the second. Separately, `ConnectBlock` sets `LOCKTIME_VERIFY_SEQUENCE` for BIP68 exactly when `CSV` is active.

## Formalization targets

### Goal — soft forks only add rules
$$
h_1 \le h_2 \;\Longrightarrow\; \mathrm{blockScriptFlags}(h_1) \subseteq \mathrm{blockScriptFlags}(h_2)
$$
for ordinary (non-exception) blocks. This is `BitcoinActivation.flags_mono`: at no height is a script rule enforced that a later height would not enforce. It is the weakest statement that makes "the rules in force at height $h$" a well-ordered notion.

### Supporting milestones
1. **Activation is monotone** (`activeAt_mono`); **after is at of the next height** (`activeAfter_eq`).
2. **Before BIP66** (`flags_before_bip66`): only the base `P2SH | WITNESS | TAPROOT`.
3. **From SegWit on** (`flags_after_segwit`): every flag.
4. **Order of activation** (`flags_order`): `CHECKLOCKTIMEVERIFY` implies `DERSIG`, `CHECKSEQUENCEVERIFY` implies `CHECKLOCKTIMEVERIFY`, `NULLDUMMY` implies `CHECKSEQUENCEVERIFY`.
5. **The BIP16 exception** (`bip16_exception`): no flags at all at its height (170,060, before BIP66).
6. **The Taproot exception** (`taproot_exception`): every flag except `TAPROOT` at its height (692,261, after SegWit).
7. **Exceptions only remove** (`exception_le`): at any height, an exception's flags are included in the default's.
8. **Sequence-lock flag** (`lockTimeFlags_eq`): `LOCKTIME_VERIFY_SEQUENCE` exactly from height $419{,}328$.

## What the result establishes

The goal and milestones pin down, as kernel-checked facts, the exact ruleset function of the pinned implementation: which script rules apply at every mainnet height, that the function is monotone and that its four height-dependent rules switch on in a fixed order, and that the two hash-keyed exceptions are the only departures and only ever relax. For the whole-consensus development this is the "historical rule selection" input: a block at height $h$ is validated against $\mathrm{blockScriptFlags}(h)$, and these theorems are what a composition proof cites when it reasons about rules across heights.

Status: all statements are open with intentional placeholder proofs. The exception blocks are identified by their hashes in the source; the model names them and states their flags at any height in the relevant range, so no claim about a specific hash is made.

## Where the obvious argument fails

There is little depth here by design; the point is exactness. The trap is the exceptions: `P2SH`, `WITNESS` and `TAPROOT` are not height-gated at all in the pinned source (they are "always on except for the two violating blocks"), so a formalization that gates them by their historical activation heights would be wrong for the pinned revision. Likewise the height-dependent flags are OR-ed onto the exception's base, so the Taproot exception block does enforce `DERSIG`, `CLTV`, `CSV` and `NULLDUMMY`.

## Formalization scope

Heights are `Nat`; flag sets are a structure of seven Booleans; inclusion is pointwise implication. Versionbits deployments (`DEPLOYMENT_TESTDUMMY`, the historical Taproot signalling) are not modeled, since the pinned source consults no versionbits state for mainnet consensus flags. The exception table is modeled as a three-valued classification of a block rather than a hash lookup; the hash-to-block correspondence is a serialization matter.

A trivializing formalization would define the flags directly as a monotone function of height, dropping the exceptions; the definition follows the source's base-then-OR structure with the exception table.

No Mathlib is required; the development imports only `Std`.

## Selected references

- Bitcoin Core contributors. *`GetBlockScriptFlags`*, `src/validation.cpp` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, lines 2249–2288. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249)
- Bitcoin Core contributors. *`DeploymentActiveAt`, `DeploymentActiveAfter`*, `src/deploymentstatus.h`; *`BuriedDeployment`, `DeploymentHeight`*, `src/consensus/params.h`; *`CMainParams`*, `src/kernel/chainparams.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp)
- Bitcoin Core contributors. *`LOCKTIME_VERIFY_SEQUENCE`*, `src/consensus/consensus.h`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/consensus.h)
- Bitcoin Improvement Proposals 16, 34, 65, 66, 68, 112, 113, 141, 147, 341, 342, collection at revision `100ba872c808946155b1eeb8c4568058f2eea0a7`. [Collection](https://github.com/bitcoin/bips/tree/100ba872c808946155b1eeb8c4568058f2eea0a7)
