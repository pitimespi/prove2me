import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinReorg

/-!
# Transaction uniqueness: BIP30 and BIP34

Two transactions with the same identifier would let a block overwrite coins that already exist,
which is what the undo data cannot restore. BIP30 forbids a block from creating a coin at an
outpoint that already has one; its scan is skipped once the BIP34 activation block is an ancestor
(until height 1,983,702), because BIP34 makes every coinbase start with a push of its height, and
a height push is never a prefix of another. This file names the quantities those two rules speak
about, so that the theorems can say exactly what validation guarantees where the scan runs and
what the height rule guarantees where it does not.
-/

namespace BitcoinUniqueness

open BitcoinSer BitcoinBlockV2

/-- The `scriptSig` of a block's coinbase (its first transaction's first input). -/
def coinbaseScriptSig (b : Block) : Bytes :=
  ((b.vtx.headD genesisCoinbase).vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig

/-- The BIP30 scan runs when `ConnectBlock` connects `b` to `S` (`fEnforceBIP30 || nHeight >=
BIP34_IMPLIES_BIP30_LIMIT`). -/
def ScanRuns (S : ChainState) (b : Block) : Prop :=
  bip30Checked S S.nextHeight (headerHash b.header) = true

/-- Freshness of a block against a ledger, over the output indices the block creates: no outpoint
of any of its transactions already holds a coin. -/
def FreshOutputs (u : Ledger) (b : Block) : Prop :=
  ∀ tx ∈ b.vtx, ∀ o, o < tx.vout.length → getCoin u ⟨txid tx, o⟩ = none

end BitcoinUniqueness
