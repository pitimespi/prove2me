import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSubsidy

/-!
# The money supply as a chain invariant

`GetBlockSubsidy` bounds what each coinbase may create; `CheckTxInputs` requires every other
transaction to spend at least what it creates. Together they bound the total value of the UTXO
set of every chain state reachable from the genesis by the subsidy issued so far. This file names
the quantities the theorems speak about; the rules themselves are those of the block mission
(`BitcoinBlockV2`) and the subsidy mission (`BitcoinSubsidy`).
-/

namespace BitcoinSupply

open BitcoinBlockV2

/-- The total value of the coins of a ledger. -/
def totalValue : Ledger → Int
  | [] => 0
  | e :: rest => e.2.out.nValue + totalValue rest

/-- Every coin's value lies in `[0, MAX_MONEY]`. -/
def ValuesInRange (u : Ledger) : Prop :=
  ∀ e ∈ u, 0 ≤ e.2.out.nValue ∧ e.2.out.nValue ≤ MAX_MONEY

/-- The subsidy a chain of `n` blocks (heights `0..n-1`) has issued, as `GetBlockSubsidy` sums it. -/
def issued (n : Nat) : Int := (BitcoinSubsidy.issuedBelow n : Int)

/-- The genesis subsidy: its coinbase is not in the UTXO set (`CMainParams`, `ConnectBlock`'s
genesis shortcut), so it is issued but never spendable. -/
def genesisSubsidy : Int := (BitcoinSubsidy.coreSubsidy 0 : Int)

end BitcoinSupply
