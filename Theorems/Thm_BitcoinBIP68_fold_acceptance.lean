import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.fold_acceptance (ctx : BitcoinBIP68.Context)
    (acc : BitcoinBIP68.Accumulator) (inputs : List BitcoinBIP68.Input) :
    BitcoinBIP68.evaluate ctx (inputs.foldl (BitcoinBIP68.coreStep ctx) acc) = true ↔
      BitcoinBIP68.evaluate ctx acc = true ∧
      ∀ input ∈ inputs, BitcoinBIP68.inputSatisfied ctx input := by sorry
