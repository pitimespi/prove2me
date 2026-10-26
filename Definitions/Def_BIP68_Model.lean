import Std

namespace BitcoinBIP68

structure Input where
  sequence : BitVec 32
  coinHeight : Nat
  deriving Repr, DecidableEq

structure Context where
  height : Nat
  mtp : Nat → Nat

def int32Max : Nat := 2147483647
def int64Max : Nat := 9223372036854775807

def specEnabled (version flags : BitVec 32) : Prop :=
  2 ≤ version.toNat ∧ flags.toNat % 2 = 1

def specDisabled (sequence : BitVec 32) : Prop :=
  sequence.toNat / 2147483648 = 1

def specTimeBased (sequence : BitVec 32) : Prop :=
  (sequence.toNat / 4194304) % 2 = 1

def specDelay (sequence : BitVec 32) : Nat :=
  sequence.toNat % 65536

instance (version flags : BitVec 32) : Decidable (specEnabled version flags) :=
  inferInstanceAs (Decidable (2 ≤ version.toNat ∧ flags.toNat % 2 = 1))

instance (sequence : BitVec 32) : Decidable (specDisabled sequence) :=
  inferInstanceAs (Decidable (sequence.toNat / 2147483648 = 1))

instance (sequence : BitVec 32) : Decidable (specTimeBased sequence) :=
  inferInstanceAs (Decidable ((sequence.toNat / 4194304) % 2 = 1))

def inputSatisfied (ctx : Context) (input : Input) : Prop :=
  specDisabled input.sequence ∨
    if specTimeBased input.sequence then
      ctx.mtp (input.coinHeight - 1) + 512 * specDelay input.sequence ≤
        ctx.mtp (ctx.height - 1)
    else
      input.coinHeight + specDelay input.sequence ≤ ctx.height

def satisfiesBIP68 (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Prop :=
  ¬ specEnabled version flags ∨ ∀ input ∈ inputs, inputSatisfied ctx input

def expectedHeights (version flags : BitVec 32) (inputs : List Input) : List Nat :=
  inputs.map fun input =>
    if specEnabled version flags ∧ specDisabled input.sequence then 0
    else input.coinHeight

def admissible (ctx : Context) (inputs : List Input) : Prop :=
  0 < ctx.height ∧ ctx.height ≤ int32Max ∧
  (∀ h, h ≤ ctx.height → ctx.mtp h ≤ int64Max) ∧
  ∀ input ∈ inputs, input.coinHeight ≤ ctx.height

def noOverflow (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Prop :=
  ∀ input ∈ inputs, specEnabled version flags → ¬ specDisabled input.sequence →
    if specTimeBased input.sequence then
      ctx.mtp (input.coinHeight - 1) + 512 * specDelay input.sequence ≤ int64Max
    else
      input.coinHeight + specDelay input.sequence ≤ int32Max

end BitcoinBIP68
