import Definitions.Def_BIP68_Model

namespace BitcoinBIP68

def coreEnabled (version flags : BitVec 32) : Bool :=
  decide (2 ≤ version.toNat) && ((flags &&& 1) != 0)

def coreDisabled (sequence : BitVec 32) : Bool :=
  (sequence &&& 0x80000000) != 0

def coreTimeBased (sequence : BitVec 32) : Bool :=
  (sequence &&& 0x00400000) != 0

def coreDelay (sequence : BitVec 32) : Nat :=
  (sequence &&& 0x0000ffff).toNat

def coreSeconds (sequence : BitVec 32) : Nat :=
  ((sequence &&& 0x0000ffff) <<< 9).toNat

structure Accumulator where
  minHeight : Int
  minTime : Int
  heightsRev : List Nat
  deriving Repr, DecidableEq

def initial : Accumulator := ⟨-1, -1, []⟩

def coreStep (ctx : Context) (acc : Accumulator) (input : Input) : Accumulator :=
  if coreDisabled input.sequence then
    { acc with heightsRev := 0 :: acc.heightsRev }
  else if coreTimeBased input.sequence then
    { acc with
      minTime := max acc.minTime
        ((ctx.mtp (input.coinHeight - 1) : Int) + (coreSeconds input.sequence : Int) - 1)
      heightsRev := input.coinHeight :: acc.heightsRev }
  else
    { acc with
      minHeight := max acc.minHeight
        ((input.coinHeight : Int) + (coreDelay input.sequence : Int) - 1)
      heightsRev := input.coinHeight :: acc.heightsRev }

def calculate (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Accumulator :=
  if coreEnabled version flags then inputs.foldl (coreStep ctx) initial
  else { initial with heightsRev := (inputs.map Input.coinHeight).reverse }

def returnedHeights (acc : Accumulator) : List Nat := acc.heightsRev.reverse

def evaluate (ctx : Context) (acc : Accumulator) : Bool :=
  decide (acc.minHeight < (ctx.height : Int) ∧
    acc.minTime < (ctx.mtp (ctx.height - 1) : Int))

def sequenceLocks (version flags : BitVec 32) (ctx : Context)
    (inputs : List Input) : Bool :=
  evaluate ctx (calculate version flags ctx inputs)

end BitcoinBIP68
