import Definitions.Def_BitcoinActivation

open BitcoinActivation

theorem solution (dep : BuriedDeployment) (prevHeight : Nat) :
    BitcoinActivation.activeAfter prevHeight dep = BitcoinActivation.activeAt (prevHeight + 1) dep := rfl
