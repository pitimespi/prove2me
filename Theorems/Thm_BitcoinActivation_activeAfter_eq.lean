import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.activeAfter_eq (dep : BuriedDeployment) (prevHeight : Nat) :
    BitcoinActivation.activeAfter prevHeight dep = BitcoinActivation.activeAt (prevHeight + 1) dep := by sorry
