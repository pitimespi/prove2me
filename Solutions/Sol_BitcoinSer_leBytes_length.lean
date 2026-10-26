import Definitions.Def_BitcoinSer

open BitcoinSer

theorem solution (k n : Nat) : (BitcoinSer.leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]
