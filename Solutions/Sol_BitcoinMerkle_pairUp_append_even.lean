import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

theorem solution {H : Type} [DecidableEq H] (c : H → H → H) :
    ∀ (l r : List H), l.length % 2 = 0 → BitcoinMerkle.pairUp c (l ++ r) = BitcoinMerkle.pairUp c l ++ BitcoinMerkle.pairUp c r
  | [], r, _ => by simp [pairUp]
  | [a], r, h => by simp at h
  | a :: b :: rest, r, h => by
    simp only [List.length_cons] at h
    have h' : rest.length % 2 = 0 := by omega
    simp only [List.cons_append, pairUp, List.cons.injEq, true_and]
    exact solution c rest r h'
