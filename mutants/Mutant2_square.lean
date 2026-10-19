import Mathlib
-- Mutant 2 (FALSE): the square with ALL column products +1 is impossible.
-- Lean must reject this: `decide` finds the all-(+1) array as a counterexample.
example : ∀ a b c d e f g h k : Bool,
      ¬ ((a ^^ b ^^ c) = false ∧ (d ^^ e ^^ f) = false ∧ (g ^^ h ^^ k) = false ∧
         (a ^^ d ^^ g) = false ∧ (b ^^ e ^^ h) = false ∧ (c ^^ f ^^ k) = false) := by
  decide
