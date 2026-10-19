import Mathlib
-- Mutant 1 (FALSE): subspaces of C^2 satisfy the distributive law.
-- Lean must reject this: it finds no distributive-lattice structure on subspaces.
example : ∀ p q r : Submodule ℂ (EuclideanSpace ℂ (Fin 2)), p ⊓ (q ⊔ r) = (p ⊓ q) ⊔ (p ⊓ r) := by
  intro p q r; exact (inf_sup_left p q r)
