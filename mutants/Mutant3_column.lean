import Mathlib
open scoped Kronecker
def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
-- Mutant 3 (FALSE): the third Peres-Mermin column multiplies to +1 (it is -1).
-- Lean must reject this: the matrix check fails.
example : (σx ⊗ₖ σx) * (σz ⊗ₖ σz) * (σy ⊗ₖ σy) = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
   simp [σx, σy, σz, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
     Matrix.one_apply, Matrix.kroneckerMap_apply] <;> ring_nf <;> simp
