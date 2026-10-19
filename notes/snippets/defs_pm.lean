def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Peres–Mermin square: nine observables of two spins (σ ⊗ σ). -/
def PM : Fin 3 → Fin 3 → M4 :=
  ![![σx ⊗ₖ 1,  1 ⊗ₖ σx,  σx ⊗ₖ σx],
    ![1 ⊗ₖ σz,  σz ⊗ₖ 1,  σz ⊗ₖ σz],
    ![σx ⊗ₖ σz, σz ⊗ₖ σx, σy ⊗ₖ σy]]
