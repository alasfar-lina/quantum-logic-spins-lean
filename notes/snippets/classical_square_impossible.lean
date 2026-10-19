theorem classical_square_impossible (v : Fin 3 → Fin 3 → ℤ)
    (rows : ∀ i, v i 0 * v i 1 * v i 2 = 1)
    (c0 : v 0 0 * v 1 0 * v 2 0 = 1) (c1 : v 0 1 * v 1 1 * v 2 1 = 1)
    (c2 : v 0 2 * v 1 2 * v 2 2 = -1) : False := …
