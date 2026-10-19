theorem kochen_specker_two_spins :
    ¬ ∃ val : M4 → ℤ, val 1 = 1 ∧ val (-1) = -1 ∧
        (∀ i, val (PM i 0 * PM i 1 * PM i 2) = val (PM i 0) * val (PM i 1) * val (PM i 2)) ∧
        (∀ j, val (PM 0 j * PM 1 j * PM 2 j) = val (PM 0 j) * val (PM 1 j) * val (PM 2 j)) := …
