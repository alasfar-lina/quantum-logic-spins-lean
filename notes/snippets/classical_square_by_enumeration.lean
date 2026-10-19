theorem classical_square_by_enumeration :
    ∀ a b c d e f g h k : Bool,
      ¬ ((a ^^ b ^^ c) = false ∧ (d ^^ e ^^ f) = false ∧ (g ^^ h ^^ k) = false ∧
         (a ^^ d ^^ g) = false ∧ (b ^^ e ^^ h) = false ∧ (c ^^ f ^^ k) = true) := by
  decide
