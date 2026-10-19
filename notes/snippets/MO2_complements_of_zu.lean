theorem MO2_complements_of_zu :
    ∀ c : Q, (meet (line zu) c = bot ∧ join (line zu) c = top) ↔
      c ∈ [line zd, line xu, line xd] := by decide
