import Mathlib

/-
  Classical logic versus quantum logic, checked in Lean 4 + Mathlib.
  Lecture companion file to the notes notes/quantum_logic_spins.pdf.

  Author: Lina Alasfar.  Prepared with the assistance of Claude Science, Opus 5.5 model (Anthropic).
  Licence: Apache-2.0.   Build: lake exe cache get && lake build

  Part 0  Classical logic: "and" distributes over "or"; a proposition splits into
          the cases "q" and "not q".  True for every Boolean algebra, hence for every
          hidden-variable model (propositions = sets of hidden states).
  Part 0b Intuitionistic logic for contrast: drops excluded middle, keeps distributivity.
  Part 1  One spin-1/2.  Propositions are subspaces of ℂ²; "and" = intersection,
          "or" = span, "not" = orthogonal complement.  Excluded middle holds,
          but bivalence fails, and so does the distributive law for S_z and S_x.
          Consequences: no truth assignment, no hidden-variable embedding,
          the law of total probability fails.  What survives: the orthomodular law,
          and classical reasoning among compatible propositions.
  Part 1b The six spin propositions as a finite lattice (MO₂), checked by `decide`.
  Part 2  Two spins: the Peres–Mermin square.  No pre-assigned ±1 values exist
          (Kochen–Specker), yet the quantum operators satisfy every constraint.
-/

open Submodule

namespace QL

/-! ## Part 0 — classical logic -/

/-- Classical distributive law. Note: `#print axioms` shows this needs no axioms at all. -/
theorem classical_distrib (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · rintro ⟨hp, hq | hr⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

/-- Proof by cases: p is equivalent to (p and q) or (p and not q). Uses excluded middle. -/
theorem classical_case_split (p q : Prop) : p ↔ (p ∧ q) ∨ (p ∧ ¬q) := by
  constructor
  · intro hp
    by_cases hq : q
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hq⟩
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

/-- The same case split in any Boolean algebra. -/
theorem boolean_case_split {α : Type*} [BooleanAlgebra α] (p q : α) :
    p = (p ⊓ q) ⊔ (p ⊓ qᶜ) := by
  rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]

/-- Hidden-variable models: propositions are sets of hidden states, so the case split holds. -/
theorem hidden_variable_case_split {Ω : Type*} (P Q : Set Ω) : P = (P ∩ Q) ∪ (P ∩ Qᶜ) :=
  boolean_case_split P Q

/-- Classical law of total probability, for any probability (indeed any measure) on hidden states. -/
theorem classical_total_probability {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (P : Set Ω) {Q : Set Ω} (hQ : MeasurableSet Q) : μ (P ∩ Q) + μ (P ∩ Qᶜ) = μ P := by
  rw [← Set.sdiff_eq]; exact MeasureTheory.measure_inter_add_sdiff P hQ

/-! ## Part 0b — intuitionistic logic, for contrast

Intuitionistic propositions form a Heyting algebra.  The smallest instructive
example has three truth values 0 < ½ < 1 (`Fin 3`, with `1 : Fin 3` playing ½);
there "not a" is 1 if a = 0 and 0 otherwise. -/

/-- Intuitionistic logic keeps the distributive law (every Heyting algebra is distributive). -/
theorem heyting_distrib {α : Type*} [HeytingAlgebra α] (p q r : α) :
    p ⊓ (q ⊔ r) = (p ⊓ q) ⊔ (p ⊓ r) := inf_sup_left p q r

/-- Intuitionistic logic keeps non-contradiction: p and not p is false. -/
theorem intuitionistic_noncontradiction {α : Type*} [HeytingAlgebra α] (p : α) : p ⊓ pᶜ = ⊥ :=
  inf_compl_self p

lemma three_half_compl : (1 : Fin 3)ᶜ = ⊥ := ite_eq_right (by decide)
lemma three_bot_compl : (⊥ : Fin 3)ᶜ = ⊤ := ite_eq_left rfl

/-- Intuitionistic logic drops excluded middle: ½ or not ½ is ½, not 1. -/
theorem intuitionistic_lem_fails : (1 : Fin 3) ⊔ (1 : Fin 3)ᶜ ≠ ⊤ := by
  rw [three_half_compl, sup_bot_eq]; decide

/-- Intuitionistic logic drops double negation: not not ½ is 1. -/
theorem intuitionistic_dne_fails : (1 : Fin 3)ᶜᶜ ≠ (1 : Fin 3) := by
  rw [three_half_compl, three_bot_compl]; decide

/-! ## Part 1 — one spin -/

abbrev V := EuclideanSpace ℂ (Fin 2)

def zUp : V := !₂[1, 0]
def zDn : V := !₂[0, 1]
def xUp : V := !₂[1, 1]
def xDn : V := !₂[1, -1]

def Zup : Submodule ℂ V := ℂ ∙ zUp
def Zdn : Submodule ℂ V := ℂ ∙ zDn
def Xup : Submodule ℂ V := ℂ ∙ xUp
def Xdn : Submodule ℂ V := ℂ ∙ xDn

/-- Two different lines through 0 in ℂ² meet only in 0 ("u and v" is the absurd proposition). -/
lemma lines_inf {u v : V} (h : u 0 * v 1 - u 1 * v 0 ≠ 0) : (ℂ ∙ u) ⊓ (ℂ ∙ v) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, mem_span_singleton, mem_span_singleton] at hx
  obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := hx
  have h0 : b * v 0 = a * u 0 := by simpa using congrArg (fun y : V => y 0) hb
  have h1 : b * v 1 = a * u 1 := by simpa using congrArg (fun y : V => y 1) hb
  have key : a * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 0 * h1 - v 1 * h0
  have ha : a = 0 := (mul_eq_zero.mp key).resolve_right h
  simp [ha]

/-- Two different lines through 0 span all of ℂ² ("u or v" is the trivially true proposition). -/
lemma lines_sup {u v : V} (h : u 0 * v 1 - u 1 * v 0 ≠ 0) : (ℂ ∙ u) ⊔ (ℂ ∙ v) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Submodule.mem_sup]
  set d := u 0 * v 1 - u 1 * v 0
  refine ⟨((x 0 * v 1 - x 1 * v 0) / d) • u, mem_span_singleton.mpr ⟨_, rfl⟩,
          ((u 0 * x 1 - u 1 * x 0) / d) • v, mem_span_singleton.mpr ⟨_, rfl⟩, ?_⟩
  ext i
  fin_cases i <;> simp <;> field_simp <;> ring


/-- If u ⟂ v in ℂ², the orthogonal complement (quantum "not") of the line through u is the line through v. -/
lemma orth_line {u v : V} (huv : inner ℂ u v = 0) (h : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    (ℂ ∙ u)ᗮ = ℂ ∙ v := by
  have hle : (ℂ ∙ v) ≤ (ℂ ∙ u)ᗮ := by
    rw [span_singleton_le_iff_mem, mem_orthogonal_singleton_iff_inner_right]; exact huv
  calc (ℂ ∙ u)ᗮ = ((ℂ ∙ v) ⊔ (ℂ ∙ u)) ⊓ (ℂ ∙ u)ᗮ := by
          rw [sup_comm, lines_sup h, top_inf_eq]
    _ = (ℂ ∙ v) ⊔ ((ℂ ∙ u) ⊓ (ℂ ∙ u)ᗮ) := sup_inf_assoc_of_le _ hle
    _ = ℂ ∙ v := by rw [inf_orthogonal_eq_bot, sup_bot_eq]


/-- No state has both S_z = +½ and S_x = +½. -/
theorem Zup_inf_Xup : Zup ⊓ Xup = ⊥ := lines_inf (by norm_num [zUp, xUp])
/-- No state has both S_z = +½ and S_x = -½. -/
theorem Zup_inf_Xdn : Zup ⊓ Xdn = ⊥ := lines_inf (by norm_num [zUp, xDn])
theorem Zdn_inf_Xup : Zdn ⊓ Xup = ⊥ := lines_inf (by norm_num [zDn, xUp])
theorem Zdn_inf_Xdn : Zdn ⊓ Xdn = ⊥ := lines_inf (by norm_num [zDn, xDn])
/-- "S_z = +½ or S_z = -½" is always true. -/
theorem Zup_sup_Zdn : Zup ⊔ Zdn = ⊤ := lines_sup (by norm_num [zUp, zDn])
/-- "S_x = +½ or S_x = -½" is always true. -/
theorem Xup_sup_Xdn : Xup ⊔ Xdn = ⊤ := lines_sup (by norm_num [xUp, xDn])

/-- Quantum negation: not(S_z = +½) is S_z = -½. -/
theorem not_Zup : Zupᗮ = Zdn :=
  orth_line (by simp [zUp, zDn, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two])
    (by norm_num [zUp, zDn])
/-- Quantum negation: not(S_x = +½) is S_x = -½. -/
theorem not_Xup : Xupᗮ = Xdn :=
  orth_line (by simp [xUp, xDn, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two])
    (by norm_num [xUp, xDn])

/-- S_z = +½ is not the absurd proposition (the state |z+⟩ exists). -/
theorem Zup_ne_bot : Zup ≠ ⊥ := by
  rw [Zup, Ne, span_singleton_eq_bot]
  intro h
  have := congrArg (fun y : V => y 0) h
  simp [zUp] at this

/-- Excluded middle holds, bivalence fails: the state |x+⟩ satisfies
"S_z = +½ or not S_z = +½", yet it satisfies neither "S_z = +½" nor "not S_z = +½". -/
theorem excluded_middle_but_not_bivalence :
    xUp ∈ Zup ⊔ Zupᗮ ∧ xUp ∉ Zup ∧ xUp ∉ Zupᗮ := by
  refine ⟨by rw [sup_orthogonal_of_hasOrthogonalProjection]; trivial, ?_, ?_⟩
  · rw [Zup, mem_span_singleton]
    rintro ⟨a, ha⟩
    have := congrArg (fun y : V => y 1) ha
    simp [zUp, xUp] at this
  · rw [not_Zup, Zdn, mem_span_singleton]
    rintro ⟨a, ha⟩
    have := congrArg (fun y : V => y 0) ha
    simp [zDn, xUp] at this

/-- Classical "or" is SET UNION. With it, "P or not P" fails for a spin: the superposition
|x+⟩ lies neither in P = (S_z = +½) nor in Pᗮ, so the union misses it. -/
theorem union_with_orthocomplement_not_everything :
    (Zup : Set V) ∪ (Zupᗮ : Set V) ≠ Set.univ := by
  intro h
  have hx : xUp ∈ (Zup : Set V) ∪ (Zupᗮ : Set V) := h ▸ Set.mem_univ xUp
  rcases hx with hx | hx
  · exact excluded_middle_but_not_bivalence.2.1 hx
  · exact excluded_middle_but_not_bivalence.2.2 hx

/-- Von Neumann's "or" is the SPAN (join). With it, "P or not P" is the whole space, for every P. -/
theorem span_with_orthocomplement_everything (P : Submodule ℂ V) : P ⊔ Pᗮ = ⊤ :=
  sup_orthogonal_of_hasOrthogonalProjection

/-- THE KEY FACT. Left side: S_z=+½ and (S_x=+½ or S_x=-½) is S_z=+½. Right side: (S_z=+½ and S_x=+½) or (S_z=+½ and S_x=-½) is absurd. -/
theorem spin_distributivity_fails :
    Zup ⊓ (Xup ⊔ Xupᗮ) = Zup ∧ (Zup ⊓ Xup) ⊔ (Zup ⊓ Xupᗮ) = ⊥ := by
  rw [not_Xup, Xup_sup_Xdn, inf_top_eq, Zup_inf_Xup, Zup_inf_Xdn, sup_bot_eq]
  exact ⟨rfl, rfl⟩

/-- Hence the distributive law is false for spin propositions. -/
theorem subspaces_not_distributive :
    ¬ ∀ p q r : Submodule ℂ V, p ⊓ (q ⊔ r) = (p ⊓ q) ⊔ (p ⊓ r) := by
  intro h
  have := h Zup Xup Xupᗮ
  rw [spin_distributivity_fails.1, spin_distributivity_fails.2] at this
  exact Zup_ne_bot this

/-- Hence proof by cases on S_x is not valid for a spin. -/
theorem quantum_case_split_fails :
    ¬ ∀ p q : Submodule ℂ V, p = (p ⊓ q) ⊔ (p ⊓ qᗮ) := by
  intro h
  have := h Zup Xup
  rw [spin_distributivity_fails.2] at this
  exact Zup_ne_bot this

/-- No faithful translation of spin propositions into sets of hidden states that keeps "and" and "or". -/
theorem no_hidden_variable_embedding (Ω : Type*) :
    ¬ ∃ f : Submodule ℂ V → Set Ω, Function.Injective f ∧
        (∀ p q, f (p ⊓ q) = f p ∩ f q) ∧ (∀ p q, f (p ⊔ q) = f p ∪ f q) := by
  rintro ⟨f, hinj, hinf, hsup⟩
  apply subspaces_not_distributive
  intro p q r
  apply hinj
  rw [hinf, hsup, hsup, hinf, hinf, Set.inter_union_distrib_left]

/-- No assignment of true/false to all spin propositions that respects "and" and "or". -/
theorem no_truth_valuation :
    ¬ ∃ v : Submodule ℂ V → Bool, v ⊤ = true ∧ v ⊥ = false ∧
        (∀ p q, v (p ⊓ q) = (v p && v q)) ∧ (∀ p q, v (p ⊔ q) = (v p || v q)) := by
  rintro ⟨v, htop, hbot, hinf, hsup⟩
  have hz := hsup Zup Zdn
  have hx := hsup Xup Xdn
  have m1 := hinf Zup Xup
  have m2 := hinf Zup Xdn
  have m3 := hinf Zdn Xup
  have m4 := hinf Zdn Xdn
  rw [Zup_sup_Zdn, htop] at hz
  rw [Xup_sup_Xdn, htop] at hx
  rw [Zup_inf_Xup, hbot] at m1
  rw [Zup_inf_Xdn, hbot] at m2
  rw [Zdn_inf_Xup, hbot] at m3
  rw [Zdn_inf_Xdn, hbot] at m4
  revert hz hx m1 m2 m3 m4
  cases v Zup <;> cases v Zdn <;> cases v Xup <;> cases v Xdn <;> decide

/-- What quantum logic keeps: p and not p is absurd, p or not p is true, double negation, contraposition. -/
theorem quantum_ortholattice (K L : Submodule ℂ V) :
    K ⊓ Kᗮ = ⊥ ∧ K ⊔ Kᗮ = ⊤ ∧ Kᗮᗮ = K ∧ (K ≤ L → Lᗮ ≤ Kᗮ) :=
  ⟨inf_orthogonal_eq_bot K, sup_orthogonal_of_hasOrthogonalProjection,
   orthogonal_orthogonal K, orthogonal_le⟩

/-- Orthomodular law (Mathlib): if K implies L, then L = K or (not K and L). This is the weak form of distributivity that survives. -/
theorem quantum_orthomodular {K L : Submodule ℂ V} (h : K ≤ L) : K ⊔ (Kᗮ ⊓ L) = L :=
  sup_orthogonal_inf_of_hasOrthogonalProjection h

/-- Proof by cases is valid when p and q are compatible (here: p implies q, or p implies not q). -/
theorem case_split_for_compatible {p q : Submodule ℂ V} (h : p ≤ q ∨ p ≤ qᗮ) :
    p = (p ⊓ q) ⊔ (p ⊓ qᗮ) := by
  rcases h with h | h
  · have : p ⊓ qᗮ = ⊥ := eq_bot_iff.mpr
      ((inf_le_inf_right _ h).trans (inf_orthogonal_eq_bot q).le)
    rw [inf_eq_left.mpr h, this, sup_bot_eq]
  · have : p ⊓ q = ⊥ := eq_bot_iff.mpr
      ((inf_le_inf_right q h).trans (by rw [inf_comm, inf_orthogonal_eq_bot]))
    rw [inf_eq_left.mpr h, this, bot_sup_eq]

/-! ## Part 1b — the six spin propositions as a finite lattice MO₂ -/

inductive Dir | zu | zd | xu | xd
  deriving DecidableEq, Repr

inductive Q | bot | top | line (d : Dir)
  deriving DecidableEq, Repr

open Dir Q

instance : Fintype Dir := ⟨{zu, zd, xu, xd}, by intro x; cases x <;> simp⟩
instance : Fintype Q :=
  ⟨{bot, top, line zu, line zd, line xu, line xd}, by
    intro x; rcases x with _ | _ | ⟨_ | _ | _ | _⟩ <;> simp⟩

def Dir.flip : Dir → Dir | zu => zd | zd => zu | xu => xd | xd => xu

def meet : Q → Q → Q
  | bot, _ => bot
  | top, b => b
  | line _, bot => bot
  | line d, top => line d
  | line d, line e => if d = e then line d else bot

def join : Q → Q → Q
  | top, _ => top
  | bot, b => b
  | line _, top => top
  | line d, bot => line d
  | line d, line e => if d = e then line d else top

def compl : Q → Q
  | bot => top
  | top => bot
  | line d => line d.flip

def le (a b : Q) : Bool := meet a b = a

/-- Checked by enumeration: the six-element lattice is an orthocomplemented lattice. -/
theorem MO2_ortho : ∀ a : Q, meet a (compl a) = bot ∧ join a (compl a) = top ∧
    compl (compl a) = a := by decide
/-- Contraposition in MO₂. -/
theorem MO2_antitone : ∀ a b : Q, le a b → le (compl b) (compl a) := by decide
/-- Orthomodular law in MO₂ (all 36 pairs). -/
theorem MO2_orthomodular : ∀ a b : Q, le a b → join a (meet (compl a) b) = b := by decide
/-- Distributivity fails in MO₂, at the same S_z/S_x triple. -/
theorem MO2_not_distributive :
    meet (line zu) (join (line xu) (line xd)) ≠ join (meet (line zu) (line xu)) (meet (line zu) (line xd)) := by
  decide
/-- The lattice alone does not fix "not": S_z = +½ has THREE lattice complements
(meet = absurd, join = always true), and only S_z = -½ is its orthocomplement. -/
theorem MO2_complements_of_zu :
    ∀ c : Q, (meet (line zu) c = bot ∧ join (line zu) c = top) ↔
      c ∈ [line zd, line xu, line xd] := by decide

/-- Restricted to one measurement (the S_z propositions), the logic is classical. -/
theorem MO2_z_block_distributive :
    ∀ a b c : Q, a ∈ [bot, top, line zu, line zd] → b ∈ [bot, top, line zu, line zd] →
      c ∈ [bot, top, line zu, line zd] → meet a (join b c) = join (meet a b) (meet a c) := by decide

def Dir.vec : Dir → V | zu => zUp | zd => zDn | xu => xUp | xd => xDn

def sem : Q → Submodule ℂ V
  | bot => ⊥
  | top => ⊤
  | line d => ℂ ∙ d.vec

lemma det_ne {d e : Dir} (h : d ≠ e) :
    d.vec 0 * e.vec 1 - d.vec 1 * e.vec 0 ≠ 0 := by
  cases d <;> cases e <;> first | exact absurd rfl h | norm_num [Dir.vec, zUp, zDn, xUp, xDn]

/-- MO₂ is exactly the logic of the six spin subspaces: "and" matches intersection, -/
theorem sem_meet (a b : Q) : sem (meet a b) = sem a ⊓ sem b := by
  cases a <;> cases b <;> simp [meet, sem]
  rename_i d e
  by_cases h : d = e
  · subst h; simp
  · simp [h, lines_inf (det_ne h)]

/-- "or" matches span, -/
theorem sem_join (a b : Q) : sem (join a b) = sem a ⊔ sem b := by
  cases a <;> cases b <;> simp [join, sem]
  rename_i d e
  by_cases h : d = e
  · subst h; simp
  · simp [h, lines_sup (det_ne h)]

/-- and "not" matches orthogonal complement. -/
theorem sem_compl (a : Q) : sem (compl a) = (sem a)ᗮ := by
  cases a with
  | bot => simp [compl, sem]
  | top => simp [compl, sem]
  | line d =>
    cases d <;> simp only [compl, sem, Dir.flip, Dir.vec]
    · exact not_Zup.symm
    · show Zup = Zdnᗮ
      rw [← not_Zup, orthogonal_orthogonal]
    · exact not_Xup.symm
    · show Xup = Xdnᗮ
      rw [← not_Xup, orthogonal_orthogonal]

/-- A hidden-value assignment for one spin: S_z = +½ and S_x = +½ both "true". -/
def bellValue : Q → Bool
  | top => true | bot => false
  | line zu => true | line zd => false | line xu => true | line xd => false

/-- Bell's caveat for ONE spin: true/false values that respect "not" do exist ... -/
theorem bell_value_respects_negation :
    bellValue top = true ∧ ∀ a, bellValue (compl a) = !bellValue a := by decide
/-- ... but they must break "and" between S_z and S_x propositions. -/
theorem bell_value_breaks_and :
    bellValue (meet (line zu) (line xu)) ≠ (bellValue (line zu) && bellValue (line xu)) := by decide

/-- Born-rule probabilities |⟨φ|z+⟩|² for the six propositions, in the state |z+⟩. -/
def bornZup : Q → ℚ
  | bot => 0 | top => 1
  | line zu => 1 | line zd => 0 | line xu => 1/2 | line xd => 1/2

/-- Born-rule probabilities in the state |z+⟩ are a consistent probability assignment: additive on mutually exclusive propositions. -/
theorem born_is_a_state :
    bornZup top = 1 ∧ ∀ a b, le a (compl b) → bornZup (join a b) = bornZup a + bornZup b := by
  refine ⟨rfl, ?_⟩
  intro a b h
  rcases a with _ | _ | ⟨_ | _ | _ | _⟩ <;> rcases b with _ | _ | ⟨_ | _ | _ | _⟩ <;>
    simp_all [le, meet, join, compl, Dir.flip, bornZup] <;> norm_num

/-- Law of total probability fails: P(S_z=+½) = 1 but P(S_z=+½ and S_x=+½) + P(S_z=+½ and S_x=-½) = 0. -/
theorem total_probability_fails :
    bornZup (line zu) ≠ bornZup (meet (line zu) (line xu)) + bornZup (meet (line zu) (line xd)) := by
  simp [bornZup, meet]

/-- The Born value |⟨x+|z+⟩|² = ½ used in the table above. -/
theorem born_overlap :
    ‖inner ℂ ((1 / Real.sqrt 2 : ℂ) • xUp) zUp‖ ^ 2 = 1 / 2 := by
  simp [xUp, zUp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

/-! ## Part 2 — two spins: the Peres–Mermin square -/

/-- Classical: no 3×3 array of numbers has all row products +1 and column products +1, +1, -1. (Multiply all nine entries two ways.) -/
theorem classical_square_impossible (v : Fin 3 → Fin 3 → ℤ)
    (rows : ∀ i, v i 0 * v i 1 * v i 2 = 1)
    (c0 : v 0 0 * v 1 0 * v 2 0 = 1) (c1 : v 0 1 * v 1 1 * v 2 1 = 1)
    (c2 : v 0 2 * v 1 2 * v 2 2 = -1) : False := by
  have h : (1 : ℤ) = -1 :=
    calc (1 : ℤ) = (v 0 0 * v 0 1 * v 0 2) * (v 1 0 * v 1 1 * v 1 2) * (v 2 0 * v 2 1 * v 2 2) := by
            rw [rows 0, rows 1, rows 2]; norm_num
      _ = (v 0 0 * v 1 0 * v 2 0) * (v 0 1 * v 1 1 * v 2 1) * (v 0 2 * v 1 2 * v 2 2) := by ring
      _ = -1 := by rw [c0, c1, c2]; norm_num
  omega

/-- Same statement by checking all 512 sign patterns (true = -1, xor = product). -/
theorem classical_square_by_enumeration :
    ∀ a b c d e f g h k : Bool,
      ¬ ((a ^^ b ^^ c) = false ∧ (d ^^ e ^^ f) = false ∧ (g ^^ h ^^ k) = false ∧
         (a ^^ d ^^ g) = false ∧ (b ^^ e ^^ h) = false ∧ (c ^^ f ^^ k) = true) := by
  decide

open scoped Kronecker

abbrev M4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

def σx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Peres–Mermin square: nine observables of two spins (σ ⊗ σ). -/
def PM : Fin 3 → Fin 3 → M4 :=
  ![![σx ⊗ₖ 1,  1 ⊗ₖ σx,  σx ⊗ₖ σx],
    ![1 ⊗ₖ σz,  σz ⊗ₖ 1,  σz ⊗ₖ σz],
    ![σx ⊗ₖ σz, σz ⊗ₖ σx, σy ⊗ₖ σy]]

macro "matrix_check" : tactic => `(tactic|
  (ext ⟨a, b⟩ ⟨c, d⟩
   fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
   simp [PM, σx, σy, σz, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
     Matrix.one_apply, Matrix.kroneckerMap_apply] <;> ring_nf <;> simp))

/-- Each of the nine two-spin observables squares to 1, so its measured values are ±1. -/
theorem PM_square : ∀ i j, PM i j * PM i j = 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> matrix_check

set_option maxHeartbeats 4000000 in
/-- Observables in one row commute: they can be measured together. -/
theorem PM_commute_in_row : ∀ i j k, PM i j * PM i k = PM i k * PM i j := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> matrix_check

set_option maxHeartbeats 4000000 in
/-- Observables in one column commute: they can be measured together. -/
theorem PM_commute_in_col : ∀ i j k, PM j i * PM k i = PM k i * PM j i := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> matrix_check

/-- Quantum: every row multiplies to +1. -/
theorem PM_rows : ∀ i, PM i 0 * PM i 1 * PM i 2 = 1 := by
  intro i; fin_cases i <;> matrix_check

/-- Quantum: column 1 multiplies to +1. -/
theorem PM_col0 : PM 0 0 * PM 1 0 * PM 2 0 = 1 := by matrix_check
/-- Quantum: column 2 multiplies to +1. -/
theorem PM_col1 : PM 0 1 * PM 1 1 * PM 2 1 = 1 := by matrix_check
/-- Quantum: column 3 multiplies to -1. -/
theorem PM_col2 : PM 0 2 * PM 1 2 * PM 2 2 = -1 := by matrix_check

/-- Kochen–Specker for two spins: no assignment of pre-existing values that respects the product rule within every commuting row and column. -/
theorem kochen_specker_two_spins :
    ¬ ∃ val : M4 → ℤ, val 1 = 1 ∧ val (-1) = -1 ∧
        (∀ i, val (PM i 0 * PM i 1 * PM i 2) = val (PM i 0) * val (PM i 1) * val (PM i 2)) ∧
        (∀ j, val (PM 0 j * PM 1 j * PM 2 j) = val (PM 0 j) * val (PM 1 j) * val (PM 2 j)) := by
  rintro ⟨val, h1, hm1, hrow, hcol⟩
  apply classical_square_impossible (fun i j => val (PM i j))
  · intro i; rw [← hrow i, PM_rows i, h1]
  · rw [← hcol 0, PM_col0, h1]
  · rw [← hcol 1, PM_col1, h1]
  · rw [← hcol 2, PM_col2, hm1]

end QL
