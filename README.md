# When proof by cases fails: classical and quantum logic for spins, checked in Lean

Lecture notes and Lean 4 / Mathlib proofs for a short lecture on logic, by **Lina Alasfar**.

> Prepared with the assistance of Claude Science, Opus 5.5 model (Anthropic).

[![Lean check](https://github.com/alasfar-lina/quantum-logic-spins-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/alasfar-lina/quantum-logic-spins-lean/actions/workflows/lean.yml)

## What is in here

| Path | Content |
|---|---|
| [`notes/quantum_logic_spins.pdf`](notes/quantum_logic_spins.pdf) | The handout (11 pages). LaTeX source in `notes/`; build with `xelatex` (twice). |
| [`QuantumLogicSpins.lean`](QuantumLogicSpins.lean) | 59 theorems and lemmas. Every statement in the notes is proved here, and the notes give the Lean name next to each statement. |
| `mutants/` | Three deliberately **false** claims that Lean must reject, plus `check_mutants.sh`. Useful as a classroom exercise. |

## The story in brief

1. **Classical logic** (propositions = sets of states, as in any hidden-variable model) satisfies the distributive law and proof by cases.
2. **One spin-½** (Birkhoff–von Neumann): propositions are subspaces of ℂ², "and" is intersection, "or" is the span, and "not" is the orthogonal complement.
   - *p or not p* still holds with the span, but **not** with set union, because superpositions lie in neither part. In other words, bivalence fails.
   - The distributive law fails for S_z and S_x.
   - There is no true/false valuation and no hidden-variable embedding, and the law of total probability fails.
   - The orthomodular law survives, and so does classical reasoning between compatible propositions.
   - In MO₂ the complement is not unique, so "not" has to be supplied by orthogonality.
3. **Intuitionistic logic**, for contrast, drops *p or not p* and keeps the distributive law. Lean checks this on the three-valued Heyting algebra.
4. **Two spins** (Peres–Mermin square): no pre-assigned ±1 values exist (Kochen–Specker), while the quantum 4×4 operators satisfy every constraint.
5. **A philosophical note** relates all of this to Aristotle's laws of thought.

## Checking the proofs

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned to Lean 4.35.0 and Mathlib v4.35.0.

```bash
lake exe cache get      # download prebuilt Mathlib
lake build              # checks QuantumLogicSpins.lean (about 1 minute after the cache)
bash mutants/check_mutants.sh   # each false claim must be rejected by Lean
```

No `sorry` and no `native_decide` are used. `#print axioms` reports only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), or none at all. The same checks run on every push via GitHub Actions.

## Licence

- Lean code (`*.lean`, `lakefile.toml`, scripts): Apache License 2.0, see [`LICENSE`](LICENSE).
- Lecture notes (`notes/`): Creative Commons Attribution 4.0 International (CC BY 4.0), see [`notes/LICENSE`](notes/LICENSE).

## Citation

Lina Alasfar, *When proof by cases fails: classical and quantum logic for spins, checked in Lean*, lecture notes (2026), https://github.com/alasfar-lina/quantum-logic-spins-lean
