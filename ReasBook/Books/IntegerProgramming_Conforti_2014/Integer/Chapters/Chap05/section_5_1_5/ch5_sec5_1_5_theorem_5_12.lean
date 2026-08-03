import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped Matrix
open scoped SplitHullNotation

-- Domain-style sampling for this refine pass:
-- * source-facing owners kept here: `is_mixed_integer_rounding_inequality`,
--   `mixed_integer_rounding_closure`
-- * core/canonical split owners reused from Chapter 5.1:
--   `Split`, `split_hull`, `splitClosure`, `polyhedron_le_set`
-- * bridge/view kept here: `mixed_split_closure`; on matrix polyhedra it is
--   identified with the Chapter 5 matrix owner `splitClosure`

section Theorem512

variable {m n : ℕ}

/-- An inequality `a x ≤ δ` is a mixed integer rounding inequality for `P` relative to the
integer-coordinate set `I` if it comes from the variable-aggregation MIR construction. -/
def is_mixed_integer_rounding_inequality
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ))
    (a : Fin n → ℝ)
    (δ : ℝ) : Prop :=
  ∃ π : Fin n → ℤ, ∃ c : Fin n → ℝ, ∃ γ β : ℝ,
    (∀ j : Fin n, j ∉ I → π j = 0) ∧
    (∀ x : Fin n → ℝ, x ∈ P →
      (fun i : Fin n ↦ (π i : ℝ)) ⬝ᵥ x - (γ - c ⬝ᵥ x) ≤ β) ∧
    (∀ x : Fin n → ℝ, x ∈ P → c ⬝ᵥ x ≤ γ) ∧
    a = (fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)) ∧
    δ = (⌊β⌋ : ℝ) + γ / (1 - Int.fract β)

/-- The mixed integer rounding closure `P^MIR[I]` of `P` is the set of points of `P`
satisfying every mixed integer rounding inequality supported on `I`. -/
def mixed_integer_rounding_closure
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  P ∩ {x : Fin n → ℝ |
    ∀ a : Fin n → ℝ, ∀ δ : ℝ,
      is_mixed_integer_rounding_inequality I P a δ → a ⬝ᵥ x ≤ δ}

/-- The mixed split closure `P^split[I]` of `P` is the intersection of the Chapter 5 split hulls
`P^(π, π₀)` over all splits supported on `I`. This is a `bridge/view` construction
built directly from the existing owners `Split` and `split_hull`. -/
def mixed_split_closure
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  ⋂ s : Split I.toFinite.toFinset, P^(s, s.π0)

namespace IndexedMixedClosureNotation

/-- Textbook notation for the mixed integer rounding closure relative to the integer-coordinate
set `I`. -/
scoped notation:max P "^MIR[" I "]" => mixed_integer_rounding_closure I P

/-- Textbook notation for the mixed split closure relative to the integer-coordinate set `I`. -/
scoped notation:max P "^split[" I "]" => mixed_split_closure I P

end IndexedMixedClosureNotation

open scoped IndexedMixedClosureNotation

/-- Membership in `P^MIR[I]` means belonging to `P` and satisfying every mixed integer rounding
inequality for `P` relative to `I`. -/
@[simp] theorem mem_mixed_integer_rounding_closure_iff
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ P^MIR[I] ↔
      x ∈ P ∧
        ∀ a : Fin n → ℝ, ∀ δ : ℝ,
          is_mixed_integer_rounding_inequality I P a δ → a ⬝ᵥ x ≤ δ :=
  Iff.rfl

/-- Membership in `P^split[I]` means belonging to every split hull `P^(π, π₀)`
whose integral split data is supported on `I`. -/
@[simp] theorem mem_mixed_split_closure_iff
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ P^split[I] ↔
      ∀ s : Split I.toFinite.toFinset, x ∈ P^(s, s.π0) := by
  simp [mixed_split_closure]

/-- On the matrix polyhedron `polyhedron_le_set A b`, the source-facing set-level mixed split
closure agrees with the canonical Chapter 5 split-closure owner
`splitClosure A b I.toFinite.toFinset`. -/
theorem mixed_split_closure_polyhedron_le_set_eq_splitClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    (polyhedron_le_set A b)^split[I] =
      splitClosure A b I.toFinite.toFinset := by
  ext x
  simp [mixed_split_closure, splitClosure, split_polyhedron]

/-- Membership in the source-facing mixed split closure of `polyhedron_le_set A b` is
equivalently membership in the canonical Chapter 5 split closure. -/
theorem mem_mixed_split_closure_polyhedron_le_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n))
    (x : Fin n → ℝ) :
    x ∈ (polyhedron_le_set A b)^split[I] ↔
      x ∈ splitClosure A b I.toFinite.toFinset := by
  simp [mixed_split_closure_polyhedron_le_set_eq_splitClosure A b I]

/-- Theorem 5.12. For the polyhedron `P = {x ∈ ℝ^n | A x ≤ b}`, the mixed integer rounding
closure `(P)^MIR[I]` equals the canonical Chapter 5 split closure relative to the same
integer-coordinate set `I`. -/
theorem mixed_integer_rounding_closure_eq_splitClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    (polyhedron_le_set A b)^MIR[I] =
      splitClosure A b I.toFinite.toFinset := sorry

/-- Theorem 5.12 in the source-facing closure notation `P^MIR[I] = P^split[I]`. -/
theorem mixed_integer_rounding_closure_eq_mixed_split_closure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    (polyhedron_le_set A b)^MIR[I] =
      (polyhedron_le_set A b)^split[I] := by
  simpa [mixed_split_closure_polyhedron_le_set_eq_splitClosure A b I] using
    mixed_integer_rounding_closure_eq_splitClosure A b I

end Theorem512
