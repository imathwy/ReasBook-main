import BauschkeLean.Chap22.Definition_22_1

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: `IsUniformlyMonotoneOnWith` and `IsUniformlyMonotoneOn` record the textbook
  localized notion on a subset `C`.
- `core/canonical`: `SetValuedOperator.IsUniformlyMonotone` from Definition 22.1 is the chapter
  owner for the whole-space notion with a fixed modulus.
- `bridge/view`: the final two theorems restrict a global uniformly monotone operator to a subset
  of its domain.

This keeps the localized notion as the source-facing owner instead of duplicating the global owner,
while still deriving the subset API from the existing Chapter 22 owner where possible. -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A localized uniform monotonicity witness on `C` with explicit modulus `φ`. -/
def IsUniformlyMonotoneOnWith
    (A : SetValuedOperator H H) (C : Set H) (φ : NNReal → EReal) : Prop :=
  C ⊆ A.dom ∧
    Monotone φ ∧
    (∀ r : NNReal, φ r = 0 ↔ r = 0) ∧
    ∀ ⦃x u y v : H⦄, x ∈ C → y ∈ C → u ∈ A x → v ∈ A y →
      φ ‖x - y‖₊ ≤ (⟪x - y, u - v⟫_ℝ : EReal)

variable {A : SetValuedOperator H H} {C : Set H} {φ : NNReal → EReal}

/-- A localized uniform monotonicity witness is only defined on a subset of `A.dom`. -/
theorem IsUniformlyMonotoneOnWith.subset_dom
    (hA : A.IsUniformlyMonotoneOnWith C φ) :
    C ⊆ A.dom :=
  hA.1

/-- The localized modulus of a uniformly monotone-on witness is monotone. -/
theorem IsUniformlyMonotoneOnWith.monotone
    (hA : A.IsUniformlyMonotoneOnWith C φ) :
    Monotone φ :=
  hA.2.1

/-- The localized modulus vanishes exactly at `0`. -/
theorem IsUniformlyMonotoneOnWith.modulus_eq_zero_iff
    (hA : A.IsUniformlyMonotoneOnWith C φ) (r : NNReal) :
    φ r = 0 ↔ r = 0 :=
  hA.2.2.1 r

/-- A localized uniform monotonicity witness lower-bounds the monotonicity pairing on `C`. -/
theorem IsUniformlyMonotoneOnWith.ineq
    (hA : A.IsUniformlyMonotoneOnWith C φ)
    {x u y v : H} (hx : x ∈ C) (hy : y ∈ C) (hu : u ∈ A x) (hv : v ∈ A y) :
    φ ‖x - y‖₊ ≤ (⟪x - y, u - v⟫_ℝ : EReal) :=
  hA.2.2.2 hx hy hu hv

/-- Remark 22.3: `A` is uniformly monotone on `C` when `C ⊆ A.dom` and there exists an
increasing modulus `φ : NNReal → EReal`, vanishing only at `0`, such that
`φ ‖x - y‖₊ ≤ (⟪x - y, u - v⟫_ℝ : EReal)` for all `x, y ∈ C`, `u ∈ A x`, and `v ∈ A y`. -/
def IsUniformlyMonotoneOn (A : SetValuedOperator H H) (C : Set H) : Prop :=
  ∃ φ : NNReal → EReal, A.IsUniformlyMonotoneOnWith C φ

/-- Uniform monotonicity on `C` forces `C ⊆ A.dom`. -/
theorem IsUniformlyMonotoneOn.subset_dom
    (hA : A.IsUniformlyMonotoneOn C) :
    C ⊆ A.dom := by
  rcases hA with ⟨φ, hφ⟩
  exact hφ.subset_dom

/-- A global uniform monotonicity modulus restricts to any subset of `A.dom`. -/
theorem IsUniformlyMonotone.uniformlyMonotoneOnWith
    (hA : A.IsUniformlyMonotone φ) (hC : C ⊆ A.dom) :
    A.IsUniformlyMonotoneOnWith C φ := by
  refine ⟨hC, hA.modulusMonotone, hA.modulus_eq_zero_iff, ?_⟩
  intro x u y v hx hy hu hv
  exact hA.ineq hu hv

/-- A globally uniformly monotone operator is uniformly monotone on every subset of `A.dom`. -/
theorem IsUniformlyMonotone.uniformlyMonotoneOn
    (hA : A.IsUniformlyMonotone φ) (hC : C ⊆ A.dom) :
    A.IsUniformlyMonotoneOn C :=
  ⟨φ, hA.uniformlyMonotoneOnWith hC⟩

end SetValuedOperator
