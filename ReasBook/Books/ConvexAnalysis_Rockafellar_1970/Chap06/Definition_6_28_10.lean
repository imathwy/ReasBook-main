import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_16_0_4

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.10 introduces the simplex-constrained separable minimization
  problem with objective `q₁(ξ₁) + ⋯ + qₙ(ξₙ)` and constraints `ξ ≥ 0`, `∑ ξᵢ = 1`.
- `core/canonical`: the owner abstractions are mathlib's feasible set `stdSimplex 𝕜 ι`,
  the project's coordinate-sum owner `separableCoordinateSum`, and mathlib's extrema owner
  `IsMinOn` on the ambient feasible set `stdSimplex 𝕜 ι`.
- `bridge/view`: the source optimization problem is owned by the minimizer predicate
  `IsStdSimplexSeparableMinimizer q x`; the minimizer set
  `stdSimplexSeparableMinimumSet q` is the derived set-level view.

Domain-style sampling used here:
- `stdSimplex` from mathlib's simplex API;
- `separableCoordinateSum` from `Chap03.Text_16_0_4`;
- `separableCoordinateSum_apply` from the same owner file;
- `isMinOn_iff` from mathlib's extrema API.

Primitive data vs derived API:
- primitive source data: the family of scalar functions `q : ι → 𝕜 → α`;
- primitive owners: the ambient feasible-owner predicate
  `IsStdSimplexSeparableMinimizer q x`, plus the intrinsic objective owner
  `stdSimplexSeparableObjective q : stdSimplex 𝕜 ι → α` as a bridge view;
- derived API: the minimizer set `stdSimplexSeparableMinimumSet q` and the textbook
  sum-inequality criterion.

Layer target: `bridge/view`, centered on the canonical ambient feasible-owner layer:
`x ∈ stdSimplex 𝕜 ι ∧ IsMinOn (separableCoordinateSum q) (stdSimplex 𝕜 ι) x`,
with a bridge to the intrinsic subtype objective owner.
-/

open scoped BigOperators

universe u v

section

variable {𝕜 : Type u} {α : Type v} {ι : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [Fintype ι]
variable [AddCommMonoid α]

variable (q : ι → 𝕜 → α)

/-- The separable objective `ξ ↦ ∑ i, qᵢ(ξᵢ)` restricted to the intrinsic feasible owner
`stdSimplex 𝕜 ι`. -/
def stdSimplexSeparableObjective (q : ι → 𝕜 → α) : stdSimplex 𝕜 ι → α :=
  fun ξ ↦ separableCoordinateSum q ξ

@[simp] theorem stdSimplexSeparableObjective_apply
    (ξ : stdSimplex 𝕜 ι) :
    stdSimplexSeparableObjective q ξ = ∑ i, q i (ξ i) :=
  rfl

variable [Preorder α]
variable (x : ι → 𝕜)

/-- Definition 6.28.10: `x` solves the simplex-constrained separable minimization problem
for the coordinate family `q` exactly when `x` is feasible for the canonical simplex owner and
minimizes the canonical separable objective owner on that feasible set. The owner is index-generic
over a finite type `ι`; the textbook `n`-coordinate form is the specialization `ι = Fin n`. -/
def IsStdSimplexSeparableMinimizer : Prop :=
  x ∈ stdSimplex 𝕜 ι ∧
    IsMinOn (separableCoordinateSum q) (stdSimplex 𝕜 ι) x

/-- Set-level view of Definition 6.28.10: all simplex-feasible minimizers of the separable
objective with coordinate family `q`. -/
def stdSimplexSeparableMinimumSet : Set (ι → 𝕜) :=
  {x | IsStdSimplexSeparableMinimizer q x}

namespace IsStdSimplexSeparableMinimizer

theorem iff :
    IsStdSimplexSeparableMinimizer q x ↔
      x ∈ stdSimplex 𝕜 ι ∧
        IsMinOn (separableCoordinateSum q) (stdSimplex 𝕜 ι) x :=
  Iff.rfl

/-- Intrinsic-subtype bridge: the ambient feasible-owner predicate of Definition 6.28.10 is
equivalent to minimizing the restricted objective on the simplex subtype. -/
theorem iff_subtype :
    IsStdSimplexSeparableMinimizer q x ↔
      ∃ hx : x ∈ stdSimplex 𝕜 ι,
        IsMinOn (stdSimplexSeparableObjective q) Set.univ ⟨x, hx⟩ := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    rw [isMinOn_univ_iff]
    intro y
    simpa [stdSimplexSeparableObjective_apply] using
      (isMinOn_iff.mp hmin) y.1 y.2
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    simpa [stdSimplexSeparableObjective_apply] using
      (isMinOn_univ_iff.mp hmin) ⟨y, hy⟩

theorem iff_mem :
    IsStdSimplexSeparableMinimizer q x ↔
      x ∈ stdSimplexSeparableMinimumSet q := by
  rfl

/-- Definition 6.28.10 in the textbook coordinate-sum spelling: the source criterion is
feasibility in the standard simplex together with the pointwise inequality
`∑ i, q i (x i) ≤ ∑ i, q i (y i)` against every feasible `y`. -/
theorem iff_sum :
    IsStdSimplexSeparableMinimizer q x ↔
      x ∈ stdSimplex 𝕜 ι ∧
        ∀ y ∈ stdSimplex 𝕜 ι, ∑ i, q i (x i) ≤ ∑ i, q i (y i) := by
  constructor
  · rintro ⟨hxmem, hmin⟩
    refine ⟨hxmem, ?_⟩
    simpa [isMinOn_iff, separableCoordinateSum_apply] using hmin
  · rintro ⟨hxmem, hsum⟩
    refine ⟨hxmem, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    simpa [separableCoordinateSum_apply] using hsum y hy

end IsStdSimplexSeparableMinimizer

namespace stdSimplexSeparableMinimumSet

variable {q}

theorem mem_iff {x : ι → 𝕜} :
    x ∈ stdSimplexSeparableMinimumSet q ↔
      IsStdSimplexSeparableMinimizer q x :=
  Iff.rfl

/-- Textbook coordinate-sum spelling of membership in `stdSimplexSeparableMinimumSet q`. -/
theorem mem_iff_sum {x : ι → 𝕜} :
    x ∈ stdSimplexSeparableMinimumSet q ↔
      x ∈ stdSimplex 𝕜 ι ∧
        ∀ y ∈ stdSimplex 𝕜 ι, ∑ i, q i (x i) ≤ ∑ i, q i (y i) := by
  simpa [mem_iff] using
    (IsStdSimplexSeparableMinimizer.iff_sum (q := q) (x := x))

end stdSimplexSeparableMinimumSet

end
