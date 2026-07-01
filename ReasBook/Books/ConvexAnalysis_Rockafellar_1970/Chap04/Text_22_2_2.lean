import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar
open LinearConstraintRelation

universe u

section

variable {E : Type*} {Y : Type*} {R : Type*} [LE R] [HasPairing E Y R] {I : Sort u}

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.2.2 describes when one weak linear inequality follows from a displayed
  system of weak linear inequalities. The coordinate-free theorem below is kept at the primitive
  pairing/order layer and specializes to the textbook `R^n` form via the canonical inner-product
  pairing.
- `core/canonical`: the primary owner surface is inclusion from the intrinsic weak indexed owner
  `LinearConstraintRelation.leFeasible a α` into the target half-space owner
  `closedHalfSpaceLE a₀ α₀`.
- `bridge/view`: the pointwise set `{x | ⟪x, a₀⟫ₚ ≤ α₀}` is only a surface rewrite of
  `closedHalfSpaceLE a₀ α₀`.
- `bridge/view`: `linearInequalitySolutionSet SStar` and its `Set.range` specialization remain
  source-facing wrappers of this intrinsic owner.

Domain-style sampling used here:
- `linearInequalitySolutionSet` from `Chap04.Definition_17_2_4`;
- `mem_linearInequalitySolutionSet_iff` and `mem_linearInequalitySolutionSet_range_iff` from
  `Chap04.Definition_17_2_4`;
- `LinearConstraintRelation.leFeasible` and `LinearConstraintRelation.mem_leFeasible` from
  `Chap01.Corollary_2_1_1`;
- `closedHalfSpaceLE` and `mem_closedHalfSpaceLE_iff` from `Chap01.Definition_2_0_3`.

Primitive data vs derived API:
- primitive data: indexed weak-system coefficients `a : I → Y`, bounds `α : I → R`, and target
  pair `(a0, α0)`;
- core owner object: `LinearConstraintRelation.leFeasible a α`;
- derived API: the source-facing `SStar` and `Set.range` reformulations.

Layer target: `core/canonical`, with a weakest-order `[LE R]` theorem surface already stated in
terms of `closedHalfSpaceLE`.
-/

/-- Intrinsic owner form of Text 22.2.2: for a family `i ↦ (a i, α i)`, consequence is owner
inclusion from the weak indexed owner `LinearConstraintRelation.leFeasible` into
`closedHalfSpaceLE a₀ α₀`. -/
theorem leFeasible_subset_closedHalfSpaceLE_iff
    (a0 : Y) (α0 : R) (a : I → Y) (α : I → R) :
    leFeasible a α ⊆ (closedHalfSpaceLE a0 α0 : Set E) ↔
      ∀ x : E, (∀ i, ⟪x, a i⟫ₚ ≤ α i) → ⟪x, a0⟫ₚ ≤ α0 := by
  simp [Set.subset_def, mem_leFeasible, mem_closedHalfSpaceLE_iff]

/-- Indexed weakest-order canonical owner form of Text 22.2.2. -/
theorem is_linear_inequality_consequence_leFeasible_iff
    (a0 : Y) (α0 : R) (a : I → Y) (α : I → R) :
    leFeasible a α ⊆ (closedHalfSpaceLE a0 α0 : Set E) ↔
      ∀ x : E, (∀ i, ⟪x, a i⟫ₚ ≤ α i) → ⟪x, a0⟫ₚ ≤ α0 :=
  leFeasible_subset_closedHalfSpaceLE_iff (a0 := a0) (α0 := α0) (a := a) (α := α)

/-- Source-facing `SStar` bridge form of Text 22.2.2: rewrite the indexed owner into
`linearInequalitySolutionSet SStar`. -/
theorem is_linear_inequality_consequence_iff
    (a0 : Y) (α0 : R) (SStar : Set (Y × R)) :
    solutionSet[SStar] ⊆ (closedHalfSpaceLE a0 α0 : Set E) ↔
      ∀ x : E, x ∈ solutionSet[SStar] → ⟪x, a0⟫ₚ ≤ α0 := by
  simp [Set.subset_def, mem_closedHalfSpaceLE_iff]

/-- Indexed `Set.range` canonical owner form of Text 22.2.2. -/
theorem is_linear_inequality_consequence_range_iff
    (a0 : Y) (α0 : R) (a : I → Y) (α : I → R) :
    solutionSet[Set.range fun i ↦ (a i, α i)] ⊆
      (closedHalfSpaceLE a0 α0 : Set E) ↔
      ∀ x : E, (∀ i, ⟪x, a i⟫ₚ ≤ α i) → ⟪x, a0⟫ₚ ≤ α0 := by
  simpa [linearInequalitySolutionSet_range_eq_leFeasible] using
    (is_linear_inequality_consequence_leFeasible_iff
      (a0 := a0) (α0 := α0) (a := a) (α := α))

/-- Pointwise bridge form of Text 22.2.2: rewrite the target half-space owner into the explicit
inequality set `{x | ⟪x, a₀⟫ₚ ≤ α₀}`. -/
theorem is_linear_inequality_consequence_set_iff
    (a0 : Y) (α0 : R) (SStar : Set (Y × R)) :
    solutionSet[SStar] ⊆ {x : E | ⟪x, a0⟫ₚ ≤ α0} ↔
      ∀ x : E, x ∈ solutionSet[SStar] → ⟪x, a0⟫ₚ ≤ α0 := by
  simpa [mem_closedHalfSpaceLE_iff] using
    (is_linear_inequality_consequence_iff (a0 := a0) (α0 := α0) (SStar := SStar))

/-- Indexed pointwise bridge form of Text 22.2.2. -/
theorem is_linear_inequality_consequence_leFeasible_set_iff
    (a0 : Y) (α0 : R) (a : I → Y) (α : I → R) :
    leFeasible a α ⊆ {x : E | ⟪x, a0⟫ₚ ≤ α0} ↔
      ∀ x : E, (∀ i, ⟪x, a i⟫ₚ ≤ α i) → ⟪x, a0⟫ₚ ≤ α0 := by
  simpa [mem_closedHalfSpaceLE_iff] using
    (is_linear_inequality_consequence_leFeasible_iff
      (a0 := a0) (α0 := α0) (a := a) (α := α))

/-- Indexed `Set.range` pointwise bridge form of Text 22.2.2. -/
theorem is_linear_inequality_consequence_range_set_iff
    (a0 : Y) (α0 : R) (a : I → Y) (α : I → R) :
    solutionSet[Set.range fun i ↦ (a i, α i)] ⊆
      {x : E | ⟪x, a0⟫ₚ ≤ α0} ↔
      ∀ x : E, (∀ i, ⟪x, a i⟫ₚ ≤ α i) → ⟪x, a0⟫ₚ ≤ α0 := by
  simpa [mem_closedHalfSpaceLE_iff] using
    (is_linear_inequality_consequence_range_iff
      (a0 := a0) (α0 := α0) (a := a) (α := α))

end
