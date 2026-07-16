import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped Rockafellar
open LinearConstraintRelation

variable {E : Type u} {Y : Type v} {R : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.4 introduces the subset cut out by a family of weak linear
  inequalities indexed by a set `S⋆ ⊆ Y × R`; specializing to the inner-product pairing with
  `R = ℝ` recovers the textbook `ℝ^n` statement.
- `core/canonical`: the canonical owner here is the upstream indexed weak feasible owner
  `LinearConstraintRelation.leFeasible`, instantiated on the intrinsic subtype index `S⋆`.
- `bridge/view`: this owner is also the intersection of weak half-spaces
  `closedHalfSpaceLE y.1 y.2` attached to the primitive data `y ∈ S⋆`.

Domain-style sampling used here:
- the chapter half-space owner `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `mem_closedHalfSpaceLE_iff` from `Chap01.Definition_2_0_3`;
- the weak indexed owner `LinearConstraintRelation.leFeasible` from
  `Chap01.Corollary_2_1_1`;
- `LinearConstraintRelation.mem_leFeasible` from `Chap01.Corollary_2_1_1`.

Primitive data vs derived API:
- primitive data: the set `S⋆ : Set (Y × R)` and pairing values `⟪x, y.1⟫ₚ`;
- source-facing owner: `linearInequalitySolutionSet S⋆`;
- derived API: the explicit membership form and indexed-range bridge to
  `LinearConstraintRelation.leFeasible`.

Layer target: `source-facing`. The owner is stated at the primitive pairing/order layer rather
than a concrete real inner-product model.
-/

section Ordered

variable [LE R] [HasPairing E Y R]

/-- Definition 17.2.4, stated at the primitive pairing layer: the subset of `E` cut out by the
family of weak inequalities encoded by `SStar ⊆ Y × R`. -/
abbrev linearInequalitySolutionSet (SStar : Set (Y × R)) : Set E :=
  (leFeasible (fun y : SStar ↦ y.1.1) (fun y ↦ y.1.2) : Set E)

scoped[Rockafellar] notation3:max "solutionSet[" SStar "]" =>
  linearInequalitySolutionSet SStar

/-- Membership in `linearInequalitySolutionSet SStar` means satisfying every inequality encoded by
an element of `SStar`. -/
@[simp] theorem mem_linearInequalitySolutionSet_iff {SStar : Set (Y × R)} {x : E} :
    x ∈ solutionSet[SStar] ↔ ∀ y ∈ SStar, ⟪x, y.1⟫ₚ ≤ y.2 := by
  rw [linearInequalitySolutionSet, mem_leFeasible]
  constructor
  · intro hx y hy
    exact hx ⟨y, hy⟩
  · intro hx y
    exact hx y.1 y.2

/-- Membership in the `Set.range` presentation of a weak indexed system is exactly the textbook
pointwise family of inequalities. This source-facing inequality lemma stays at the primitive
`[LE R]` pairing layer. -/
@[simp] theorem mem_linearInequalitySolutionSet_range_iff
    {I : Sort*} (a : I → Y) (α : I → R) {x : E} :
    x ∈ solutionSet[Set.range fun i ↦ (a i, α i)] ↔ ∀ i, ⟪x, a i⟫ₚ ≤ α i := by
  rw [mem_linearInequalitySolutionSet_iff]
  constructor
  · intro hx i
    simpa using hx (a i, α i) ⟨i, rfl⟩
  · intro hx y hy
    rcases hy with ⟨i, rfl⟩
    simpa using hx i

/-- The source-facing weak-system owner is definitionally the upstream weak indexed owner. -/
theorem linearInequalitySolutionSet_eq_leFeasible (SStar : Set (Y × R)) :
    solutionSet[SStar] =
      (leFeasible (fun y : SStar ↦ y.1.1) (fun y ↦ y.1.2) : Set E) :=
  rfl

/-- The source-facing owner is exactly the intersection of the primitive weak-inequality fibers
indexed by `SStar`. This bridge stays at the minimal order layer `[LE R]`. -/
theorem linearInequalitySolutionSet_eq_iInter_setOf
    (SStar : Set (Y × R)) :
    solutionSet[SStar] = ⋂ y ∈ SStar, {x : E | ⟪x, y.1⟫ₚ ≤ y.2} := by
  ext x
  simp [linearInequalitySolutionSet, mem_leFeasible]

end Ordered

section WeakConstraintBridge

variable [HasPairing E Y R]

/-- The source-facing owner is exactly the textbook intersection of the half-spaces encoded by
`SStar`. -/
theorem linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE [LE R]
    (SStar : Set (Y × R)) :
    solutionSet[SStar] = ⋂ y ∈ SStar, (closedHalfSpaceLE y.1 y.2 : Set E) := by
  rw [linearInequalitySolutionSet_eq_iInter_setOf (SStar := SStar)]
  ext x
  simp [closedHalfSpaceLE]

/-- For an indexed weak system, the `Set.range` presentation of Definition 17.2.4 is exactly the
upstream indexed weak owner `LinearConstraintRelation.leFeasible`. -/
theorem linearInequalitySolutionSet_range_eq_leFeasible
    [LE R]
    {I : Sort*} (a : I → Y) (α : I → R) :
    solutionSet[Set.range fun i ↦ (a i, α i)] =
      (leFeasible a α : Set E) := by
  ext x
  rw [mem_linearInequalitySolutionSet_iff, mem_leFeasible]
  constructor
  · intro hx i
    simpa using hx (a i, α i) ⟨i, rfl⟩
  · intro hx y hy
    rcases hy with ⟨i, rfl⟩
    simpa using hx i

end WeakConstraintBridge

end
