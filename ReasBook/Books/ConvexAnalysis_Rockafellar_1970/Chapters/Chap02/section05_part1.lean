import Mathlib
import Mathlib.Analysis.InnerProductSpace.Orthogonal

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_2_5_1 (from Chap01) -/
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.5.1 says that the common solution set of the homogeneous linear
  inequalities `⟪x, b i⟫ₚ ≤ 0` is a convex cone. The canonical owner for this all-`le` homogeneous
  specialization is `LinearConstraintRelation.homogeneousLeFeasibleSet`.
- `core/canonical`: each single-constraint factor is `closedHalfSpaceLE (b i) 0`, discharged by
  `Set.closedHalfSpaceLE_zero_isConvexCone`; indexed intersections are handled by
  `Set.IsConvexCone.iInter`, and rewritten through
  `LinearConstraintRelation.homogeneousLeFeasibleSet`.
- `bridge/view`: the specialized weak owner `LinearConstraintRelation.leFeasible` and the textbook
  set `{x | ∀ i, ⟪x, b i⟫ₚ ≤ 0}` are recovered as downstream views of the homogeneous owner layer.
- Primitive data vs derived API: the family `b : I → Y` is primitive data; the source-facing
  conclusion `Set.IsConvexCone 𝕜 _` is derived API.
  `LinearConstraintRelation.homogeneousLeFeasibleSet`,
  `Set.closedHalfSpaceLE_zero_isConvexCone`, and
  `Set.IsConvexCone.iInter`.
- Layer target: `source-facing` at the homogeneous-feasible-set owner layer, with `bridge/view`
  restatements for the weak-owner and textbook set-builder surfaces.
-/

namespace LinearConstraintRelation

/-- Corollary 2.5.1 in canonical owner form: the homogeneous all-`le` feasible set is a convex
cone. -/
theorem homogeneousLeFeasibleSet_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (homogeneousLeFeasibleSet 𝕜 b : Set X) := by
  simpa [homogeneousLeFeasibleSet_eq_iInter_closedHalfSpaceLE_zero (b := b)] using
    (Set.IsConvexCone.iInter (fun i ↦ Set.closedHalfSpaceLE_zero_isConvexCone (b i)))

/-- Bridge form of Corollary 2.5.1 at the weak owner layer `leFeasible`. -/
theorem leFeasible_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (leFeasible b (fun _ : I ↦ (0 : 𝕜)) : Set X) := by
  simpa [homogeneousLeFeasibleSet_eq_leFeasible_zero] using
    homogeneousLeFeasibleSet_isConvexCone (b := b)

end LinearConstraintRelation

/-- The homogeneous closed-half-space intersection attached to `b` is a convex cone. -/
theorem iInter_closedHalfSpaceLE_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 ((⋂ i, closedHalfSpaceLE (b i) (0 : 𝕜)) : Set X) := by
  simpa [LinearConstraintRelation.homogeneousLeFeasibleSet_eq_iInter_closedHalfSpaceLE_zero
    (b := b)] using
    LinearConstraintRelation.homogeneousLeFeasibleSet_isConvexCone (b := b)

/-- Corollary 2.5.1, stated at the pairing layer: for any family of vectors `b i`, the set of all
`x` satisfying `⟪x, b i⟫ₚ ≤ 0` for every index `i` is a convex cone, formalized in the chapter's
source-facing form `Set.IsConvexCone 𝕜 _`. -/
theorem setOf_forall_pairing_nonpos_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ (0 : 𝕜)} := by
  rw [← LinearConstraintRelation.homogeneousLeFeasibleSet_eq_setOf (X := X) (b := b)]
  exact LinearConstraintRelation.homogeneousLeFeasibleSet_isConvexCone (b := b)

end

/-! ### Corollary_2_5_2 (from Chap01) -/
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {I : Sort u}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.5.2 says that the common solution set of the homogeneous linear
  inequalities `0 ≤ ⟪x, b i⟫ₚ` is a convex cone; the pairing-layer formulation here specializes to
  the textbook `R^n` statement under the standard real inner product.
- `core/canonical`: the primitive owner is a family of linear maps `f : I → X →ₗ[𝕜] 𝕜`; the
  homogeneous nonnegative system is the set `{x | ∀ i, 0 ≤ f i x}`.
- `bridge/view`: pairing constraints `0 ≤ ⟪x, b i⟫ₚ` are obtained by specializing
  `f i = HasLinearPairing.pairingLinear.flip (b i)`, and the Chapter 1 owner
  `LinearConstraintRelation.homogeneousGeFeasibleSet` is a downstream reformulation of that
  set-builder view.
- Primitive data vs derived API: primitive data are the linear family `f`; convex-cone closure is
  derived API via `Set.closedHalfSpaceGE_zero_isConvexCone` and `Set.IsConvexCone.iInter`.
- Layer target: `core/canonical` first, with source-facing owner and textbook pairing forms as
  bridge theorems.
-/

/-- Core owner theorem for Corollary 2.5.2: a homogeneous nonnegative linear-map system is a
convex cone. -/
theorem setOf_forall_zero_le_linearMap_isConvexCone (f : I → X →ₗ[𝕜] 𝕜) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, (0 : 𝕜) ≤ f i x} := by
  have hset : {x : X | ∀ i, (0 : 𝕜) ≤ f i x} =
      (⋂ i, (closedHalfSpaceGE (f i) (0 : 𝕜) : Set X)) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr (fun i ↦ ?_)
      exact (mem_closedHalfSpaceGE_iff).2 (by
        change (0 : 𝕜) ≤ f i x
        exact hx i)
    · intro hx i
      have hxi : x ∈ (closedHalfSpaceGE (f i) (0 : 𝕜) : Set X) := (Set.mem_iInter.mp hx) i
      have hxi' : (0 : 𝕜) ≤ ⟪x, f i⟫ₚ := (mem_closedHalfSpaceGE_iff).1 hxi
      change (0 : 𝕜) ≤ f i x at hxi'
      exact hxi'
  rw [hset]
  exact Set.IsConvexCone.iInter (fun i ↦
    Set.closedHalfSpaceGE_zero_isConvexCone
      (𝕜 := 𝕜) (X := X) (Y := X →ₗ[𝕜] 𝕜) (b := f i))

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

omit [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜] in
/-- Helper for Corollary 2.5.2: the homogeneous all-`ge` feasible set is the indexed
intersection of the corresponding closed half-spaces through the origin. -/
theorem homogeneousGeFeasibleSet_eq_iInter_closedHalfSpaceGE_zero (b : I → Y) :
    (homogeneousGeFeasibleSet 𝕜 b : Set X) =
      ((⋂ i, closedHalfSpaceGE (b i) (0 : 𝕜)) : Set X) := by
  -- Unfold both owner descriptions to the same pointwise nonnegativity condition.
  ext x
  simp

/-- Helper for Corollary 2.5.2: the homogeneous all-`ge` feasible set is a convex cone. -/
theorem homogeneousGeFeasibleSet_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (homogeneousGeFeasibleSet 𝕜 b : Set X) := by
  -- Rewrite the feasible set as the intersection from the source proof.
  rw [homogeneousGeFeasibleSet_eq_iInter_closedHalfSpaceGE_zero]
  -- Each homogeneous closed half-space is a convex cone, and arbitrary intersections preserve it.
  exact Set.IsConvexCone.iInter (fun i ↦
    Set.closedHalfSpaceGE_zero_isConvexCone (𝕜 := 𝕜) (X := X) (Y := Y) (b := b i))

/-- Bridge form of Corollary 2.5.2 at the weak owner layer `geFeasible`. -/
theorem geFeasible_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (geFeasible b (fun _ : I ↦ (0 : 𝕜)) : Set X) := by
  simpa [homogeneousGeFeasibleSet, homogeneousFeasibleSet, geFeasible, feasibleSet] using
    homogeneousGeFeasibleSet_isConvexCone (b := b)

end LinearConstraintRelation

/-- The homogeneous closed-half-space `ge` intersection attached to `b` is a convex cone. -/
theorem iInter_closedHalfSpaceGE_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 ((⋂ i, closedHalfSpaceGE (b i) (0 : 𝕜)) : Set X) := by
  exact Set.IsConvexCone.iInter (fun i ↦ Set.closedHalfSpaceGE_zero_isConvexCone (b i))

/-- Corollary 2.5.2, stated at the textbook set-builder surface: for any family of vectors `b i`,
the set of all `x` satisfying `0 ≤ ⟪x, b i⟫ₚ` for every index `i` is a convex cone. -/
theorem setOf_forall_pairing_nonneg_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, (0 : 𝕜) ≤ ⟪x, b i⟫ₚ} := by
  -- Return from the owner feasible-set form to the textbook set-builder statement.
  simpa [LinearConstraintRelation.homogeneousGeFeasibleSet_eq_setOf] using
    (LinearConstraintRelation.homogeneousGeFeasibleSet_isConvexCone
      (𝕜 := 𝕜) (X := X) (Y := Y) (I := I) (b := b))

end

/-! ### Corollary_2_5_3 (from Chap01) -/
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

private theorem openHalfSpaceGT_zero_isConvexCone_local (b : Y) :
    Set.IsConvexCone 𝕜 (openHalfSpaceGT b (0 : 𝕜) : Set X) := by
  refine ⟨?_, openHalfSpaceGT_convex b (0 : 𝕜)⟩
  intro c hc x hx
  rw [mem_openHalfSpaceGT_iff] at hx ⊢
  calc
    (0 : 𝕜) = c • (0 : 𝕜) := by simp
    _ < c • ⟪x, b⟫ₚ := by simpa using smul_lt_smul_of_pos_left hx hc
    _ = ⟪c • x, b⟫ₚ := by simp

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {I : Sort u}

/-
Source/core/bridge triage:
- `core/canonical`: for Chapter 1 interfaces, the primitive owner is
  `LinearConstraintRelation.homogeneousGtFeasibleSet`; this file proves convex-cone closure at
  that owner layer.
- `bridge/view`: the open-half-space intersection surface
  `⋂ i, openHalfSpaceGT (b i) 0`, the set-builder pairing surface
  `{x | ∀ i, 0 < ⟪x, b i⟫ₚ}`, and the linear-map specialization
  `{x | ∀ i, 0 < f i x}` are bridge views of the same owner statement.
- Primitive data vs derived API: primitive data for the owner theorem are the relation family and
  normals `b : I → Y`; convex-cone closure is derived API via
  `Set.openHalfSpaceGT_zero_isConvexCone` and `Set.IsConvexCone.iInter`.
- Layer target: `source-facing` owner first, with textbook and linear-functional bridges.
-/

/-- Linear-map bridge form of Corollary 2.5.3: a strict homogeneous linear system is a convex
cone. -/
theorem setOf_forall_zero_lt_linearMap_isConvexCone (f : I → X →ₗ[𝕜] 𝕜) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, (0 : 𝕜) < f i x} := by
  have hset : {x : X | ∀ i, (0 : 𝕜) < f i x} =
      (⋂ i, (openHalfSpaceGT (f i) (0 : 𝕜) : Set X)) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr (fun i ↦ ?_)
      exact (mem_openHalfSpaceGT_iff).2 (by
        change (0 : 𝕜) < f i x
        exact hx i)
    · intro hx i
      exact (by
        have hxi : x ∈ (openHalfSpaceGT (f i) (0 : 𝕜) : Set X) := (Set.mem_iInter.mp hx) i
        exact (by
          have hxi' : (0 : 𝕜) < ⟪x, f i⟫ₚ := (mem_openHalfSpaceGT_iff).1 hxi
          change (0 : 𝕜) < f i x at hxi'
          exact hxi'))
  rw [hset]
  exact Set.IsConvexCone.iInter (fun i ↦
    openHalfSpaceGT_zero_isConvexCone_local (X := X) (Y := X →ₗ[𝕜] 𝕜) (f i))

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- Bridge view: the strict homogeneous owner is exactly the intersection of open half-spaces
through the origin. -/
theorem homogeneousGtFeasibleSet_eq_iInter_openHalfSpaceGT_zero (b : I → Y) :
    homogeneousGtFeasibleSet 𝕜 b =
      ⋂ i, (openHalfSpaceGT (b i) (0 : 𝕜) : Set X) := by
  ext x
  simp [homogeneousGtFeasibleSet, homogeneousFeasibleSet, feasibleSet, solutionSet]

variable [IsOrderedCancelAddMonoid 𝕜] [PosSMulStrictMono 𝕜 𝕜]

/-- Corollary 2.5.3 at the owner layer: the homogeneous all-`gt` feasible set is a convex cone. -/
theorem homogeneousGtFeasibleSet_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (LinearConstraintRelation.homogeneousGtFeasibleSet 𝕜 b : Set X) := by
  simpa [homogeneousGtFeasibleSet_eq_iInter_openHalfSpaceGT_zero] using
    (Set.IsConvexCone.iInter (fun i ↦ openHalfSpaceGT_zero_isConvexCone_local (b i)))

end LinearConstraintRelation

variable [IsOrderedCancelAddMonoid 𝕜] [PosSMulStrictMono 𝕜 𝕜]

/-- The homogeneous strict-superlevel half-space intersection attached to `b` is a convex cone. -/
theorem iInter_openHalfSpaceGT_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (⋂ i, (openHalfSpaceGT (b i) (0 : 𝕜) : Set X)) := by
  simpa [LinearConstraintRelation.homogeneousGtFeasibleSet_eq_iInter_openHalfSpaceGT_zero] using
    LinearConstraintRelation.homogeneousGtFeasibleSet_isConvexCone (b := b)

/-- Corollary 2.5.3, stated at the pairing layer: for any family of vectors `b i`, the set of all
`x` satisfying `0 < ⟪x, b i⟫ₚ` for every index `i` is a convex cone, formalized in the chapter's
source-facing form `Set.IsConvexCone 𝕜 _`. -/
theorem setOf_forall_pairing_pos_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, (0 : 𝕜) < ⟪x, b i⟫ₚ} := by
  simpa [LinearConstraintRelation.homogeneousGtFeasibleSet_eq_setOf] using
    LinearConstraintRelation.homogeneousGtFeasibleSet_isConvexCone (b := b)

end

/-! ### Corollary_2_5_4 (from Chap01) -/
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Preorder 𝕜] [Zero 𝕜]
variable {X : Type*} {Y : Type*} [HasPairing X Y 𝕜]
variable {I : Sort u}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.5.4 states that the common solution set of the strict homogeneous
  linear inequalities `⟪x, b i⟫ₚ < 0` is a convex cone.
- `core/canonical`: the owner layer is the dedicated strict homogeneous owner
  `LinearConstraintRelation.homogeneousLtFeasibleSet`.
- `bridge/view`: the owner set above reduces to the intersection
  `⋂ i, openHalfSpaceLT (b i) 0`, and then to the displayed set-builder form
  `{x | ∀ i, ⟪x, b i⟫ₚ < 0}`.
- Primitive data vs derived API: the family `b : I → Y` is primitive data; the source-facing
  convex-cone conclusions are derived API.
- Domain-style sampling: `LinearConstraintRelation.homogeneousFeasibleSet`,
  `LinearConstraintRelation.homogeneousLtFeasibleSet`, `LinearConstraintRelation.solutionSet`,
  `Set.openHalfSpaceLT_zero_isConvexCone`, and
  `Set.IsConvexCone.iInter`.
- Layer target: `source-facing` at the homogeneous-constraint owner layer, with `bridge/view`
  restatements to open-half-space and set-builder surfaces.
-/

namespace LinearConstraintRelation

/-- Bridge view: the strict homogeneous owner is exactly the intersection of open half-spaces
through the origin. -/
theorem homogeneousLtFeasibleSet_eq_iInter_openHalfSpaceLT_zero (b : I → Y) :
    homogeneousLtFeasibleSet 𝕜 b =
      ⋂ i, (openHalfSpaceLT (b i) (0 : 𝕜) : Set X) := by
  ext x
  simp [homogeneousLtFeasibleSet, homogeneousFeasibleSet, feasibleSet, solutionSet]

end LinearConstraintRelation

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

variable [IsOrderedCancelAddMonoid 𝕜] [PosSMulStrictMono 𝕜 𝕜]

namespace LinearConstraintRelation

/-- Corollary 2.5.4 in canonical strict homogeneous owner form: the all-`lt` feasible set is a
convex cone. -/
theorem homogeneousLtFeasibleSet_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (homogeneousLtFeasibleSet 𝕜 b : Set X) := by
  simpa [homogeneousLtFeasibleSet_eq_iInter_openHalfSpaceLT_zero] using
    (Set.IsConvexCone.iInter (fun i ↦ Set.openHalfSpaceLT_zero_isConvexCone (b i)))

end LinearConstraintRelation

/-- The homogeneous strict-sublevel half-space intersection attached to `b` is a convex cone. -/
theorem iInter_openHalfSpaceLT_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 (⋂ i, (openHalfSpaceLT (b i) (0 : 𝕜) : Set X)) := by
  simpa [LinearConstraintRelation.homogeneousLtFeasibleSet_eq_iInter_openHalfSpaceLT_zero] using
    LinearConstraintRelation.homogeneousLtFeasibleSet_isConvexCone (b := b)

/-- Corollary 2.5.4, stated at the pairing layer: for any family of vectors `b i`, the set of all
`x` satisfying `⟪x, b i⟫ₚ < 0` for every index `i` is a convex cone, formalized in the chapter's
source-facing form `Set.IsConvexCone 𝕜 _`. -/
theorem setOf_forall_pairing_neg_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ < (0 : 𝕜)} := by
  simpa [LinearConstraintRelation.homogeneousLtFeasibleSet_eq_setOf] using
    LinearConstraintRelation.homogeneousLtFeasibleSet_isConvexCone (b := b)

end

/-! ### Corollary_2_5_5 (from Chap01) -/
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Z : Type*} [AddCommMonoid Z] [Module 𝕜 Z]
variable {I : Sort u}

/-
Source/core/bridge triage:
- `core/canonical`: the primitive owner layer for homogeneous equations is a family of linear
  maps `f : I → X →ₗ[𝕜] Z`; the common zero set is the intersection of kernels
  `⋂ i, LinearMap.ker (f i)` and should be exposed as a convex-cone theorem at this layer.
- `bridge/view`: the pairing form `⟪x, b i⟫ₚ = 0` is a specialization through
  `f i = HasLinearPairing.pairingLinear.flip (b i)`.
- `source-facing`: the labeled corollary remains the textbook pairing statement, now factored as
  a thin bridge over the linear-map owner theorem.
- Primitive data vs derived API: primitive data for the canonical owner theorem are
  `f : I → X →ₗ[𝕜] Z`; primitive data for the source-facing corollary are `b : I → Y` and a
  pairing instance. Convex-cone closure is derived API in both views.
- Layer target: `core/canonical` first, with pairing and inner-product statements as bridge views.
-/

namespace LinearMap

/-- The kernel of a linear map is a convex cone. -/
theorem ker_isConvexCone (f : X →ₗ[𝕜] Z) :
    Set.IsConvexCone 𝕜 (LinearMap.ker f : Set X) := by
  refine ⟨?_, (LinearMap.ker f).convex⟩
  refine (Set.isCone_iff_forall_pos_smul_subset (𝕜 := 𝕜)
    (K := (LinearMap.ker f : Set X))).2 ?_
  intro c _hc x hx
  rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
  exact (LinearMap.ker f).smul_mem c hy

/-- Core owner theorem for Corollary 2.5.5: the common kernel of any family of linear maps is a
convex cone. -/
theorem iInter_ker_isConvexCone (f : I → X →ₗ[𝕜] Z) :
    Set.IsConvexCone 𝕜 (⋂ i, (LinearMap.ker (f i) : Set X)) := by
  exact Set.IsConvexCone.iInter (fun i ↦ ker_isConvexCone (f i))

/-- Set-builder bridge for the linear-map owner theorem: a homogeneous system
`f i x = 0` defines a convex cone. -/
theorem setOf_forall_eq_zero_isConvexCone (f : I → X →ₗ[𝕜] Z) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, f i x = 0} := by
  have hset : {x : X | ∀ i, f i x = 0} = ⋂ i, (LinearMap.ker (f i) : Set X) := by
    ext x
    simp [LinearMap.mem_ker]
  simpa [hset] using iInter_ker_isConvexCone (f := f)

end LinearMap

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- Corollary 2.5.5 at the canonical homogeneous-constraint owner layer: for equality constraints,
the homogeneous feasible set is a convex cone. -/
theorem homogeneousEqFeasibleSet_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜
      (homogeneousEqFeasibleSet 𝕜 b : Set X) := by
  rw [homogeneousEqFeasibleSet_eq_setOf (b := b)]
  simpa [HasLinearPairing.pairing_eq_pairingLinear] using
    (LinearMap.setOf_forall_eq_zero_isConvexCone
      (f := fun i : I ↦ HasLinearPairing.pairingLinear.flip (b i)))

end LinearConstraintRelation

/-- Corollary 2.5.5, stated at the pairing layer: for any family of vectors `b i`, the common
zero set of the homogeneous linear equations `⟪x, b i⟫ₚ = 0` is a convex cone, formalized in the
chapter's short source-facing form `Set.IsConvexCone 𝕜 _`. -/
theorem setOf_forall_pairing_eq_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ = (0 : 𝕜)} := by
  simpa [LinearConstraintRelation.homogeneousEqFeasibleSet_eq_setOf (b := b)] using
    (LinearConstraintRelation.homogeneousEqFeasibleSet_isConvexCone (b := b))

end

section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {I : Sort u}

/-- Inner-product bridge for Corollary 2.5.5: in an inner-product space, the common zero set of
the equations `inner 𝕜 x (b i) = 0` is exactly the orthogonal complement of the span of the family
`b`. -/
theorem setOf_forall_inner_eq_zero_eq_orthogonal (b : I → E) :
    {x : E | ∀ i, inner 𝕜 x (b i) = 0} = (Submodule.span 𝕜 (Set.range b))ᗮ := by
  let K : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range b)
  ext x
  change (∀ i, inner 𝕜 x (b i) = 0) ↔ x ∈ Kᗮ
  rw [Submodule.mem_orthogonal']
  constructor
  · intro hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        exact hx i
    | zero =>
        simp
    | add y z _ _ hy hz =>
        simp [inner_add_right, hy, hz]
    | smul a y _ hy =>
        simp [inner_smul_right, hy]
  · intro hx i
    exact hx _ (Submodule.subset_span ⟨i, rfl⟩)

end

/-! ### Theorem_2_5 (from Chap01) -/
universe u v

variable {𝕜 : Type v}
variable {E : Type u}

/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.5 states that an arbitrary intersection of convex cones is again a
  convex cone, where Definition 2.5.10 provides the short source-facing owner
  `Set.IsConvexCone 𝕜 K`.
- `core/canonical`: the closure proofs use the owner-side intersection theorems
  `Set.IsCone.sInter` / `Set.IsCone.iInter` and `convex_sInter` / `convex_iInter` through the
  fields of `Set.IsConvexCone`; the source-facing closure API is exposed both at `sInter` and at
  the indexed-family surface `Set.IsConvexCone.iInter`.
- `bridge/view`: mathlib's bundled theorem `ConvexCone.coe_sInf` is only a companion bridge. The
  numbered item itself should stay at the textbook subset layer and reuse the owner-side
  intersection theorems directly.
- Primitive data vs derived API: the primitive datum is the family `S : Set (Set E)`. Closure of
  the source owner `Set.IsConvexCone` under arbitrary intersections is derived API.
- Domain-style sampling: this refinement is guided by the chapter owner `Set.IsCone` from
  Definition 2.5.9, the short source-facing owner `Set.IsConvexCone` from Definition 2.5.10,
  `Set.IsCone.sInter`, `Set.IsCone.iInter`, `convex_sInter`, `convex_iInter`, and the bundled
  bridge `ConvexCone.coe_sInf`.
- Layer target: `source-facing`.
-/

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

namespace Set.IsConvexCone

/-- Primitive constructor form of Theorem 2.5: if each member of a family is both a cone and
convex, then the intersection is a convex cone. -/
theorem sInter_mk {S : Set (Set E)}
    (hCone : ∀ s ∈ S, Set.IsCone 𝕜 s)
    (hConvex : ∀ s ∈ S, Convex 𝕜 s) :
    IsConvexCone 𝕜 (⋂₀ S) := by
  exact ⟨Set.IsCone.sInter hCone, convex_sInter hConvex⟩

/-- Theorem 2.5: an arbitrary intersection of convex cones is again a convex cone, expressed in the
chapter's source-facing owner form `Set.IsConvexCone 𝕜 _`. -/
theorem sInter {S : Set (Set E)}
    (hS : ∀ s ∈ S, IsConvexCone 𝕜 s) : IsConvexCone 𝕜 (⋂₀ S) := by
  exact sInter_mk (fun s hs ↦ (hS s hs).isCone) (fun s hs ↦ (hS s hs).convex)

/-- Primitive constructor form of indexed intersection closure for convex cones. -/
theorem iInter_mk {ι : Sort*} {s : ι → Set E}
    (hCone : ∀ i, Set.IsCone 𝕜 (s i))
    (hConvex : ∀ i, Convex 𝕜 (s i)) :
    IsConvexCone 𝕜 (⋂ i, s i) := by
  exact ⟨Set.IsCone.iInter hCone, convex_iInter hConvex⟩

/-- Indexed-family form of Theorem 2.5: intersections written as `iInter` are convex cones when
every fiber is a convex cone. -/
theorem iInter {ι : Sort*} {s : ι → Set E}
    (hs : ∀ i, IsConvexCone 𝕜 (s i)) : IsConvexCone 𝕜 (⋂ i, s i) := by
  exact iInter_mk (fun i ↦ (hs i).isCone) (fun i ↦ (hs i).convex)

end Set.IsConvexCone

/-! ### Corollary_2_5_6 (from Chap01) -/
open scoped Rockafellar

universe u

section

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.5.6 states that the common solution set of a homogeneous system of
  linear relations of the five textbook forms is a convex cone; the coordinate-free
  pairing formulation specializes to the textbook `R^n` statement.
- `core/canonical`: the chapter owner abstractions are `LinearConstraintRelation`,
  `LinearConstraintRelation.homogeneousFeasibleSet`, and the short source-facing convex-cone owner
  `Set.IsConvexCone`.
- `bridge/view`: a homogeneous system is exactly a linear-constraint system with right-hand side
  identically zero, so this file should specialize the existing Chapter 1 owner instead of
  introducing a second homogeneous-only relation type and feasible-set wrapper.
- Primitive data vs derived API: for one homogeneous constraint, the primitive owner data are the
  relation tag and normal `b : Y`; the convex-cone property of `relation.solutionSet b 0` is
  derived from the owner half-space theorems and, for the equality case, the kernel owner of the
  pairing linear functional. For a homogeneous system, the primitive data are the relation family
  `relation : I → LinearConstraintRelation` and normals `b : I → Y`; the set-level cone property
  of the zero-right-hand-side feasible set is then derived from those single-constraint owner facts
  plus the existing feasible-set owner `LinearConstraintRelation.feasibleSet`.
  `LinearConstraintRelation.feasibleSet`, `Set.closedHalfSpaceLE_zero_isConvexCone`,
  `Set.closedHalfSpaceGE_zero_isConvexCone`, `Set.openHalfSpaceLT_zero_isConvexCone`,
  `Set.openHalfSpaceGT_zero_isConvexCone`, `LinearMap.ker`, and `Set.IsConvexCone.iInter`.
- Layer target: `bridge/view`, specializing the Chapter 1 linear-constraint owner to the
  homogeneous case `β = 0`.
-/

namespace LinearConstraintRelation

/-- A single homogeneous linear constraint of any of the five textbook relation kinds cuts out a
convex cone. -/
theorem solutionSet_zero_isConvexCone
    (relation : LinearConstraintRelation) (b : Y) :
    Set.IsConvexCone 𝕜 (relation.solutionSet b (0 : 𝕜) : Set X) := by
  cases relation with
  | le =>
      simpa [Set.IsConvexCone, LinearConstraintRelation.solutionSet] using
        Set.closedHalfSpaceLE_zero_isConvexCone b
  | ge =>
      simpa [Set.IsConvexCone, LinearConstraintRelation.solutionSet] using
        Set.closedHalfSpaceGE_zero_isConvexCone b
  | lt =>
      simpa [Set.IsConvexCone, LinearConstraintRelation.solutionSet] using
        Set.openHalfSpaceLT_zero_isConvexCone b
  | gt =>
      simpa [Set.IsConvexCone, LinearConstraintRelation.solutionSet] using
        Set.openHalfSpaceGT_zero_isConvexCone b
  | eq =>
      let K : Submodule 𝕜 X := LinearMap.ker (HasLinearPairing.pairingLinear.flip b)
      have hK : (LinearConstraintRelation.eq.solutionSet b (0 : 𝕜) : Set X) = (K : Set X) := by
        ext x
        simp [K, LinearConstraintRelation.solutionSet, LinearMap.mem_ker,
          HasLinearPairing.pairing_eq_pairingLinear]
      change Set.IsConvexCone 𝕜 (LinearConstraintRelation.eq.solutionSet b (0 : 𝕜) : Set X)
      rw [hK]
      refine ⟨?_, K.convex⟩
      intro c x _ hx
      exact K.smul_mem c hx

/-- Corollary 2.5.6 at the owner layer: every homogeneous feasible set of textbook linear
relations is a convex cone. -/
theorem homogeneousFeasibleSet_isConvexCone
    (relation : I → LinearConstraintRelation) (b : I → Y) :
    Set.IsConvexCone 𝕜 (homogeneousFeasibleSet 𝕜 relation b : Set X) := by
  simpa [homogeneousFeasibleSet, feasibleSet] using
    Set.IsConvexCone.iInter (fun i ↦ (relation i).solutionSet_zero_isConvexCone (b i))

end LinearConstraintRelation

end

/-! ### Definition_2_5_9 (from Chap01) -/
open scoped BigOperators Pointwise

universe u v

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.5.9 introduces the cone predicate on subsets of `R^n` by closure
  under multiplication by positive real scalars.
- `core/canonical`: the chapter owner predicate for that notion is
  `Set.IsCone`, exposed canonically as pointwise positive-scalar closure
  `∀ c > 0, ∀ x ∈ K, c • x ∈ K`; on the bundled side, mathlib's owner object is
  `ConvexCone R E`.
- `bridge/view`: `ConvexCone.isCone` forgets the additive closure of a bundled convex cone and
  recovers the weaker source-facing predicate on its underlying set over the same scalar semiring.
- Primitive data vs derived API: pointwise positive-scalar closure is the primitive source-level
  content; the setwise positive-ray inclusion `({c : R | 0 < c}) • K ⊆ K` and the bundled
  `ConvexCone` view are derived bridges. There is no upstream unbundled owner in mathlib to
  replace `Set.IsCone`.
  This file should therefore keep the source predicate and only use the bundled cone as a bridge.
  Domain-style sampling used here: `Set.IsCone`, `Set.smul_set_subset_iff`, `Set.mem_smul`,
  `HasLinearPairing.pairingLinear`, `Set.mem_finset_sum` / `Set.mem_fintype_sum`, and the bundled
  bridge `ConvexCone.smul_mem`. These confirm that the source-facing cone owner remains primitive,
  while pairing-based dual-evaluation lemmas and bundled cone bridges stay derived.
- Layer target: `source-facing`; this file owns the unbundled textbook predicate, while the only
  retained derived API is the setwise positive-scalar bridge, the primitive finite-sum closure
  theorem on `Finset`s together with its `Fintype` specialization, and the bundled-to-set bridge
  theorem below.
-/

namespace Set

variable {𝕜 : Type v} {E : Type u}

section

variable (𝕜 : Type v) [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E]

/-- Definition 2.5.9: a subset is a cone if it is closed under multiplication by positive
scalars. This owner is primitive in pointwise form. -/
def IsCone (K : Set E) : Prop :=
  ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ K → c • x ∈ K

end

section

variable {𝕜 : Type v} [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E]

/-- Definition 2.5.9 in canonical setwise form as a bridge theorem. -/
theorem isCone_iff_pos_smul_subset (K : Set E) :
    IsCone 𝕜 K ↔ ({c : 𝕜 | 0 < c}) • K ⊆ K := by
  constructor
  · intro hK x hx
    rcases Set.mem_smul.mp hx with ⟨c, hc, y, hy, rfl⟩
    exact hK hc hy
  · intro hK c hc x hx
    exact hK (Set.mem_smul.mpr ⟨c, hc, x, hx, rfl⟩)

/-- Setwise action bridge form of Definition 2.5.9:
`K` is a cone iff each positive scalar acts invariantly on `K` as a whole set. -/
theorem isCone_iff_forall_pos_smul_subset (K : Set E) :
    IsCone 𝕜 K ↔ ∀ c : 𝕜, 0 < c → c • K ⊆ K := by
  constructor
  · intro hK c hc
    exact smul_set_subset_iff.2 (fun x hx ↦ hK hc hx)
  · intro hK c hc x hx
    exact smul_set_subset_iff.mp (hK c hc) hx

end

namespace IsCone

variable [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E]

/-- A cone is closed under multiplication by each positive scalar. -/
theorem smul_mem {K : Set E} (hK : IsCone 𝕜 K) {c : 𝕜}
    (hc : 0 < c) {x : E} (hx : x ∈ K) : c • x ∈ K :=
  hK hc hx

/-- A cone is stable under each positive scalar action on its whole carrier set. -/
theorem smul_set_subset {K : Set E} (hK : IsCone 𝕜 K) {c : 𝕜}
    (hc : 0 < c) : c • K ⊆ K :=
  smul_set_subset_iff.2 (hK hc)

/-- An arbitrary intersection of cones is again a cone. -/
theorem sInter {S : Set (Set E)} (hS : ∀ s ∈ S, IsCone 𝕜 s) :
    IsCone 𝕜 (⋂₀ S) := by
  intro c hc x hx
  rw [Set.mem_sInter] at hx ⊢
  intro s hs
  exact (hS s hs) hc (hx s hs)

/-- Indexed-family form of cone intersection closure. -/
theorem iInter {ι : Sort*} {s : ι → Set E} (hs : ∀ i, IsCone 𝕜 (s i)) :
    IsCone 𝕜 (⋂ i, s i) := by
  intro c hc x hx
  rw [Set.mem_iInter] at hx ⊢
  intro i
  exact (hs i) hc (hx i)

end IsCone

section PairingLinearOrderedSemifield

open scoped Rockafellar

namespace IsCone

variable {𝕜 : Type v} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- If the pairing with `b` is bounded above on a cone by an explicit scalar bound `β`, then every
pairing value on that cone is nonpositive. This primitive owner-level theorem underlies the
`BddAbove` bridge below. -/
theorem pairing_nonpos_of_upperBound
    {K : Set X} (hK : IsCone 𝕜 K) {b : Y} {β : 𝕜}
    (hβ : ∀ x ∈ K, ⟪x, b⟫ₚ ≤ β) (x : X) (hx : x ∈ K) :
    ⟪x, b⟫ₚ ≤ (0 : 𝕜) := by
  by_contra hx_nonpos
  have hx_pos : (0 : 𝕜) < ⟪x, b⟫ₚ := lt_of_not_ge hx_nonpos
  let c : 𝕜 := max β 0 / ⟪x, b⟫ₚ + 1
  have hc : 0 < c := by
    dsimp [c]
    have h_nonneg : 0 ≤ max β 0 / ⟪x, b⟫ₚ := by
      exact div_nonneg (le_max_right β 0) (le_of_lt hx_pos)
    exact lt_of_lt_of_le (show (0 : 𝕜) < 1 by exact zero_lt_one) (le_add_of_nonneg_left h_nonneg)
  have hcx : ⟪c • x, b⟫ₚ ≤ β := hβ _ (hK.smul_mem hc hx)
  have hmul : c * ⟪x, b⟫ₚ ≤ β := by
    simpa [c] using hcx
  have hcalc : c * ⟪x, b⟫ₚ = max β 0 + ⟪x, b⟫ₚ := by
    calc
      c * ⟪x, b⟫ₚ = (max β 0 / ⟪x, b⟫ₚ + 1) * ⟪x, b⟫ₚ := by rfl
      _ = (max β 0 / ⟪x, b⟫ₚ) * ⟪x, b⟫ₚ + ⟪x, b⟫ₚ := by ring
      _ = max β 0 + ⟪x, b⟫ₚ := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hx_pos.ne', mul_one]
  have hsum_le : max β 0 + ⟪x, b⟫ₚ ≤ β := hcalc ▸ hmul
  have hβ_lt : β < max β 0 + ⟪x, b⟫ₚ :=
    lt_of_le_of_lt (le_max_left β 0) (lt_add_of_pos_right (max β 0) hx_pos)
  exact (not_le_of_gt hβ_lt) hsum_le

/-- If the pairing with `b` is bounded above on a cone, then it is nonpositive on that cone. -/
theorem pairing_nonpos_of_bddAbove {K : Set X} (hK : IsCone 𝕜 K) {b : Y}
    (hbdd : BddAbove ((fun x : X ↦ (⟪x, b⟫ₚ : 𝕜)) '' K)) (x : X) (hx : x ∈ K) :
    ⟪x, b⟫ₚ ≤ (0 : 𝕜) := by
  rcases hbdd with ⟨β, hβ⟩
  exact pairing_nonpos_of_upperBound hK (fun y hy ↦ hβ ⟨y, hy, rfl⟩) x hx

end IsCone

end PairingLinearOrderedSemifield

section PairingLinearOrderedField

open scoped Rockafellar

namespace IsCone

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Any common upper bound for the pairing with `b` on a nonempty cone is nonnegative. -/
theorem pairing_upperBound_nonneg_of_nonempty {K : Set X} (hK : IsCone 𝕜 K)
    (hK_nonempty : K.Nonempty) {b : Y} {β : 𝕜} (hβ : ∀ x ∈ K, ⟪x, b⟫ₚ ≤ β) :
    (0 : 𝕜) ≤ β := by
  rcases hK_nonempty with ⟨y, hy⟩
  have hy_le : ⟪y, b⟫ₚ ≤ β := hβ y hy
  by_contra hβ_nonneg
  have hβ_neg : β < (0 : 𝕜) := lt_of_not_ge hβ_nonneg
  have hy_neg : ⟪y, b⟫ₚ < (0 : 𝕜) := lt_of_le_of_lt hy_le hβ_neg
  let c : 𝕜 := β / ((2 : 𝕜) * ⟪y, b⟫ₚ)
  have hc : 0 < c := by
    dsimp [c]
    refine div_pos_of_neg_of_neg hβ_neg ?_
    exact mul_neg_of_pos_of_neg (show (0 : 𝕜) < 2 by norm_num) hy_neg
  have hcy : ⟪c • y, b⟫ₚ ≤ β := hβ _ (hK.smul_mem hc hy)
  have hmul : c * ⟪y, b⟫ₚ ≤ β := by
    simpa using hcy
  have hcalc : (2 : 𝕜) * (c * ⟪y, b⟫ₚ) = β := by
    have htwo_ne : (2 : 𝕜) ≠ 0 := by norm_num
    have hy_ne : ⟪y, b⟫ₚ ≠ (0 : 𝕜) := hy_neg.ne
    have hden_ne : (2 : 𝕜) * ⟪y, b⟫ₚ ≠ 0 := mul_ne_zero htwo_ne hy_ne
    calc
      (2 : 𝕜) * (c * ⟪y, b⟫ₚ) = (β / ((2 : 𝕜) * ⟪y, b⟫ₚ) * ((2 : 𝕜) * ⟪y, b⟫ₚ)) := by
        dsimp [c]
        ring
      _ = β * (((2 : 𝕜) * ⟪y, b⟫ₚ)⁻¹ * ((2 : 𝕜) * ⟪y, b⟫ₚ)) := by
        rw [div_eq_mul_inv]
        ring
      _ = β := by rw [inv_mul_cancel₀ hden_ne, mul_one]
  have hβ_le_twoβ : β ≤ (2 : 𝕜) * β := by
    nlinarith [hmul, hcalc]
  have hβ_nonneg' : (0 : 𝕜) ≤ β := by nlinarith [hβ_le_twoβ]
  exact (not_le_of_gt hβ_neg) hβ_nonneg'

end IsCone

end PairingLinearOrderedField

namespace IsCone

variable [LT 𝕜] [Zero 𝕜] [AddCommMonoid E] [DistribSMul 𝕜 E]
variable {ι : Type*}

/-- A finite Minkowski sum of cones is again a cone. This is the primitive operational finite-sum
API; the `Fintype`-indexed theorem below is its `Finset.univ` specialization. -/
theorem finset_sum {s : Finset ι} {K : ι → Set E} (hK : ∀ i, i ∈ s → IsCone 𝕜 (K i)) :
    IsCone 𝕜 (∑ i ∈ s, K i) := by
  intro c hc x hx
  rw [Set.mem_finset_sum] at hx ⊢
  rcases hx with ⟨g, hg, rfl⟩
  exact ⟨fun i ↦ c • g i, fun {i} hi ↦ (hK i hi) hc (hg hi), by
    simpa using
      (show ∑ i ∈ s, c • g i = c • ∑ i ∈ s, g i from Finset.smul_sum.symm)⟩

variable [Fintype ι]

/-- A finite Minkowski sum of cones is again a cone. -/
theorem fintype_sum {K : ι → Set E} (hK : ∀ i, IsCone 𝕜 (K i)) :
    IsCone 𝕜 (∑ i, K i) := by
  simpa using
    (finset_sum (fun i _ ↦ hK i) : IsCone 𝕜 (∑ i ∈ (Finset.univ : Finset ι), K i))

end IsCone

end Set

namespace ConvexCone

variable {R : Type v} {E : Type u} [Semiring R] [PartialOrder R] [AddCommMonoid E] [SMul R E]

/-- Every bundled convex cone is a cone in the sense of Definition 2.5.9 after forgetting additive
closure. -/
theorem isCone (C : ConvexCone R E) : Set.IsCone R (C : Set E) := by
  intro c hc x hx
  exact C.smul_mem hc hx

end ConvexCone

/-! ### Definition_2_5_10 (from Chap01) -/
open scoped Pointwise

universe u v

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.5.10 identifies convex cones in `ℝ^n` as subsets that are both
  cones and convex, so the primary public surface is the unbundled subset predicate
  `Set.IsConvexCone R K`.
- `core/canonical`: the bundled owner abstraction is `ConvexCone R E`, and its canonical owner
  construction on subsets is `ConvexCone.hull R K`.
- `bridge/view`: `Set.IsCone.hull_eq` and `Set.IsConvexCone.hull_eq_iff` connect the
  source-facing subset predicate to the bundled owner.
- Primitive data vs derived API: the source-facing owner is `Set.IsConvexCone R K`, while the
  primitive bridge into the bundled owner uses the raw cone data `Set.IsCone R K` together with
  additive closure. The convex-facing hull fixed-point statements are then derived API.
- Domain-style sampling used here: the chapter owner `Set.IsCone` from Definition 2.5.9 together
  with mathlib's `ConvexCone R E`, `ConvexCone.hull`, `ConvexCone.hull_le_iff`,
  `ConvexCone.convex`, and the chapter bridge `ConvexCone.isCone`. These confirm that there is no
  upstream set-level owner beyond the conjunction itself, while the bundled owner remains the
  right target for companion bridge lemmas.
- Layer target: `source-facing` for the numbered item itself, with `bridge/view` companion lemmas
  for the bundled hull.
-/

section SourceFacing

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set

/-- Definition 2.5.10: a subset is a convex cone if it is both a cone and convex. This keeps the
textbook subset-level notion as the main public surface with a short owner name. -/
def IsConvexCone (R : Type v) [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommMonoid E] [SMul R E] (K : Set E) : Prop :=
  Set.IsCone R K ∧ Convex R K

@[simp] theorem isConvexCone_iff (K : Set E) :
    IsConvexCone R K ↔ Set.IsCone R K ∧ Convex R K :=
  Iff.rfl

namespace IsConvexCone

theorem isCone {K : Set E} (hK : Set.IsConvexCone R K) : Set.IsCone R K :=
  hK.1

theorem convex {K : Set E} (hK : Set.IsConvexCone R K) : Convex R K :=
  hK.2

end IsConvexCone
end Set

end SourceFacing

section PrimitiveHullBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set.IsCone

/-- A cone with additive closure is fixed by the canonical owner hull. This is the primitive
set-level bridge to the bundled `ConvexCone` owner. -/
theorem hull_eq {K : Set E} (hK : Set.IsCone R K)
    (hadd : K + K ⊆ K) :
    (ConvexCone.hull R K : Set E) = K := by
  let C : ConvexCone R E := {
    carrier := K
    smul_mem' := fun _ hc _ hx ↦ hK.smul_mem hc hx
    add_mem' := fun {_} hx {_} hy ↦ hadd (Set.add_mem_add hx hy)
  }
  simpa [C] using
    congrArg (fun D : ConvexCone R E ↦ (D : Set E)) (ConvexCone.gi.l_u_eq C)

/-- Primitive owner-level fixed-point criterion for `ConvexCone.hull`: a set is fixed by the hull
exactly when it is both a cone and closed under pointwise set addition. -/
theorem hull_eq_iff (K : Set E) :
    (ConvexCone.hull R K : Set E) = K ↔ Set.IsCone R K ∧ K + K ⊆ K := by
  constructor
  · intro hHull
    refine ⟨by simpa [hHull] using (ConvexCone.hull R K).isCone, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hxHull : x ∈ (ConvexCone.hull R K : Set E) := by simpa [hHull] using hx
    have hyHull : y ∈ (ConvexCone.hull R K : Set E) := by simpa [hHull] using hy
    have hzHull : x + y ∈ (ConvexCone.hull R K : Set E) :=
      (ConvexCone.hull R K).add_mem hxHull hyHull
    simpa [hHull] using hzHull
  · intro hK
    exact hK.1.hull_eq hK.2

end Set.IsCone

end PrimitiveHullBridge

section PrimitiveSourceBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [SMul R E]

namespace Set.IsConvexCone

/-- Primitive source-facing bridge: if a source-facing convex cone is also known to be closed under
set addition, then it is fixed by the canonical owner hull. This keeps the hull fixed-point API at
the weaker semiring layer when additive closure is available as primitive data. -/
theorem hull_eq_of_add_subset {K : Set E} (hK : Set.IsConvexCone R K)
    (hadd : K + K ⊆ K) :
    (ConvexCone.hull R K : Set E) = K := by
  exact hK.isCone.hull_eq hadd

end Set.IsConvexCone

end PrimitiveSourceBridge

section BundledBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

namespace ConvexCone

/-- Every bundled convex cone is source-facing convex after forgetting to its carrier set. -/
theorem isConvexCone (C : ConvexCone R E) : Set.IsConvexCone R (C : Set E) := by
  refine ⟨C.isCone, ?_⟩
  refine C.isCone.convex_of_add_subset ?_
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  exact C.add_mem hx hy

end ConvexCone

end BundledBridge

section WeakHullBridge

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [MulActionWithZero R E]

namespace Set.IsConvexCone

/-- Any set fixed by the canonical owner hull is source-facing convex-cone valued. This direction
works at the weaker semiring/action layer, without the division-semiring assumptions used in
`Set.IsConvexCone.hull_eq`. -/
theorem of_hull_eq {K : Set E} (hK : (ConvexCone.hull R K : Set E) = K) :
    Set.IsConvexCone R K := by
  rcases (Set.IsCone.hull_eq_iff (R := R) K).1 hK with ⟨hCone, hAdd⟩
  exact ⟨hCone, hCone.convex_of_add_subset hAdd⟩

end Set.IsConvexCone

end WeakHullBridge

section Bridge

variable {R : Type v} [DivisionSemiring R] [PartialOrder R]
variable [PosMulReflectLT R] [ZeroLEOneClass R] [AddLeftMono R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

namespace Set.IsConvexCone

/-- A source-facing convex cone is closed under addition. -/
theorem add_mem {K : Set E} (hK : Set.IsConvexCone R K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : x + y ∈ K := by
  exact (hK.isCone.convex_iff_add_subset.mp hK.convex) (Set.add_mem_add hx hy)

/-- A source-facing convex cone is closed under set addition. -/
theorem add_subset {K : Set E} (hK : Set.IsConvexCone R K) :
    K + K ⊆ K := by
  exact hK.isCone.convex_iff_add_subset.mp hK.convex

/-- A source-facing convex cone is fixed by the canonical owner hull. -/
theorem hull_eq {K : Set E} (hK : Set.IsConvexCone R K) :
    (ConvexCone.hull R K : Set E) = K := by
  exact hK.hull_eq_of_add_subset hK.add_subset

/-- Owner-level canonical bridge: a subset is a convex cone exactly when it is fixed by the
`ConvexCone` hull. -/
theorem hull_eq_iff (K : Set E) :
    Set.IsConvexCone R K ↔ (ConvexCone.hull R K : Set E) = K := by
  constructor
  · intro hK
    exact hK.hull_eq
  · intro hK
    exact Set.IsConvexCone.of_hull_eq hK

end Set.IsConvexCone

namespace Set.IsCone

/-- A convex cone is closed under addition. -/
theorem add_mem {K : Set E} (hK : Set.IsCone R K) (hconv : Convex R K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : x + y ∈ K := by
  exact (hK.convex_iff_add_subset.mp hconv) (Set.add_mem_add hx hy)

/-- A cone that is convex is closed under set addition. -/
theorem add_subset {K : Set E} (hK : Set.IsCone R K) (hconv : Convex R K) :
    K + K ⊆ K := by
  exact hK.convex_iff_add_subset.mp hconv

/-- A cone that is convex is fixed by the canonical owner hull. -/
theorem hull_eq_of_convex {K : Set E} (hK : Set.IsCone R K) (hconv : Convex R K) :
    (ConvexCone.hull R K : Set E) = K := by
  exact hK.hull_eq (hK.add_subset hconv)

end Set.IsCone

end Bridge

/-! ### Definition_2_5_11 (from Chap01) -/
namespace Rockafellar

/- Source notation for the canonical nonnegative orthant as a set in an ordered module. -/
scoped notation:max "orthant[" 𝕜 "](" M ")" => (ConvexCone.positive 𝕜 M : Set M)

end Rockafellar

open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.5.11 names the nonnegative cone of an ordered ambient space.
- `core/canonical`: the source-facing owner is the set-level orthant notation `orthant[𝕜](M)`;
  the bundled cone `ConvexCone.positive 𝕜 M` is retained as the upstream bridge owner.
- Primitive data vs derived API: the ordered-module structure and set-level orthant are primitive;
  bridges to `ConvexCone.positive` are derived API.
- Domain-style sampling: `orthant[𝕜](M)`, `ConvexCone.positive`, and `ConvexCone.mem_positive`.
- Layer target: `core/canonical`; concrete coordinate models belong in downstream bridge files.
-/

/- Definition 2.5.11: after equipping the ambient space with the relevant order, the
non-negative orthant cone is the canonical positive cone. -/
#check ConvexCone.positive

section SourceFacing

variable {𝕜 M : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M]

/-- Canonical short owner theorem: the orthant is the upper set `Set.Ici 0`. -/
@[simp] theorem orthant_eq_Ici :
    orthant[𝕜](M) = Set.Ici (0 : M) :=
  rfl

/-- Canonical short membership theorem for `orthant[𝕜](M)`. -/
@[simp] theorem mem_orthant_iff {x : M} :
    x ∈ orthant[𝕜](M) ↔ 0 ≤ x :=
  Iff.rfl

end SourceFacing

/-! ### Definition_2_5_12 (from Chap01) -/
open scoped Pointwise

namespace Rockafellar

/- Source notation for the canonical positive orthant as the interior of the nonnegative orthant. -/
scoped notation:max "orthant⁺[" 𝕜 "](" M ")" => interior (orthant[𝕜](M))

end Rockafellar

open scoped Rockafellar
/-
Source/core/bridge triage:
- `source-facing`: Definition 2.5.12 names the positive orthant as the interior of the
  nonnegative cone.
- `core/canonical`: the owner surface is the short notation `orthant⁺[𝕜](M)`, definitionally
  equal to `interior (orthant[𝕜](M))` at the abstract ordered topological module layer.
- Primitive data vs derived API: `orthant[𝕜](M)` and topological interior are primitive;
  cone/convex facts below are derived bridge API, with any `ConvexCone.positive` references
  kept inside bridge proofs.
- Domain-style sampling: `orthant[𝕜](M)`, `ConvexCone.smul_mem`, and `interior`.
- Layer target: `core/canonical`; concrete coordinate models and coordinatewise positivity tests
  belong in downstream bridge files.
-/

section PositiveOrthantMembership

variable {𝕜 M : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]

/-- Definition 2.5.12: bridge form of positive-orthant membership through the concrete upper-set model. -/
theorem mem_positiveOrthant_iff_mem_interior_Ici {x : M} :
    x ∈ orthant⁺[𝕜](M) ↔
      x ∈ interior (Set.Ici (0 : M)) := by
  -- Unfold the positive-orthant owner once and rewrite through Definition 2.5.11.
  rw [orthant_eq_Ici]

end PositiveOrthantMembership

section PositiveOrthantCone

variable {𝕜 M : Type*} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]

variable [ContinuousConstSMul 𝕜 M]

/-- Helper for Definition 2.5.12: positive scalar multiplication preserves the nonnegative orthant. -/
private theorem smul_orthant_subset {c : 𝕜} (hc : 0 < c) :
    c • orthant[𝕜](M) ⊆ orthant[𝕜](M) := by
  -- Route correction: keep the interior-of-orthant owner and remove the parser-invalid `omit`
  -- wrapper; the carrier-level cone argument is unchanged.
  -- Reduce membership in the scalar image to a point of the underlying positive cone.
  rintro _ ⟨y, hy, rfl⟩
  exact (ConvexCone.positive 𝕜 M).smul_mem hc hy

/-- Helper for Definition 2.5.12: the interior of the orthant is stable under positive scaling. -/
private theorem smul_mem_positiveOrthant {c : 𝕜} (hc : 0 < c) {x : M}
    (hx : x ∈ orthant⁺[𝕜](M)) :
    c • x ∈ orthant⁺[𝕜](M) := by
  -- First place the scaled point in the scaled interior.
  have hx_smul : c • x ∈ c • orthant⁺[𝕜](M) :=
    Set.smul_mem_smul_set hx
  have hx_interior : c • x ∈ interior (c • orthant[𝕜](M)) := by
    rw [interior_smul₀ (α := M) (G₀ := 𝕜) (c := c) (ne_of_gt hc)]
    exact hx_smul
  -- Then move back to the original orthant using monotonicity of interior.
  exact interior_mono (smul_orthant_subset hc) hx_interior

/-- The positive orthant is a cone at the canonical owner level. -/
theorem isCone_positiveOrthant :
    Set.IsCone 𝕜 (orthant⁺[𝕜](M)) := by
  -- Cone closure reduces to positive-scalar closure on the carrier set.
  refine (Set.isCone_iff_forall_pos_smul_subset (𝕜 := 𝕜) (K := orthant⁺[𝕜](M))).2 ?_
  intro c hc x hx
  -- Rewrite the scaled interior back to an interior of a scaled carrier set.
  have hx_interior : x ∈ interior (c • orthant[𝕜](M)) := by
    rwa [← interior_smul₀ (α := M) (G₀ := 𝕜) (c := c) (ne_of_gt hc)] at hx
  -- Then shrink along the carrier-level orthant inclusion.
  exact interior_mono (smul_orthant_subset hc) hx_interior

end PositiveOrthantCone

section PositiveOrthantConvex

variable {𝕜 M : Type*} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]

variable [ContinuousConstSMul 𝕜 M] [ContinuousConstVAdd M M]

/-- Helper for Definition 2.5.12: the nonnegative orthant is closed under addition. -/
private theorem add_orthant_subset :
    orthant[𝕜](M) + orthant[𝕜](M) ⊆ orthant[𝕜](M) := by
  -- Route correction: keep the additive proof at the carrier level and only transport to
  -- interiors afterward, instead of changing the source-faithful owner.
  -- Expand membership in the Minkowski sum and use addition in the ambient positive cone.
  rintro _ ⟨u, hu, v, hv, rfl⟩
  exact (ConvexCone.positive 𝕜 M).add_mem hu hv

/-- Helper for Definition 2.5.12: the interior of the orthant is closed under addition. -/
private theorem add_mem_positiveOrthant {x y : M}
    (hx : x ∈ orthant⁺[𝕜](M))
    (hy : y ∈ orthant⁺[𝕜](M)) :
    x + y ∈ orthant⁺[𝕜](M) := by
  -- Add an interior point to a point of the orthant to reach the interior of the Minkowski sum.
  have hxy : x + y ∈ interior (orthant[𝕜](M) + orthant[𝕜](M)) := by
    exact subset_interior_add_right (Set.add_mem_add (interior_subset hx) hy)
  -- The Minkowski sum sits back inside the orthant because the orthant is additive.
  have hsubset : interior (orthant[𝕜](M) + orthant[𝕜](M)) ⊆ orthant⁺[𝕜](M) :=
    interior_mono add_orthant_subset
  exact hsubset hxy

/-- Helper for Definition 2.5.12: scalar closure of the positive orthant in the exact field shape
required by `ConvexCone`. -/
private theorem positiveOrthant_smul_mem_field :
    ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ orthant⁺[𝕜](M) → c • x ∈ orthant⁺[𝕜](M) := by
  -- Reuse the owner-level scalar-stability bridge from the cone section.
  intro c hc x hx
  exact smul_mem_positiveOrthant hc hx

/-- Helper for Definition 2.5.12: additive closure of the positive orthant in the exact field shape
required by `ConvexCone`. -/
private theorem positiveOrthant_add_mem_field :
    ∀ ⦃x : M⦄, x ∈ orthant⁺[𝕜](M) → ∀ ⦃y : M⦄, y ∈ orthant⁺[𝕜](M) →
      x + y ∈ orthant⁺[𝕜](M) := by
  -- Reuse the owner-level additive-stability bridge for the cone packaging step.
  intro x hx y hy
  exact add_mem_positiveOrthant hx hy

/-- Helper for Definition 2.5.12: the positive orthant carries the canonical convex-cone
structure induced by the established scalar and additive closure lemmas. -/
private def positiveOrthantCone : ConvexCone 𝕜 M :=
  { carrier := orthant⁺[𝕜](M)
    smul_mem' := positiveOrthant_smul_mem_field
    add_mem' := positiveOrthant_add_mem_field }

/-- The positive orthant is convex after forgetting to its carrier set. -/
theorem convex_positiveOrthant :
    Convex 𝕜 (orthant⁺[𝕜](M)) := by
  -- Package the established scalar and additive closure into the canonical local cone owner.
  -- A convex cone has a convex carrier set.
  simpa [positiveOrthantCone] using (ConvexCone.convex (positiveOrthantCone : ConvexCone 𝕜 M))

end PositiveOrthantConvex

/-! ### Definition_2_5_13 (from Chap01) -/
open ConvexCone
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.5.13 identifies comparison notation `x ≥ x'` with the condition
  that the difference `x - x'` lies in the nonnegative cone.
- `core/canonical`: the primitive owner is the order-theoretic lemma `sub_nonneg` on additive
  ordered groups.
- `bridge/view`: the nonnegative orthant carrier statement is a thin bridge via
  `ConvexCone.mem_positive`, surfaced with chapter notation `orthant[𝕜](M)`.
- `bridge/view`: no coordinate model is introduced here; concrete coordinatewise readings belong
  downstream from the ordered-module statement.
-- Primitive data vs derived API: additive ordered-group comparison data are primitive; the
  orthant-membership statement below is derived bridge API.
- Domain-style sampling: `orthant[𝕜](M)`, `ConvexCone.mem_positive`, and `sub_nonneg`.
- Layer target: `core/canonical`.
-/

/- Definition 2.5.13: after abstracting the ambient coordinate order, the primitive comparison
owner is `sub_nonneg`, with orthant membership as a bridge view. -/
#check sub_nonneg
#check ConvexCone.positive
#check ConvexCone.mem_positive

section OrderedComparison

variable {E : Type*}

/-- Definition 2.5.13 (primitive form): in an ordered additive group, endpoint comparison is
equivalent to nonnegativity of the difference. -/
@[simp] theorem ge_iff_sub_nonneg
    [AddGroup E] [Preorder E] [AddRightMono E]
    {x x' : E} :
    x ≥ x' ↔ 0 ≤ x - x' := by
  exact (sub_nonneg (a := x) (b := x')).symm

/-- Definition 2.5.13 (set-owner primitive form): endpoint comparison is exactly membership of
the difference in `Set.Ici 0`. -/
@[simp] theorem sub_mem_Ici_zero_iff_ge
    [AddGroup E] [Preorder E] [AddRightMono E]
    {x x' : E} :
    x - x' ∈ Set.Ici (0 : E) ↔ x ≥ x' := by
  rw [Set.mem_Ici]
  exact (ge_iff_sub_nonneg (x := x) (x' := x')).symm

end OrderedComparison

section OrthantComparison

variable {R E : Type*}

/-- Definition 2.5.13: in any ordered additive module, membership of a difference in the
nonnegative orthant is equivalent to endpoint comparison. -/
@[simp] theorem sub_mem_orthant_iff
    [Semiring R] [PartialOrder R]
    [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    {x x' : E} :
    x - x' ∈ orthant[R](E) ↔ x ≥ x' := by
  rw [orthant_eq_Ici]
  exact sub_mem_Ici_zero_iff_ge (x := x) (x' := x')

/-- Definition 2.5.13: rewriting comparison as orthant membership for a difference
vector. -/
theorem ge_iff_sub_mem_orthant
    [Semiring R] [PartialOrder R]
    [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    {x x' : E} :
    x ≥ x' ↔ x - x' ∈ orthant[R](E) := by
  exact (sub_mem_orthant_iff (x := x) (x' := x')).symm

end OrthantComparison

/-! ### Proposition_2_5_14 (from Chap01) -/
universe u v

section

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.5.14 states that every linear subspace of a module is a convex
  cone, so the chapter surface should use `Set.IsConvexCone`.
- `core/canonical`: the canonical owner abstraction for linear subspaces is
  `Submodule.toConvexCone`.
- `bridge/view`: the source-facing set-level statement is obtained by forgetting the bundled owner
  with `ConvexCone.isConvexCone`.
- Primitive data vs derived API: additive and scalar closure are primitive at the bundled
  `ConvexCone` owner; the chapter statement is the derived unbundled view.
- Layer target: keep `Submodule.toConvexCone` as the owner-level root and expose
  `Set.IsConvexCone` only as the source-facing bridge.
-/

namespace Submodule

/-- Helper for Proposition 2.5.14: forgetting a submodule's canonical bundled cone gives a
source-facing convex cone. -/
theorem toConvexCone_isConvexCone (S : Submodule R E) :
    Set.IsConvexCone R (S.toConvexCone : Set E) := by
  -- The bundled convex cone already carries the required source-facing property.
  simpa using (S.toConvexCone.isConvexCone)

/-- Proposition 2.5.14: every linear subspace is a convex cone in the chapter's source-facing
set-level sense. -/
theorem isConvexCone (S : Submodule R E) : Set.IsConvexCone R (S : Set E) := by
  -- Forget the bundled cone structure and identify its carrier with the submodule itself.
  simpa using S.toConvexCone_isConvexCone

end Submodule

end

/-! ### Proposition_2_5_15 (from Chap01) -/
open scoped Pointwise
open scoped Rockafellar

/- 
Source/core/bridge triage:
- `source-facing`: Proposition 2.5.15 asserts that the two orthants introduced just above are
  convex cones in the textbook sense.
- `core/canonical`: the nonnegative orthant clause belongs at the generic ordered-module owner
  layer `orthant[𝕜](M)`; for the positive orthant this file works on the canonical owner surface
  `orthant⁺[𝕜](M)`.
- `bridge/view`: both clauses are set-level `Set.IsConvexCone` statements, proved from the bundled
  owner for `orthant[𝕜](M)` and from Definition 2.5.12 for `orthant⁺[𝕜](M)`.
- Primitive data vs derived API: the orthants themselves are already defined; the convex-cone
  claims are derived from the existing carrier descriptions, cone closure, and convexity theorems.
- Domain-style sampling: `ConvexCone.positive`, `ConvexCone.mem_positive`, `Set.IsCone.hull_eq`,
  `Set.IsConvexCone.hull_eq_iff`, `mem_orthant_iff`, and
  `mem_positiveOrthant_iff_mem_interior_Ici`.
- Layer target: both clauses are now `source-facing` set-level convex-cone statements through the
  short owner `Set.IsConvexCone`; clause (1) is scalar/ambient-generalized, and clause (2) is
  implemented at the same abstract ordered topological module layer as Definition 2.5.12.
-/

section Orthant

variable {𝕜 M : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module 𝕜 M] [PosSMulMono 𝕜 M]

/- Proposition 2.5.15 (1): the non-negative orthant is a convex cone at the canonical scalar and
ambient owner layer. -/
namespace Set.IsConvexCone

/-- Proposition 2.5.15: the nonnegative orthant is a convex cone. -/
theorem orthant :
    Set.IsConvexCone 𝕜 (orthant[𝕜](M)) := by
  -- Transport the bundled positive cone result directly to the orthant carrier.
  simpa using (ConvexCone.positive 𝕜 M).isConvexCone

end Set.IsConvexCone

/-- Helper for Proposition 2.5.15: expose the nonnegative-orthant clause without reopening the
owner namespace. -/
theorem orthant_isConvexCone :
    Set.IsConvexCone 𝕜 (orthant[𝕜](M)) := by
  -- Reuse the owner theorem verbatim through the source-facing wrapper name.
  simpa using (Set.IsConvexCone.orthant (𝕜 := 𝕜) (M := M))

end Orthant

section PositiveOrthant

variable {𝕜 : Type*} [DivisionSemiring 𝕜] [PartialOrder 𝕜]
variable {M : Type*} [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
variable [Module 𝕜 M] [PosSMulMono 𝕜 M] [TopologicalSpace M]
variable [ContinuousConstSMul 𝕜 M] [ContinuousConstVAdd M M]

/- Proposition 2.5.15 (2): the positive orthant is a convex cone at the abstract owner layer. -/
namespace Set.IsConvexCone

/-- Proposition 2.5.15: the positive orthant is a convex cone. -/
theorem positiveOrthant :
    Set.IsConvexCone 𝕜 (orthant⁺[𝕜](M)) := by
  -- Combine the previously proved cone and convexity facts at the set owner level.
  exact ⟨isCone_positiveOrthant, convex_positiveOrthant⟩

end Set.IsConvexCone

/-- Helper for Proposition 2.5.15: expose the positive-orthant clause without reopening the
owner namespace. -/
theorem positiveOrthant_isConvexCone :
    Set.IsConvexCone 𝕜 (orthant⁺[𝕜](M)) := by
  -- Reuse the owner theorem verbatim through the source-facing wrapper name.
  simpa using (Set.IsConvexCone.positiveOrthant (𝕜 := 𝕜) (M := M))

end PositiveOrthant
