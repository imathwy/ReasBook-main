import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_5_16
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

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
