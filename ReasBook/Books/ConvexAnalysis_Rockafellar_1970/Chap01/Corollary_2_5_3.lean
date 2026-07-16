import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

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
