import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_5_16
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2

-- Declarations for this item will be appended below by the statement pipeline.

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
