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
