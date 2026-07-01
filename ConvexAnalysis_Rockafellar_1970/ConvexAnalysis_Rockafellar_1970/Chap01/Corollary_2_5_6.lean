import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_5_16
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

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
