import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall:
-- `lean_leansearch` recalled the canonical affine-open basis theorem
-- `AlgebraicGeometry.Scheme.isBasis_affineOpens`.
-- Local Chapter 29 precedent already expresses the relative affine-local condition through affine
-- opens `U ⊆ X`, `V ⊆ S` with `U ≤ f ⁻¹ᵁ V`, so the source-faithful statement here is the
-- corresponding relative basis theorem on the source.

/-- Remark 29.32.6: the affine opens `U ⊆ X` for which there exists an affine open `V ⊆ S` with
`U ≤ f ⁻¹ᵁ V` form a basis for the topology on `X`. This is the basis on which the remark
describes the affine-open construction of `\Omega_{X/S}`. -/
@[stacks 01UU]
theorem isBasis_affineOpens_mappingIntoAffineOpen :
    TopologicalSpace.Opens.IsBasis
      {U : X.Opens | ∃ _ : IsAffineOpen U, ∃ V : S.Opens, IsAffineOpen V ∧ U ≤ f ⁻¹ᵁ V} := sorry

end AlgebraicGeometry
