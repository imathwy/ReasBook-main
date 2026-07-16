import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

/- Definition 31.13.6: given effective Cartier divisors `D₁` and `D₂` on a scheme `S`, their sum
is the closed subscheme corresponding to the product ideal sheaf
`\mathcal{I}_{D_1}\mathcal{I}_{D_2} \subset \mathcal{O}_S`. -/
/-- The sum of two effective Cartier divisors is the closed subscheme cut out by the product of
their ideal sheaves on each affine open. -/
abbrev effectiveCartierDivisorSum {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData) : X.IdealSheafData :=
  D₁ * D₂

@[simp] theorem effectiveCartierDivisorSum_eq {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData) :
    effectiveCartierDivisorSum D₁ D₂ = D₁ * D₂ :=
  rfl

/-- Backwards-compatible ideal-sheaf spelling for the divisor sum. -/
@[simp] theorem ideal_effectiveCartierDivisorSum {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData) :
    (effectiveCartierDivisorSum D₁ D₂).ideal = D₁.ideal * D₂.ideal :=
  rfl

/-- On affine opens, `effectiveCartierDivisorSum D₁ D₂` has section ideal
`D₁(U) * D₂(U)`. -/
@[simp] theorem effectiveCartierDivisorSum_ideal {X : Scheme.{u}}
    (D₁ D₂ : X.IdealSheafData) (U : X.affineOpens) :
    (effectiveCartierDivisorSum D₁ D₂).ideal U = D₁.ideal U * D₂.ideal U := by
  rfl

end AlgebraicGeometry
