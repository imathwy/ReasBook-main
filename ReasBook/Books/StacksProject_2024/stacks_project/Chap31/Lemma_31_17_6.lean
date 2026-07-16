import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_78_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_48_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall note: `lean_leansearch` was rate-limited (HTTP 429) in this environment, so the
-- owner/API choice was checked against mathlib's `PolynomialLaw`, `Algebra.norm`, and
-- `Algebra.norm_localization`, together with the current scheme affine-open API
-- `IsAffineHom` / `Scheme.Hom.app`.

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ)

/-- The ring of sections on the affine-open preimage of `U` is canonically a
`Γ(Y, U)`-algebra via the restriction map attached to `π`. -/
instance preimageSectionAlgebra (U : Y.Opens) :
    Algebra (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) :=
  (π.app U).hom.toAlgebra

/-- A norm on `π : X ⟶ Y` is recorded on affine opens as an affine-local family of polynomial
laws on sections. -/
abbrev Norm (π : X ⟶ Y) :=
  ∀ (U : Y.Opens) (_ : IsAffineOpen U),
    Γ(X, π ⁻¹ᵁ U) →ₚₗ[Γ(Y, U)] Γ(Y, U)

/-- A degree-`d` norm family on `π : X ⟶ Y` has the canonical ground map on every affine open and
raises pulled-back scalars to the `d`th power. The arbitrary-base-change clause is carried by the
`PolynomialLaw` owner. -/
structure IsNorm (π : X ⟶ Y) (d : ℕ) (N : Norm π) : Prop where
  /-- The ground map of the affine-open polynomial law is the canonical algebra norm. -/
  ground_eq_norm :
    ∀ (U : Y.Opens) (hU : IsAffineOpen U),
      (N U hU).ground = Algebra.norm (Γ(Y, U))
  /-- The affine-open ground map has degree `d` on sections pulled back from the base. -/
  ground_algebraMap_pow :
    ∀ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)),
      (N U hU).ground (algebraMap (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) r) = r ^ d

/-- Lemma 31.17.6: for an affine morphism whose affine-open section rings are finite locally free
of constant rank `d ≥ 1`, there exists a canonical norm of degree `d`. Here the arbitrary
base-change clause is encoded by taking the norm on each affine open to be a `PolynomialLaw`. -/
theorem finiteLocallyFreeOfRank_on_affineOpens [IsFiniteLocallyFreeOfRank π d]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.FiniteLocallyFreeOfRank (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) d := by
  sorry

/-- Lemma 31.17.6: for a finite locally free morphism of constant rank `d ≥ 1`, there exists a
canonical norm of degree `d`. Here the arbitrary base-change clause is encoded by taking the norm
on each affine open to be a `PolynomialLaw`, and the affine-open section-ring rank statement is
recovered by `finiteLocallyFreeOfRank_on_affineOpens`. -/
theorem exists_norm_of_finiteLocallyFreeOfRank [IsFiniteLocallyFreeOfRank π d] (hd : 1 ≤ d) :
    ∃ N : Norm π, IsNorm π d N := sorry

end AlgebraicGeometry.Scheme
