import Mathlib.AlgebraicGeometry.Morphisms.Integral

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `AlgebraicGeometry.IsIntegralHom` is the canonical owner for integral
-- morphisms of schemes, and its affine-local / target-local interfaces already live in mathlib.
-- This file records the Stacks-project cover formulations as source-facing companion theorems.

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Restricting a scheme morphism to an open cover of the target detects integrality. -/
theorem isIntegralHom_iff_forall_restrict
    {ι : Type v} (U : ι → S.Opens) (hU : iSup U = ⊤) :
    IsIntegralHom f ↔ ∀ i, IsIntegralHom (f ∣_ U i) := by
  simpa using
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f) U hU)

/-- Restricting a scheme morphism to an affine open cover of the target detects integrality
through affineness of the preimage and integrality of the induced map on global sections. -/
theorem isIntegralHom_iff_forall_affineOpen
    {ι : Type v} (U : ι → S.affineOpens)
    (hU : iSup (fun i ↦ (U i : S.Opens)) = ⊤) :
    IsIntegralHom f ↔
      ∀ i,
        IsAffine (f ⁻¹ᵁ U i) ∧
          (CommRingCat.Hom.hom (Scheme.Hom.appTop (f ∣_ U i))).IsIntegral := by
  simpa [isIntegralHom_iff] using
    (HasAffineProperty.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f) U hU)

end

end AlgebraicGeometry
