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

/-- Lemma 29.44.2 (1): a morphism of schemes is integral if and only if there exists an affine
open covering of the target such that every preimage is affine and the induced map on global
sections is integral. -/
theorem isIntegralHom_iff_exists_affineOpenCover :
    IsIntegralHom f ↔
      ∃ (ι : Type v) (U : ι → S.affineOpens),
        iSup (fun i ↦ (U i : S.Opens)) = ⊤ ∧
          ∀ i,
            IsAffine (f ⁻¹ᵁ U i) ∧
              (CommRingCat.Hom.hom (Scheme.Hom.appTop (f ∣_ U i))).IsIntegral := by
  sorry

/-- Lemma 29.44.2 (2):
covering of the target such that each restricted morphism over a member of the cover is
integral. -/
theorem isIntegralHom_iff_exists_openCover :
    IsIntegralHom f ↔
      ∃ (ι : Type v) (U : ι → S.Opens),
        iSup U = ⊤ ∧ ∀ i, IsIntegralHom (f ∣_ U i) := by
  constructor
  · intro hf
    refine ⟨S.affineCover.I₀, fun i ↦ (S.affineCover.f i).opensRange,
      S.affineCover.iSup_opensRange, ?_⟩
    intro i
    exact IsZariskiLocalAtTarget.restrict (P := @IsIntegralHom) hf _
  · rintro ⟨ι, U, hU, hint⟩
    exact (isIntegralHom_iff_forall_restrict (f := f) U hU).2 hint

/-- Lemma 29.44.2 (3): if a morphism of schemes is integral, then its restriction to any open
subscheme of the target is integral. -/
theorem isIntegralHom_restrict (U : S.Opens) [IsIntegralHom f] :
    IsIntegralHom (f ∣_ U) :=
  inferInstance

end

end AlgebraicGeometry
