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
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (@IsIntegralHom) f U hU)

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
    (HasAffineProperty.iff_of_iSup_eq_top (@IsIntegralHom) f U hU)

/-- Lemma 29.44.2 (1): a morphism of schemes is integral if and only if there exists an affine
open covering of the target such that every preimage is affine and the induced map on global
sections is integral. -/
@[stacks 01WM]
theorem isIntegralHom_iff_exists_affineOpenCover :
    IsIntegralHom f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          IsAffine (f ⁻¹ᵁ (𝒰.U i)) ∧
            (CommRingCat.Hom.hom
              (Scheme.Hom.appTop (f ∣_ 𝒰.U i))).IsIntegral := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover, ?_⟩
    simpa using
      (isIntegralHom_iff_forall_affineOpen f S.affineOpenCover.U
        (by simpa using S.affineOpenCover.iSup_opensRange)).1 hf
  · rintro ⟨𝒰, h𝒰⟩
    exact
      (isIntegralHom_iff_forall_affineOpen f 𝒰.U
        (by simpa using 𝒰.iSup_opensRange)).2 <|
        by simpa using h𝒰

/-- Lemma 29.44.2 (2): a morphism of schemes is integral if and only if there exists an open
covering of the target such that each restricted morphism over a member of the cover is
integral. -/
@[stacks 01WM]
theorem isIntegralHom_iff_exists_openCover :
    IsIntegralHom f ↔
      ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, IsIntegralHom (f ∣_ 𝒰.U i) := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover.openCover, ?_⟩
    simpa using
      (isIntegralHom_iff_forall_restrict f S.affineOpenCover.openCover.U
        (by simpa using S.affineOpenCover.openCover.isOpenCover_opensRange.iSup_eq_top)).1 hf
  · rintro ⟨𝒰, h𝒰⟩
    exact
      (isIntegralHom_iff_forall_restrict f 𝒰.U
        (by simpa using 𝒰.isOpenCover_opensRange.iSup_eq_top)).2 h𝒰

/-- Lemma 29.44.2 (3): if a morphism of schemes is integral, then its restriction to any open
subscheme of the target is integral. -/
@[stacks 01WM]
theorem isIntegralHom_restrict (hf : IsIntegralHom f) (U : S.Opens) :
    IsIntegralHom (f ∣_ U) := by
  letI := hf
  infer_instance

end

end AlgebraicGeometry
