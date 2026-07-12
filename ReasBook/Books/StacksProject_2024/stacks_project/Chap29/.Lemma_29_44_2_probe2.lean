import Mathlib.AlgebraicGeometry.Morphisms.Integral

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem isIntegralHom_iff_forall_restrict
    {ι : Type v} (U : ι → S.Opens) (hU : iSup U = ⊤) :
    IsIntegralHom f ↔ ∀ i, IsIntegralHom (f ∣_ U i) := by
  simpa using
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f) U hU)

theorem isIntegralHom_iff_forall_affineOpen
    {ι : Type v} (U : ι → S.affineOpens)
    (hU : iSup (fun i ↦ (U i : S.Opens)) = ⊤) :
    IsIntegralHom f ↔
      ∀ i,
        IsAffine (f ⁻¹ᵁ U i) ∧
          (CommRingCat.Hom.hom (Scheme.Hom.appTop (f ∣_ U i))).IsIntegral := by
  simpa [isIntegralHom_iff] using
    (HasAffineProperty.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f) U hU)

theorem isIntegralHom_iff_exists_affineOpenCover :
    IsIntegralHom f ↔
      ∃ (ι : Type v) (U : ι → S.affineOpens),
        iSup (fun i ↦ (U i : S.Opens)) = ⊤ ∧
          ∀ i,
            IsAffine (f ⁻¹ᵁ U i) ∧
              (CommRingCat.Hom.hom (Scheme.Hom.appTop (f ∣_ U i))).IsIntegral := by
  constructor
  · intro hf
    let U : S.affineCover.I₀ → S.affineOpens :=
      fun i ↦ ⟨(S.affineCover.f i).opensRange, isAffineOpen_opensRange _⟩
    refine ⟨S.affineCover.I₀, U, S.affineCover.iSup_opensRange, ?_⟩
    exact (isIntegralHom_iff_forall_affineOpen f U S.affineCover.iSup_opensRange).1 hf
  · rintro ⟨ι, U, hU, hint⟩
    exact (isIntegralHom_iff_forall_affineOpen (f := f) U hU).2 hint

theorem isIntegralHom_iff_exists_openCover :
    IsIntegralHom f ↔
      ∃ (ι : Type v) (U : ι → S.Opens),
        iSup U = ⊤ ∧ ∀ i, IsIntegralHom (f ∣_ U i) := by
  sorry

theorem isIntegralHom_restrict (U : S.Opens) [IsIntegralHom f] :
    IsIntegralHom (f ∣_ U) :=
  inferInstance

end

end AlgebraicGeometry
