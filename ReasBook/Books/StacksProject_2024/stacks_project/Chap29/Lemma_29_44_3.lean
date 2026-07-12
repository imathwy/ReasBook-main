import Mathlib.AlgebraicGeometry.Morphisms.Finite

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

section

-- Semantic recall: `AlgebraicGeometry.IsFinite` is the canonical owner for finite morphisms of
-- schemes, and the target-local / affine-local detection lemmas below are source-facing
-- companions built directly on top of that owner.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Restricting a scheme morphism to an open cover of the target detects finiteness. -/
theorem isFinite_iff_forall_restrict
    {ι : Type v} (U : ι → S.Opens) (hU : iSup U = ⊤) :
    IsFinite f ↔ ∀ i, IsFinite (f ∣_ U i) := by
  simpa using
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (@IsFinite) f U hU)

/-- Restricting a scheme morphism to an affine open cover of the target detects finiteness through
affineness of the preimage and finiteness of the induced map on global sections. -/
theorem isFinite_iff_forall_affineOpen
    {ι : Type v} (U : ι → S.affineOpens)
    (hU : iSup (fun i ↦ (U i : S.Opens)) = ⊤) :
    IsFinite f ↔
      ∀ i,
        IsAffine (f ⁻¹ᵁ U i) ∧
          (CommRingCat.Hom.hom (Scheme.Hom.appTop (f ∣_ U i))).Finite := by
  simpa [isFinite_iff] using
    (HasAffineProperty.iff_of_iSup_eq_top (@IsFinite) f U hU)

/-- Lemma 29.44.3 (1): a morphism of schemes is finite if and only if there exists an affine open
covering of the target such that every preimage is affine and the induced map on global sections is
finite. -/
@[stacks 01WI]
theorem isFinite_iff_exists_affineOpenCover :
    IsFinite f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          IsAffine (f ⁻¹ᵁ 𝒰.U i) ∧
            (CommRingCat.Hom.hom
              (Scheme.Hom.appTop (f ∣_ 𝒰.U i))).Finite := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover, ?_⟩
    simpa using
      (isFinite_iff_forall_affineOpen f S.affineOpenCover.U
        (by simpa using S.affineOpenCover.iSup_opensRange)).1 hf
  · rintro ⟨𝒰, h𝒰⟩
    exact
      (isFinite_iff_forall_affineOpen f 𝒰.U
        (by simpa using 𝒰.iSup_opensRange)).2 <|
        by simpa using h𝒰

/-- Lemma 29.44.3 (2): a morphism of schemes is finite if and only if there exists an open
covering of the target such that each restricted morphism over a member of the cover is finite. -/
@[stacks 01WI]
theorem isFinite_iff_exists_openCover :
    IsFinite f ↔
      ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, IsFinite (f ∣_ 𝒰.U i) := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover.openCover, ?_⟩
    simpa using
      (isFinite_iff_forall_restrict f S.affineOpenCover.openCover.U
        (by simpa using S.affineOpenCover.openCover.isOpenCover_opensRange.iSup_eq_top)).1 hf
  · rintro ⟨𝒰, h𝒰⟩
    exact
      (isFinite_iff_forall_restrict f 𝒰.U
        (by simpa using 𝒰.isOpenCover_opensRange.iSup_eq_top)).2 h𝒰

/-- Lemma 29.44.3 (3): if a morphism of schemes is finite, then its restriction to any open
subscheme of the target is finite. -/
@[stacks 01WI]
theorem isFinite_restrict (U : S.Opens) [IsFinite f] :
    IsFinite (f ∣_ U) :=
  inferInstance

end

end AlgebraicGeometry
