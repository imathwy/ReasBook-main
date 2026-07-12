import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic note: `QuasiCompact` is the canonical owner for quasi-compact morphisms of schemes.
-- For affine-local criteria, the source asks that each inverse-image open subscheme be
-- quasi-compact as a scheme, whose canonical mathlib surface is the compactness of the
-- corresponding open subset.

/- Source/core/bridge triage for Lemma 26.19.2:
- `source-facing`: quasi-compactness can be checked on an affine open cover of the target, and
  equivalently on some affine open cover;
- `core/canonical`: `quasiCompact_iff_forall_isAffineOpen`;
- `bridge/view`: the fixed affine-open-cover criterion derived from
  `HasAffineProperty.iff_of_iSup_eq_top`. -/

/- Lemma 26.19.2 (1): this is exactly mathlib's affine-open criterion for quasi-compact scheme
morphisms. -/
#check quasiCompact_iff_forall_isAffineOpen

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Companion API: a morphism of schemes is quasi-compact exactly when the inverse image of every
member of a fixed affine open cover of the target is quasi-compact. This is the fixed-cover form
of the affine-open criterion from part (1), specialized through
`HasAffineProperty.iff_of_iSup_eq_top`.
-/
theorem Scheme.Hom.quasiCompact_iff_affineOpenCover_preimage_isCompact
    (𝒰 : S.AffineOpenCover) :
    QuasiCompact f ↔
      ∀ i : 𝒰.I₀,
        IsCompact (f ⁻¹ᵁ 𝒰.U i : Set X) := by
  simpa using
    (HasAffineProperty.iff_of_iSup_eq_top
      (P := @QuasiCompact) (f := f) (U := 𝒰.U)
      (by simpa using 𝒰.iSup_opensRange))

/-- Lemma 26.19.2 (2): a morphism of schemes is quasi-compact if and only if there exists an affine
open cover of the target whose inverse-image open subschemes are quasi-compact. -/
@[stacks 01K4]
theorem quasiCompact_iff_exists_affineOpenCover :
    QuasiCompact f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsCompact (f ⁻¹ᵁ 𝒰.U i : Set X) := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover, ?_⟩
    simpa using
      (Scheme.Hom.quasiCompact_iff_affineOpenCover_preimage_isCompact
        (f := f) S.affineOpenCover).1 hf
  · rintro ⟨𝒰, h𝒰⟩
    exact
      (Scheme.Hom.quasiCompact_iff_affineOpenCover_preimage_isCompact
        (f := f) 𝒰).2 <|
        by simpa using h𝒰

end

end AlgebraicGeometry
