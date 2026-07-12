import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-morphism owner
-- `AlgebraicGeometry.IsAffineHom`, the closed-image criterion
-- `AlgebraicGeometry.isAffineHom_of_isInducing`, and the immersion factorization API
-- `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`; the source-facing statement below keeps
-- the textbook's affine-open/complement hypotheses on the surface rather than replacing them by a
-- stronger closed-range specialization.

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}} (j : Y ⟶ X)

/-- Auxiliary fixed-open hypothesis package for the affine-immersion criterion used below. -/
class AffineImmersionOnOpenComplement (j : Y ⟶ X) (U : X.Opens) : Prop where
  /-- The chosen open immersion target is affine over the ambient scheme. -/
  isAffineHom_inclusion : IsAffineHom U.ι
  /-- The restriction of the immersion to the chosen open is affine. -/
  isAffineHom_restrict : IsAffineHom (j ∣_ U)
  /-- The part of the image lying over the closed complement of the chosen open is closed. -/
  isClosed_range_inter_compl : IsClosed (Set.range j ∩ (U : Set X)ᶜ)

/-- The fixed-open affine-immersion hypothesis package supplies an affine inclusion. -/
theorem AffineImmersionOnOpenComplement.isAffineHomInclusion (U : X.Opens)
    [h : AffineImmersionOnOpenComplement j U] :
    IsAffineHom U.ι :=
  h.isAffineHom_inclusion

/-- The fixed-open affine-immersion hypothesis package supplies an affine restriction. -/
instance instIsAffineHomRestrict (U : X.Opens) [h : AffineImmersionOnOpenComplement j U] :
    IsAffineHom (j ∣_ U) :=
  h.isAffineHom_restrict

/-- The fixed-open affine-immersion hypothesis package records closedness over the complement. -/
theorem AffineImmersionOnOpenComplement.isClosedRangeInterCompl (U : X.Opens)
    [h : AffineImmersionOnOpenComplement j U] :
    IsClosed (Set.range j ∩ (U : Set X)ᶜ) :=
  h.isClosed_range_inter_compl

/-- Lemma 29.11.15: let `j : Y ⟶ X` be an immersion of schemes. Assume there exists an open
`U ⊆ X` such that the inclusion `U ⟶ X` is affine, the restricted morphism `j⁻¹(U) ⟶ U` is affine,
and `j(Y) ∩ (X \ U)` is closed. Then `j` is affine. -/
theorem isAffineHom_of_exists_affine_restrict_and_closed_compl
    [IsImmersion j]
    (h : ∃ U : X.Opens, AffineImmersionOnOpenComplement j U) :
    IsAffineHom j := sorry

/-- An immersion into an affine scheme has affine source. -/
theorem isAffine_of_isAffineTarget_of_isImmersion
    [IsImmersion j] [IsAffine X] :
    IsAffine Y := sorry

end

end AlgebraicGeometry
