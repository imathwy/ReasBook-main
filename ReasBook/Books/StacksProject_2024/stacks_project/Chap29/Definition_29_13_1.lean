import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine-morphism analogue `IsAffineHom` and the
-- scheme property `Scheme.IsQuasiAffine`; mathlib's generic owner `targetAffineLocally` matches
-- the source exactly by requiring the restricted source over each affine open of the target to be
-- quasi-affine.

/-- Definition 29.13.1: a morphism of schemes `f : X ⟶ S` is quasi-affine if the inverse image of
every affine open of `S` is a quasi-affine scheme. -/
@[stacks 01SL]
abbrev QuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  targetAffineLocally
    (fun {Y T : Scheme} (_ : Y ⟶ T) ↦ Y.IsQuasiAffine) f

/-- Canonical affine-open form of `QuasiAffineHom`. -/
theorem quasiAffineHom_iff_affineOpens {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔
      ∀ U : S.affineOpens, (f ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine :=
  Iff.rfl

/-- Unfold `QuasiAffineHom` as the affine-open preimage condition from the source definition. -/
theorem quasiAffineHom_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔
      ∀ U : S.Opens, IsAffineOpen U → (f ⁻¹ᵁ U).toScheme.IsQuasiAffine := by
  sorry

end AlgebraicGeometry
