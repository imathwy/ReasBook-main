import Mathlib

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- `lean_leansearch` recalled mathlib's canonical relative-normalization API
-- `Scheme.Hom.fromNormalization`, `Scheme.Hom.toNormalization`, and
-- `Scheme.Hom.normalizationDesc`. Local Chapter 29 precedent already formalizes relative
-- normalization through that owner, so this item is stated as the universal property and its
-- two consequences for the canonical factorization `Y ⟶ f.normalization ⟶ X`.

/-- Lemma 29.53.4 (1): for a quasi-compact and quasi-separated morphism of schemes
`f : Y ⟶ X`, the canonical morphism from the normalization of `X` in `Y` to `X` is integral. -/
@[stacks 035I]
theorem Scheme.Hom.isIntegralHom_fromNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom f.fromNormalization := sorry

/-- Lemma 29.53.4 (2): the factorization
`f = f.toNormalization ≫ f.fromNormalization` of a quasi-compact and quasi-separated morphism
`f : Y ⟶ X` through the normalization of `X` in `Y` is initial among factorizations
`f = g ≫ π` with `π` integral. -/
@[stacks 035I]
theorem Scheme.Hom.existsUnique_lift_fromNormalization
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π] (hf : f = g ≫ π) :
    ∃! h : f.normalization ⟶ Z,
      f.toNormalization ≫ h = g ∧ h ≫ π = f.fromNormalization := sorry

/-- Lemma 29.53.4 (3): the canonical map from `Y` to the normalization of `X` in `Y` is
dominant. -/
@[stacks 035I]
theorem Scheme.Hom.isDominant_toNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    IsDominant f.toNormalization := sorry

/-- Lemma 29.53.4 (4): in the universal property of relative normalization, the induced morphism
`h : f.normalization ⟶ Z` to an integral factor `π : Z ⟶ X` is itself integral. -/
@[stacks 035I]
theorem Scheme.Hom.isIntegralHom_normalizationDesc
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π] (hf : f = g ≫ π) :
    IsIntegralHom (f.normalizationDesc g π hf) := sorry

/-- Lemma 29.53.4 (5): for an integral factorization `f = g ≫ π`, the induced map
`h = f.normalizationDesc g π hf : f.normalization ⟶ Z` is the normalization of `Z` in `Y`;
equivalently, it is initial among integral factorizations of `g`. -/
@[stacks 035I]
theorem Scheme.Hom.existsUnique_lift_normalizationDesc
    {X Y Z Z' : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π] (hf : f = g ≫ π)
    (g' : Y ⟶ Z') (π' : Z' ⟶ Z) [IsIntegralHom π'] (hg : g = g' ≫ π') :
    ∃! h' : f.normalization ⟶ Z',
      f.toNormalization ≫ h' = g' ∧ h' ≫ π' = f.normalizationDesc g π hf := sorry

end AlgebraicGeometry
