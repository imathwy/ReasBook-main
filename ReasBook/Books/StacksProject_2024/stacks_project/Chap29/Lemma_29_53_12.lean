import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact relative-normalization owner
-- `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`, stating that for an integral morphism
-- the canonical map to the relative normalization is an isomorphism. The Stacks tag evidence is
-- consistent: item tag `03GP` agrees with the URL ending in `/tag/03GP`.

/-- Lemma 29.53.12: let `f : Y ⟶ X` be an integral morphism. Then the normalization of `X`
in `Y` is equal to `Y`; equivalently, the canonical morphism
`Y ⟶ f.normalization` is an isomorphism. -/
@[stacks 03GP]
theorem Scheme.Hom.isIso_toNormalization_of_isIntegralHom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegralHom f] :
    IsIso f.toNormalization := sorry

end AlgebraicGeometry
