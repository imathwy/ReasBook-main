import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recalled the canonical relative-normalization morphism
-- `Scheme.Hom.toNormalization`; local Chapter 29/31 precedent packages “generic point of an
-- irreducible component” as membership in `genericPointsOfIrreducibleComponents`.

/-- Lemma 29.53.9: let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of schemes, and
let `X' ⟶ X` be the normalization of `X` in `Y`. Then every generic point of an irreducible
component of `X'` is the image of a generic point of an irreducible component of `Y`. -/
@[stacks 0AXP]
theorem Scheme.Hom.surjOn_genericPointsOfIrreducibleComponents_toNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    Set.SurjOn f.toNormalization
      (genericPointsOfIrreducibleComponents Y)
      (genericPointsOfIrreducibleComponents f.normalization) := sorry

/-- The canonical map to the relative normalization is surjective on the canonical owner
`genericPoints`. -/
theorem Scheme.Hom.surjOn_genericPoints_toNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    Set.SurjOn f.toNormalization (genericPoints Y) (genericPoints f.normalization) := by
  simpa [genericPointsOfIrreducibleComponents_eq_genericPoints] using
    f.surjOn_genericPointsOfIrreducibleComponents_toNormalization

end AlgebraicGeometry
