import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `Scheme.Hom.QuasiFiniteAt`,
-- `LocallyOfFiniteType`, and `genericPoints`; local Chapter 29 precedent uses
-- `genericPointsOfIrreducibleComponents` for the source notation `X^0` and `Y^0`.

/-- Lemma 29.51.4: let `f : X ⟶ Y` be locally of finite type, let `X⁰` and `Y⁰` denote the
generic points of irreducible components, and let `η ∈ Y⁰`. The following are equivalent:
the fibre over `η` is contained in `X⁰`; `f` is quasi-finite at every point lying over `η`; and
`f` is quasi-finite at every point of `X⁰` lying over `η`. -/
@[stacks 0BAH]
theorem Scheme.Hom.tfae_fiber_subset_genericPointsOfIrreducibleComponents_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {η : Y}
    (hη : η ∈ genericPointsOfIrreducibleComponents Y) :
    List.TFAE
      [ (∀ x : X, f.base x = η → x ∈ genericPointsOfIrreducibleComponents X)
      , (∀ x : X, f.base x = η → f.QuasiFiniteAt x)
      , (∀ x : X, x ∈ genericPointsOfIrreducibleComponents X → f.base x = η →
          f.QuasiFiniteAt x)
      ] := sorry

end AlgebraicGeometry
