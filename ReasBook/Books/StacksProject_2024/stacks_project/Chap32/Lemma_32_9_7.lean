import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsFinite`, `IsClosedImmersion`, and `Scheme.Hom.FinitePresentation`; local Chapter 32
-- precedent encodes a morphism over the base by an explicit equation `i ≫ f' = f`.

/-- Lemma 32.9.7: let `f : X ⟶ S` be finite, with `S` quasi-compact and quasi-separated.
Then `f` factors over `S` through a closed immersion `X ⟶ X'`, where `X' ⟶ S` is finite
and of finite presentation. -/
@[stacks 01ZK]
theorem exists_finite_finitePresentation_closedImmersion_factorization_of_isFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (f' : X' ⟶ S),
      ∃ (_ : IsClosedImmersion i), ∃ (_ : IsFinite f'),
        ∃ (_ : Scheme.Hom.FinitePresentation f'), i ≫ f' = f := sorry

end AlgebraicGeometry
