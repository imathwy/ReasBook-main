import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism predicates
-- `IsFinite` and `Surjective`, and the scheme properties `IsAffine` and `IsNoetherian`;
-- nearby Chapter 30 files use `[IsNoetherian X]` for the source phrase "X Noetherian".

/-- Lemma 30.13.3: let `f : Y ⟶ X` be a finite surjective morphism of schemes. If `Y` is
affine and `X` is Noetherian, then `X` is affine. -/
@[stacks 01YQ]
theorem isAffine_of_finite_surjective_of_isAffine_source
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsAffine Y]
    [IsNoetherian X] :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
