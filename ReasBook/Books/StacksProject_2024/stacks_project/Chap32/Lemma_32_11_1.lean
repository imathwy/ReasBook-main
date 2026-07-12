import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism predicates
-- `IsFinite` and `Surjective`, and the scheme property `IsAffine`; the source statement is
-- therefore a direct theorem over the canonical scheme API.

/-- Lemma 32.11.1: let `f : X ⟶ S` be a morphism of schemes. If `f` is surjective and finite,
and `X` is affine, then `S` is affine. -/
@[stacks 01ZT]
theorem isAffine_of_surjective_finite_of_isAffine_source
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [IsFinite f] [IsAffine X] :
    IsAffine S := sorry

end AlgebraicGeometry.Scheme
