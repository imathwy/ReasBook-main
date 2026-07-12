import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism predicate
-- `UniversallyClosed` together with `Surjective`; nearby Chapter 32 precedent states affineness
-- descent for finite surjective morphisms over the canonical `Scheme` API.

/-- Proposition 32.11.2: let `f : X ⟶ S` be a morphism of schemes. If `X` is affine and `f` is
surjective and universally closed, then `S` is affine. -/
@[stacks 05YU]
theorem isAffine_of_surjective_universallyClosed_of_isAffine_source
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [UniversallyClosed f] [IsAffine X] :
    IsAffine S := sorry

end AlgebraicGeometry.Scheme
