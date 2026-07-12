import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism theorem
-- `AlgebraicGeometry.locallyOfFiniteType_of_comp`. The source wording is the over-base
-- specialization of that owner theorem, so this file is a pure recall rather than a local wrapper.

/- Lemma 29.15.8: let `f : X ⟶ Y` be a morphism of schemes over a base scheme `S`, exhibited by
`g : Y ⟶ S`. If `X` is locally of finite type over `S`, i.e. if the composite `f ≫ g : X ⟶ S` is
locally of finite type, then `f` is locally of finite type. -/
recall AlgebraicGeometry.locallyOfFiniteType_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType (f ≫ g)] :
    LocallyOfFiniteType f

end AlgebraicGeometry
