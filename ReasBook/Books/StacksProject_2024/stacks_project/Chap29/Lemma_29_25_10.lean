import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned the exact canonical scheme-morphism instance
-- `AlgebraicGeometry.UniversallyOpen.of_flat`, whose assumptions and conclusion match the source
-- statement: flat plus locally of finite presentation implies universally open.

/- Lemma 29.25.10: a flat morphism locally of finite presentation is universally open. This is
the canonical mathlib instance `AlgebraicGeometry.UniversallyOpen.of_flat`. -/
recall AlgebraicGeometry.UniversallyOpen.of_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    UniversallyOpen f

end AlgebraicGeometry
