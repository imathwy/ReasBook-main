import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

-- Source/core/bridge triage:
-- - `source-facing`: the Stacks statements that an open morphism is generizing and a universally
--   open morphism is universally generizing;
-- - `core/canonical`: `topologically GeneralizingMap f`,
--   `(topologically @GeneralizingMap).universally f`, and `UniversallyOpen f`;
-- - `bridge/view`: the private monotonicity helper below from universal openness to universal
--   generizing, via the topological owner `IsOpenMap`.

/-- Lemma 29.23.5 (1): if a morphism of schemes is open, then generalizations lift along its
underlying map, i.e. the morphism is generizing. -/
theorem generalizingMap_of_isOpenMap
    (hopen : IsOpenMap f.base) :
    topologically GeneralizingMap f := sorry

/-- Lemma 29.23.5 (2): if a morphism of schemes is universally open, then every base change is
generizing, i.e. the morphism is universally generizing. -/
theorem universallyGeneralizing_of_universallyOpen
    [UniversallyOpen f] :
    (topologically GeneralizingMap).universally f := by
  intro X Y g h
  have hopen : IsOpenMap (pullback.snd f g).base :=
    UniversallyOpen.universally_isOpenMap (f := pullback.snd f g) X Y g h
  exact generalizingMap_of_isOpenMap (f := pullback.snd f g) hopen

end AlgebraicGeometry
