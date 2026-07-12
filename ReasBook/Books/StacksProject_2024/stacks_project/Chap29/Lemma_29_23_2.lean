import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

-- Source/core/bridge triage for Lemma 29.23.2:
-- - `source-facing`: the Stacks hypotheses "generizing" and "universally generizing" for a
--   scheme morphism locally of finite presentation;
-- - `core/canonical`: the mathlib theorem `isOpenMap_of_generalizingMap` for the topological
--   openness clause and the owner `UniversallyOpen` with bridge `universallyOpen_iff`;
-- - `bridge/view`: the two theorem names below, which keep the source-facing scheme-level
--   statements while reusing the canonical owners directly.

/-- Lemma 29.23.2 (1): if `f` is locally of finite presentation and generalizations lift along
`f`, then `f` is open. -/
theorem isOpenMap_of_locallyOfFinitePresentation_of_generalizingMap
    [LocallyOfFinitePresentation f] (hf : topologically GeneralizingMap f) :
    topologically IsOpenMap f := by
  simpa using (isOpenMap_of_generalizingMap (f := f) hf)

/-- Lemma 29.23.2 (2): if `f` is locally of finite presentation and generalizations lift along
every base change of `f`, then `f` is universally open. -/
theorem universallyOpen_of_locallyOfFinitePresentation_of_universallyGeneralizing
    [LocallyOfFinitePresentation f]
    (hf : (topologically GeneralizingMap).universally f) :
    UniversallyOpen f := by
  exact ⟨fun X Y g h ↦ isOpenMap_of_generalizingMap (f := pullback.snd f g) (hf X Y g h)⟩

end AlgebraicGeometry
