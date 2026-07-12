import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Source/core/bridge triage for Lemma 29.23.3:
- `source-facing`: the composition statements for open and universally open morphisms of schemes;
- `core/canonical`: `IsOpenMap.comp` for the topological clause and
  `MorphismProperty.comp_mem UniversallyOpen f g` for universal openness;
- `bridge/view`: the textbook phrases "open morphism" and "universally open morphism" expressed
  through `f.base` and `AlgebraicGeometry.UniversallyOpen`.

The first clause is a source-facing bridge from scheme morphisms to `IsOpenMap`. The second clause
adds no new owner beyond the canonical morphism-property composition theorem, so refine that clause
to direct recall/check rather than a chapter-local wrapper. -/

/-- Lemma 29.23.3 (1): the composition of open morphisms of schemes is open, expressed on the
underlying continuous maps. -/
@[stacks 02V2]
theorem base_isOpenMap_comp
    (hf : IsOpenMap f.base) (hg : IsOpenMap g.base) :
    IsOpenMap (f ≫ g).base := by
  simpa using hg.comp hf

/- Lemma 29.23.3 (2): the universally open clause is exactly the canonical specialization
`MorphismProperty.comp_mem (@UniversallyOpen) f g`. -/
recall MorphismProperty.comp_mem

#check
  (MorphismProperty.comp_mem (@UniversallyOpen) f g :
    UniversallyOpen f → UniversallyOpen g → UniversallyOpen (f ≫ g))

end AlgebraicGeometry
