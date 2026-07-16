import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall / analogue check:
-- - `lean_leansearch` surfaced the canonical composition instances
--   `AlgebraicGeometry.locallyOfFinitePresentation_comp`,
--   `AlgebraicGeometry.quasiCompact_comp`, and `AlgebraicGeometry.quasiSeparated_comp`;
-- - nearby Section 29.21 files use the local owner `Scheme.Hom.FinitePresentation` for the
--   source phrase “of finite presentation”.

/- Lemma 29.21.3 (1): the composition of two morphisms which are locally of finite presentation is
locally of finite presentation. This is the canonical mathlib composition instance
`AlgebraicGeometry.locallyOfFinitePresentation_comp`. -/
recall AlgebraicGeometry.locallyOfFinitePresentation_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (f ≫ g)

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 29.21.3: the composition of two morphisms of finite presentation is of finite
presentation. -/
@[stacks 01TR]
theorem finitePresentation_comp [FinitePresentation f] [FinitePresentation g] :
    FinitePresentation (f ≫ g) := by
  exact
    { toLocallyOfFinitePresentation := inferInstance
      toQuasiCompact := inferInstance
      toQuasiSeparated := inferInstance }

/-- The composition of two finite-presentation morphisms is of finite presentation. -/
@[stacks 01TR, instance]
instance instFinitePresentationComp [FinitePresentation f] [FinitePresentation g] :
    FinitePresentation (f ≫ g) :=
  finitePresentation_comp f g

end AlgebraicGeometry.Scheme.Hom
