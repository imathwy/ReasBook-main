import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` returned the canonical mathlib composition instance
  `AlgebraicGeometry.locallyOfFiniteType_comp`;
- `Definition_29_15_1.lean` records the source phrase “of finite type” for scheme morphisms as
  `Scheme.Hom.FiniteType`, the canonical pair `QuasiCompact` and `LocallyOfFiniteType`;
- nearby `Lemma_29_15_4.lean` exposes this local finite-type owner with both theorem and instance
  surfaces.
-/

/- Lemma 29.15.3 (1): the composition of two morphisms which are locally of finite type is
locally of finite type. This is the canonical mathlib composition instance
`AlgebraicGeometry.locallyOfFiniteType_comp`. -/
recall AlgebraicGeometry.locallyOfFiniteType_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g)

namespace Scheme.Hom

/-- Lemma 29.15.3 (2): the composition of two morphisms of finite type is of finite type. -/
@[stacks 01T3]
theorem finiteType_comp_of_finiteType
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) := by
  exact
    { toQuasiCompact := inferInstance
      toLocallyOfFiniteType := inferInstance }

/-- Finite-type morphisms are closed under composition as a typeclass instance. -/
@[stacks 01T3, instance]
instance instFiniteTypeCompOfFiniteType
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) :=
  finiteType_comp_of_finiteType f g

end Scheme.Hom

end AlgebraicGeometry
