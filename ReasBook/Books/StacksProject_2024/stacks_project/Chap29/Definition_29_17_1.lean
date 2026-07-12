import Mathlib
import StacksProject_2024.Chap05.Definition_5_11_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

/- Semantic recall / analogue check:
- ring-level analogue: `UniversallyCatenaryRing` in `Chap10/Definition_10_105_3`;
- scheme morphism owner for “locally of finite type”: `LocallyOfFiniteType`;
- underlying-space owners: `TopologicalSpace.LocallyNoetherianSpace` and `CatenarySpace`.
-/

/-- Definition 29.17.1: a locally Noetherian scheme `S` is universally catenary if every scheme
locally of finite type over `S` is catenary. -/
@[stacks 02J8]
class UniversallyCatenary (S : Scheme.{u}) : Prop extends IsLocallyNoetherian S where
  catenarySpace_of_locallyOfFiniteType {X : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    CatenarySpace X

/-- A universally catenary scheme is catenary via the identity morphism. -/
instance instCatenarySpaceOfUniversallyCatenary (S : Scheme.{u}) [h : UniversallyCatenary S] :
  CatenarySpace S := by
  letI : LocallyOfFiniteType (CategoryTheory.CategoryStruct.id S) := inferInstance
  simpa using h.catenarySpace_of_locallyOfFiniteType (CategoryTheory.CategoryStruct.id S)

end AlgebraicGeometry
