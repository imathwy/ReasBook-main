import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.37.2:
- primary domain: compact objects in triangulated categories, expressed as an object property and
  its induced full subcategory;
- sampled owner declarations:
  `IsCompactObject`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`,
  `IsTriangulated P.FullSubcategory`;
- best owner abstraction: the source-facing owner remains `IsCompactObject`, while saturation and
  triangulatedity are expressed through the canonical object-property owners
  `ObjectProperty.IsStableUnderRetracts` and `ObjectProperty.IsTriangulated`; the compact
  subcategory is the direct bridge/view `D_c(D)`;
- primitive data: the compactness predicate `IsCompactObject`;
- derived API: closure under isomorphisms from retract stability and triangulatedity of `D_c(D)`
  from the generic full-subcategory instance;
- source/core/bridge triage:
  `source-facing`: the compact-object predicate `IsCompactObject`;
  `core/canonical`: the owner predicates `ObjectProperty.IsStableUnderRetracts` and
    `ObjectProperty.IsTriangulated`;
  `bridge/view`: the full subcategory `D_c(D)`.

This file is therefore the owner only of the two missing compact-object instances; strict-fullness
and the triangulated structure on `D_c(D)` remain derived recall/view API from the generic
object-property machinery. -/

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{max u v} D]

/-- The compact-object property is saturated, i.e. stable under retracts/direct summands. -/
-- Proof sketch: if `K` is a retract of `L`, then `Hom_D(K,-)` is a retract of `Hom_D(L,-)` in the
-- functor category; a retract of a coproduct-preserving additive functor again preserves the same
-- coproducts.
instance isCompactObject_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (IsCompactObject : ObjectProperty D) := sorry

/- Companion recall: retract-stable object properties are automatically strictly full, so the
compact-object property is canonically closed under isomorphisms. -/
#check (inferInstance :
  ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObject : ObjectProperty D))

variable [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- The compact-object property is triangulated in the object-property sense. -/
-- Proof sketch: represented functors are homological in a pretriangulated category. For a
-- distinguished triangle, if two terms are compact then applying `Hom_D(-,-)` to any coproduct
-- yields a morphism of long exact sequences; Lemma `12.5.20` gives the third compactness
-- condition, while zero objects and shifts are formal.
instance isCompactObject_isTriangulated :
    ObjectProperty.IsTriangulated (IsCompactObject : ObjectProperty D) := sorry

variable [IsTriangulated D]

/- Lemma 13.37.2: in a triangulated category `D` with direct sums, the compact objects form a
strictly full saturated triangulated subcategory `D_c ⊆ D`. Once
`ObjectProperty.IsTriangulated (IsCompactObject : ObjectProperty D)` is available, the
triangulated structure on `D_c(D)` is the canonical full-subcategory instance. -/
#check (inferInstance : IsTriangulated (D_c(D)))

end

end CategoryTheory
