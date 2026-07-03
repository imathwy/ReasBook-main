import Mathlib
import StacksProject_2024.Chap13.Definition_13_3_4
import StacksProject_2024.Chap13.Lemma_13_35_1
import StacksProject_2024.Chap13.Definition_13_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.40.5:
- primary domain: triangulated closure of extension products of object properties in a
  triangulated category;
- sampled core/canonical declarations:
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderBinaryProducts`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`;
- best owner abstraction: the source-facing object property `A ⋆ A^⊥`, owned canonically by
  `ObjectProperty.extensionProduct`, whose three triangle-closure clauses are organized by the
  owner predicate `.IsTriangulated`, while direct-sum closure is the generic
  `ObjectProperty.IsClosedUnderBinaryCoproducts` owner consequence of a triangulated object
  property in the preadditive ambient category;
- primitive data: the object property `A`, its canonical right orthogonal `A^⊥`, and their
  canonical extension product `A ⋆ A^⊥`;
- derived API: the clausewise closure predicates
  `(A ⋆ A^⊥).IsTriangulatedClosed₁`,
  `(A ⋆ A^⊥).IsTriangulatedClosed₂`, and
  `(A ⋆ A^⊥).IsTriangulatedClosed₃`;
  clause `(4)` is the direct binary-coproduct closure of this same owner, obtained from its
  triangulated/product closure and the canonical biproduct bridge in a preadditive category.

Source/core/bridge triage:
- `source-facing`: Lemma `13.40.5` asserts that `A ⋆ A^⊥` is closed under the three distinguished
  triangle clauses and under binary direct sums;
- `core/canonical`: the owner declarations `extensionProduct`, `rightOrthogonal`, and
  `IsTriangulated`;
- `bridge/view`: the clausewise `IsTriangulatedClosed₁/₂/₃` consequences obtained by inference from
  the main triangulated owner instance, together with the generic binary-coproduct closure owner
  instance reused for clause `(4)`.

The file should therefore keep the owner-level triangulated instance as the main declaration and
demote the individual closure clauses to companion recalls, rather than storing all three as
primitive parallel instances. -/

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: the owner-level mathematical content of clauses `(1)`–`(3)` is that the
-- canonical extension product `A ⋆ A^⊥` is triangulated. Its `Closed₁` and
-- `Closed₃` clauses are then derived automatically from the canonical owner instance.
/-- Lemma 13.40.5 (1)–(3): the canonical extension product `A ⋆ A^⊥` is a
triangulated subcategory. Equivalently, it satisfies all three distinguished-triangle closure
clauses from the source statement. -/
instance extensionProduct_rightOrthogonal_isTriangulated :
    (A ⋆ A^⊥).IsTriangulated where
  toContainsZero := by
    obtain ⟨Z, hZ, hA⟩ := A.exists_prop_of_containsZero
    exact ⟨Z, hZ, le_extensionProduct_left (A^⊥) Z hA⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := sorry

/- Companion recall for clause `(1)`: this is the canonical `Closed₁` consequence of the
triangulated owner instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₁)

/- Companion recall for clause `(2)`: this is the `Closed₂` field of the triangulated owner
instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₂)

/- Companion recall for clause `(3)`: this is the canonical `Closed₃` consequence of the
triangulated owner instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₃)

/- Companion recall for clause `(4)`: binary direct-sum closure is the generic owner consequence
of the triangulated instance above together with the canonical isomorphism-closure of
`extensionProduct`. -/
#check (inferInstance : (A ⋆ A^⊥).IsClosedUnderBinaryCoproducts)

end Triangulated

end CategoryTheory.ObjectProperty
