import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Definition 13.40.9:
- primary domain: admissible full triangulated subcategories of a triangulated category;
- sampled owner API:
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderIsomorphisms`,
  `Functor.IsRightAdjoint`,
  `Functor.IsLeftAdjoint`;
- best owner abstraction: the object property `A : ObjectProperty D` together with the canonical
  inclusion functor `A.ι : A.FullSubcategory ⥤ D`;
- primitive data:
  `A.IsTriangulated`,
  `A.IsClosedUnderIsomorphisms`,
  and the adjointness of the owner inclusion functor;
- ambient layer: only the pretriangulated structure on `D` is primitive here; the ambient
  hypothesis `[IsTriangulated D]` is not needed for the owner declarations themselves;
- derived API: the induced instances `A.ι.IsRightAdjoint` and `A.ι.IsLeftAdjoint`, and the
  one-sided admissibility instances recovered from two-sided admissibility;
- source/core/bridge triage:
  `source-facing`: right admissibility, left admissibility, and admissibility of a triangulated
    subcategory;
  `core/canonical`: the existing owners `ObjectProperty.IsTriangulated`,
    `ObjectProperty.IsClosedUnderIsomorphisms`, `Functor.IsRightAdjoint`, and
    `Functor.IsLeftAdjoint`;
  `bridge/view`: the inclusion functor `A.ι`, whose adjointness is the canonical functor-level
    view of admissibility.

No higher object replaces the source notion here: admissibility is intrinsically a property of the
owner object property `A`, and the only non-primitive data is the adjointness of `A.ι`. -/

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A right admissible subcategory is a strictly full triangulated subcategory satisfying the
equivalent conditions of Lemma `13.40.7`; here this is packaged by requiring the inclusion functor
to be a left adjoint, equivalently to admit a right adjoint. -/
class IsRightAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsLeftAdjoint

/-- A left admissible subcategory is a strictly full triangulated subcategory satisfying the
equivalent conditions of Lemma `13.40.8`; here this is packaged by requiring the inclusion functor
to be a right adjoint, equivalently to admit a left adjoint. -/
class IsLeftAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsRightAdjoint

/-- Definition 13.40.9: a two-sided admissible subcategory is a strictly full triangulated
subcategory that is both right admissible and left admissible. -/
@[stacks 0FXD]
class IsAdmissible (A : ObjectProperty D) : Prop extends
    A.IsTriangulated, A.IsClosedUnderIsomorphisms, A.ι.IsLeftAdjoint, A.ι.IsRightAdjoint

instance instIsRightAdmissibleOfIsAdmissible (A : ObjectProperty D) [hA : IsAdmissible A] :
    IsRightAdmissible A where
  toIsTriangulated := hA.toIsTriangulated
  toIsClosedUnderIsomorphisms := hA.toIsClosedUnderIsomorphisms
  toIsLeftAdjoint := hA.toIsLeftAdjoint

instance instIsLeftAdmissibleOfIsAdmissible (A : ObjectProperty D) [hA : IsAdmissible A] :
    IsLeftAdmissible A where
  toIsTriangulated := hA.toIsTriangulated
  toIsClosedUnderIsomorphisms := hA.toIsClosedUnderIsomorphisms
  toIsRightAdjoint := hA.toIsRightAdjoint

end

end CategoryTheory.ObjectProperty
