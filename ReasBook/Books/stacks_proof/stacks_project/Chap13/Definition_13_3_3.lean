import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasShift C ℤ] [HasShift D ℤ]

/- Domain-style sampling for Definition 13.3.3:
- primary domain: triangulated functors between categories with shift by `ℤ`;
- sampled core/canonical declarations:
  `Functor.CommShift`,
  `Functor.IsTriangulated`,
  `Functor.mapTriangle`,
  `Functor.mapTriangleCompIso`;
- best owner abstraction: exactness is owned canonically by the pair of functor-level structures
  `[F.CommShift ℤ]` and `[F.IsTriangulated]`, with `Functor.IsTriangulated` carrying the actual
  distinguished-triangle preservation property and `Functor.CommShift ℤ` as the primitive
  shift-compatibility data it depends on;
- primitive data: a functor `F : C ⥤ D` together with the shift-commuting structure
  `[F.CommShift ℤ]`;
- derived API: `F.mapTriangle`, the induced exactness/additivity instances, and the composition
  compatibility supplied upstream by `mapTriangleCompIso` and the standard composite instances;
- source/core/bridge triage:
  `source-facing`: the Stacks notion of an exact functor between pretriangulated categories;
  `core/canonical`: `Functor.CommShift` and `Functor.IsTriangulated`;
  `bridge/view`: the induced functor on triangles and the composition/isomorphism API built from
    those owners.

Definition 13.3.3 is therefore a pure recall of the canonical owner declarations, not a place
for a local wrapper predicate or duplicate exact-functor structure. -/

/- The primitive shift-compatibility data in the definition of an exact functor is the canonical
`Functor.CommShift ℤ` structure. -/
recall Functor.CommShift

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ]

/- Definition 13.3.3: once the shift-commuting data is fixed, the exactness condition for a
functor between pre-triangulated categories is the canonical predicate
`Functor.IsTriangulated`. -/
recall Functor.IsTriangulated

end

end CategoryTheory
