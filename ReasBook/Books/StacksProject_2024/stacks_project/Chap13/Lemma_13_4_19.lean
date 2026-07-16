import StacksProject_2024.stacks_project.Chap13.Definition_13_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

/- Domain-style sampling for Lemma 13.4.19:
- primary domain: composition of exact functors between pretriangulated categories;
- sampled owner declarations:
  `Functor.CommShift`,
  `Functor.IsTriangulated`,
  `Functor.mapTriangleCompIso`,
  the composite instance `[F.IsTriangulated] [G.IsTriangulated] : (F ⋙ G).IsTriangulated`;
- best owner abstraction: exactness is already owned by the pair
  `Functor.CommShift ℤ` and `Functor.IsTriangulated`, so this lemma should be a direct recall of
  the composite owner instances, not a parallel local wrapper.

Primitive data vs. derived API:
- primitive data: the functors together with their `CommShift` structures;
- derived exactness API: the `IsTriangulated` owner on the composite functor.

Source/core/bridge triage:
- `source-facing`: exact functors compose;
- `core/canonical`: `Functor.CommShift` and `Functor.IsTriangulated`;
- `bridge/view`: the anonymous composite instances provided by the shift and triangulated functor
  APIs.
-/

section CommShift

variable {D : Type u₁} {D' : Type u₂} {D'' : Type u₃}
  [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} D'']
  [HasShift D ℤ] [HasShift D' ℤ] [HasShift D'' ℤ]
  (F : D ⥤ D') (F' : D' ⥤ D'')
  [F.CommShift ℤ] [F'.CommShift ℤ]

/- Lemma 13.4.19, primitive owner layer: the composite of shift-compatible functors is again
shift-compatible. -/
#check (inferInstance : (F ⋙ F').CommShift ℤ)

end CommShift

section IsTriangulated

variable {D : Type u₁} {D' : Type u₂} {D'' : Type u₃}
  [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} D'']
  [HasZeroObject D] [HasZeroObject D'] [HasZeroObject D'']
  [HasShift D ℤ] [HasShift D' ℤ] [HasShift D'' ℤ]
  [Preadditive D] [Preadditive D'] [Preadditive D'']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [∀ n : ℤ, (shiftFunctor D'' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [Pretriangulated D'']
  (F : D ⥤ D') (F' : D' ⥤ D'')
  [F.CommShift ℤ] [F'.CommShift ℤ] [F.IsTriangulated] [F'.IsTriangulated]

/- Lemma 13.4.19, exact owner layer: if `F` and `F'` are exact functors in the canonical sense of
Definition 13.3.3, then `F ⋙ F'` is exact as well. The faithful source-facing surface is to check
the canonical composite `IsTriangulated` owner directly, since the composite instance is already
provided upstream and has no separate local name to recall. -/
#check (inferInstance : (F ⋙ F').IsTriangulated)

end IsTriangulated

end CategoryTheory
