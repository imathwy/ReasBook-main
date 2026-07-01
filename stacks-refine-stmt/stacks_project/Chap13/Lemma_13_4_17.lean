import Mathlib.CategoryTheory.Triangulated.Functor

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/- Domain-style sampling for Lemma 13.4.17:
- primary domain: exact functors between pretriangulated categories and their additive structure;
- sampled owner declarations:
  `Functor.IsTriangulated`,
  `Functor.IsTriangulated.map_distinguished`,
  the upstream owner instance `[F.IsTriangulated] : F.Additive`,
  `Adjunction.isTriangulated_rightAdjoint` as a downstream consumer of the same exact-functor
    abstraction;
- best owner abstraction: `Functor.IsTriangulated`;
- primitive data: the shift-compatibility structure `[F.CommShift ℤ]` and the distinguished-triangle
  preservation structure `[F.IsTriangulated]`;
- derived API: the additive structure on `F`, provided canonically by the owner instance rather
  than by a separate local theorem;
- source/core/bridge triage:
  `source-facing`: the Stacks assertion that an exact functor is additive;
  `core/canonical`: the mathlib owner instance `[F.IsTriangulated] : F.Additive`;
  `bridge/view`: the recall below, specialized to exact functors encoded by
    `Functor.CommShift ℤ` and `Functor.IsTriangulated`.

This item is therefore a pure recall of the canonical owner consequence, not a new theorem-shaped
API. -/

variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Lemma 13.4.17: an exact functor of pretriangulated categories, encoded by
`F.CommShift ℤ` and `F.IsTriangulated`, is additive. This is the canonical upstream instance
attached to `Functor.IsTriangulated`. -/
#check (inferInstance : F.Additive)

end

end CategoryTheory
