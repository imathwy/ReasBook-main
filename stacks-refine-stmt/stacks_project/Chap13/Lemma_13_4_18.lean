import stacks_project.Chap13.Definition_13_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

section

variable {D : Type u₁} {D' : Type u₂} [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D' n)]
  [Pretriangulated D] [Pretriangulated D']
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]

/- Domain-style sampling for Lemma 13.4.18:
- primary domain: fully faithful exact functors between pretriangulated categories and their
  action on distinguished triangles;
- sampled core/canonical declarations in this domain:
  `Functor.IsTriangulated`,
  `Functor.map_distinguished`,
  `Functor.map_distinguished_iff`,
  `Functor.mapTriangle`;
- best owner abstraction: Definition 13.3.3 already fixes exactness as the owner pair
  `[F.CommShift ℤ] [F.IsTriangulated]`, and for a full faithful functor the precise reflection
  statement is already the canonical theorem `Functor.map_distinguished_iff`;
- primitive data: the functor `F`, its exactness owners, and the full/faithful hypotheses;
- derived API: the equivalence between distinguishedness of `T` and of `F.mapTriangle.obj T`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a fully faithful exact functor reflects distinguished
  triangles;
- `core/canonical`: `Functor.map_distinguished_iff`;
- `bridge/view`: the forward implication `Functor.map_distinguished` and the mapped triangle
  `F.mapTriangle.obj T`.

There is no chapter-local owner to keep here: the file should reuse the upstream theorem directly
rather than repackage it as a parallel local lemma. -/

/- Lemma 13.4.18: if `F : D ⥤ D'` is a fully faithful exact functor between pre-triangulated
categories, then a triangle `T` of `D` is distinguished if and only if its image
`F.mapTriangle.obj T`, corresponding to the tuple `(F(X), F(Y), F(Z), F(f), F(g), F(h))`, is
distinguished in `D'`. This is exactly the canonical theorem
`CategoryTheory.Functor.map_distinguished_iff`. -/
recall Functor.map_distinguished_iff

end

end CategoryTheory
