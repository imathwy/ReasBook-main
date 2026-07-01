import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

section Precompose

/- Domain-style sampling for Lemma 13.4.20:
- primary domain: homological functors out of pretriangulated categories and exact functors between
  abelian categories;
- sampled owner declarations:
  `Functor.IsHomological`,
  the canonical precomposition instance `(L ⋙ F).IsHomological`,
  `ShortComplex.Exact.map`,
  `ExactFunctor`;
- best owner abstraction: `Functor.IsHomological`;
- primitive data: a triangulated functor `F : D' ⥤ D`, a homological functor `H : D ⥤ A`, and an
  exact functor `G : A ⥤ₑ A'`;
- derived API: the induced homologicality instances on `F ⋙ H` and `H ⋙ G.obj`;
- source/core/bridge triage:
  `source-facing`: the two stability statements in Lemma 13.4.20;
  `core/canonical`: `Functor.IsHomological`;
  `bridge/view`: exactness transport along `ShortComplex.Exact.map` for the abelian
    postcomposition case.

The precomposition part is therefore a pure recall of the owner instance, while the
postcomposition part should be stated directly as an owner instance on the composite functor,
rather than as a parallel theorem returning the same `Prop`. -/

variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]

/- Lemma 13.4.20: if `H : D ⥤ A` is homological and `F : D' ⥤ D` is an exact functor between
pretriangulated categories, encoded by `F.CommShift ℤ` and `F.IsTriangulated`, then the composite
`F ⋙ H` is homological. This is exactly the canonical instance on `Functor.IsHomological`; the
companion declaration below records the analogous postcomposition owner instance for exact functors
between abelian categories. -/
variable (F : D' ⥤ D) (H : D ⥤ A) [F.CommShift ℤ] [F.IsTriangulated] [H.IsHomological] in
#check (inferInstance : (F ⋙ H).IsHomological)

end Precompose

section Postcompose

variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable {A' : Type u₄} [Category.{v₄} A'] [Abelian A']

-- Proof sketch: for any distinguished triangle in `D`, homologicality of `H` gives an exact
-- short complex in `A`. Since `G : A ⥤ₑ A'` is exact, its underlying functor `G.obj` preserves
-- exact short complexes, so the image short complex for `H ⋙ G.obj` is exact.
/-- Postcomposition with an exact functor between abelian categories preserves homological
functors. -/
instance (H : D ⥤ A) (G : A ⥤ₑ A') [H.IsHomological] : (H ⋙ G.obj).IsHomological where
  exact T hT := (H.map_distinguished_exact T hT).map G.obj

end Postcompose

end CategoryTheory
