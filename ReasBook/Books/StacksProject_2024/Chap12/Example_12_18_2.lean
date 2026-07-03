import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits ComplexShape

universe v₁ v₂ v₃ u₁ u₂ u₃

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms C]
variable (tensor : A ⥤ B ⥤ C) [tensor.PreservesZeroMorphisms]
  [∀ X, (tensor.obj X).PreservesZeroMorphisms]
variable (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ)

/- Domain-style sampling for Example 12.18.2:
- primary domain: bicomplexes produced by applying a bifunctor to cochain complexes;
- sampled core/canonical declarations:
  `Functor.mapBifunctorHomologicalComplex`,
  `Functor.mapBifunctorHomologicalComplex_obj_obj_X_X`,
  `Functor.mapBifunctorHomologicalComplex_obj_obj_d_f`,
  `Functor.mapBifunctorHomologicalComplex_obj_obj_X_d`;
- best owner abstraction: `Functor.mapBifunctorHomologicalComplex`;
- primitive data: the bifunctor `tensor : A ⥤ B ⥤ C`, its zero-morphism preservation in each
  variable, and the input cochain complexes `X` and `Y`;
- derived API: the resulting bicomplex and its `(p, q)`-terms together with the horizontal and
  vertical differentials;
- source/core/bridge triage:
  `source-facing`: the textbook bicomplex obtained from applying `tensor` degreewise to
    `X` and `Y`;
  `core/canonical`: `tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)`;
  `bridge/view`: the componentwise computation rules recalled below.

No local wrapper should be introduced here: the source-facing bicomplex is already the direct
evaluation of the canonical owner bifunctor on `X` and `Y`. -/
/-
Example 12.18.2 is source-facing in the bicomplex domain: the textbook additive bifunctor
`\otimes : \mathcal A × \mathcal B ⥤ \mathcal C` is recalled through the owner bifunctor
`tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)`, whose canonical API only needs
zero-morphism preservation in each variable.
-/
recall Functor.mapBifunctorHomologicalComplex

/- Evaluating that owner bifunctor at cochain complexes `X^\bullet` and `Y^\bullet` gives the
canonical bicomplex `((tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj X).obj Y`. -/
#check ((tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj X).obj Y

/- Companion recall: the `(p, q)`-term of this bicomplex is `(tensor.obj (X.X p)).obj (Y.X q)`. -/
recall Functor.mapBifunctorHomologicalComplex_obj_obj_X_X

/- Companion recall: the horizontal differential is induced by the differential of `X`. -/
recall Functor.mapBifunctorHomologicalComplex_obj_obj_d_f

/- Companion recall: the vertical differential is induced by the differential of `Y`. -/
recall Functor.mapBifunctorHomologicalComplex_obj_obj_X_d

end
