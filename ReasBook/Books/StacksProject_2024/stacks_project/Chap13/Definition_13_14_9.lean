import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂} [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
variable (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-
Domain-style sampling for Definition 13.14.9:
- primary domain: pointwise derived functors with respect to a localization morphism property;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.HasPointwiseRightDerivedFunctor`,
  `Functor.HasPointwiseLeftDerivedFunctor`;
- best owner abstraction: the mathlib pointwise-everywhere predicates
  `Functor.HasPointwiseRightDerivedFunctor` and `Functor.HasPointwiseLeftDerivedFunctor`;
- primitive data: the pointwise-at owners `Functor.HasPointwiseRightDerivedFunctorAt` and
  `Functor.HasPointwiseLeftDerivedFunctorAt`;
- derived API: the everywhere-defined predicates obtained by quantifying those pointwise-at
  owners over all objects.

Source/core/bridge triage:
- `source-facing`: the Stacks Project assertions that the right or left derived functor of `F`
  with respect to `S` is defined everywhere;
- `core/canonical`: `Functor.HasPointwiseRightDerivedFunctor` and
  `Functor.HasPointwiseLeftDerivedFunctor`;
- `bridge/view`: Definition 13.14.2, which records the corresponding pointwise-at owners.

This file should therefore stay as a direct recall of the canonical owner predicates rather than
introducing a parallel local alias or wrapper.
-/

/- Definition 13.14.9: for a functor `F : 𝒟 ⥤ 𝒟'` and a localization class `S`, saying that
`F` is right derivable, or that `RF` is everywhere defined, is the canonical pointwise-everywhere
predicate `F.HasPointwiseRightDerivedFunctor S`, meaning that the right derived functor is
defined at every object of `𝒟`. -/
recall HasPointwiseRightDerivedFunctor
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) : Prop

/- Companion recall: saying that `F` is left derivable, or that `LF` is everywhere defined, is
the canonical predicate `F.HasPointwiseLeftDerivedFunctor S`, meaning that the left derived
functor is defined at every object of `𝒟`. -/
recall HasPointwiseLeftDerivedFunctor
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) : Prop

end

end Functor

end CategoryTheory
