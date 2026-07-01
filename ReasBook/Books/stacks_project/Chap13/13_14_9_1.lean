import Mathlib.Tactic.Recall
import stacks_project.Chap13.Definition_13_14_9

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {𝒟 : Type u₁} {𝒟' : Type u₂} [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
variable (S : MorphismProperty 𝒟) (F : 𝒟 ⥤ 𝒟')

/-
Domain-style sampling for 13.14.9.1:
- primary domain: derived functors of a functor `F : 𝒟 ⥤ 𝒟'` along the localization of a
  morphism property `S`;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctor`,
  `Functor.HasPointwiseLeftDerivedFunctor`,
  `Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`,
  `Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor`,
  `Functor.totalRightDerived`,
  `Functor.totalLeftDerived`,
  and the chapter recall file `Definition_13_14_9`;
- best owner abstraction: the generic mathlib owners `Functor.totalRightDerived` and
  `Functor.totalLeftDerived`, specialized to the localization functor `S.Q : 𝒟 ⥤ S.Localization`,
  with the source-facing “everywhere defined” hypotheses supplied first by Chapter `13`'s
  canonical recall `Definition_13_14_9` and then by the canonical bridge instances from
  pointwise to total derived functors;
- primitive data: the underived functor `F`, the morphism property `S`, and the localization
  functor `S.Q`, together with the pointwise-everywhere owner predicates;
- derived API: the total existence predicates `Functor.HasRightDerivedFunctor`,
  `Functor.HasLeftDerivedFunctor` obtained canonically from
  `Functor.HasPointwiseRightDerivedFunctor`, `Functor.HasPointwiseLeftDerivedFunctor`, and the
  resulting total derived functors.

Source/core/bridge triage:
- `source-facing`: the canonical functors `RF : S.Localization ⥤ 𝒟'` and
  `LF : S.Localization ⥤ 𝒟'`, under the source hypothesis that they are everywhere defined;
- `core/canonical`: `Functor.totalRightDerived` and `Functor.totalLeftDerived`;
- `bridge/view`: Definition `13.14.9`, which records the pointwise-everywhere predicates
  `Functor.HasPointwiseRightDerivedFunctor` and `Functor.HasPointwiseLeftDerivedFunctor`, and the
  mathlib bridge instances turning those predicates into total derived-functor existence.

Primitive data is already owned by the generic derived-functor framework. This file should not
introduce any local wrapper for `RF` or `LF`; it should simply expose the source-facing
specializations of the canonical owner declarations on `S.Localization`.
-/

section Right

variable [F.HasPointwiseRightDerivedFunctor S]

/- The canonical bridge from Definition `13.14.9` upgrades “pointwise everywhere defined” to the
global existence predicate for the total right derived functor. -/
recall Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor

/- Canonical owner recall: the right derived functor is the generic owner declaration
`Functor.totalRightDerived`, specialized below to the localization functor `S.Q`. -/
recall Functor.totalRightDerived

/- 13.14.9.1: if the right derived functor of `F : 𝒟 ⥤ 𝒟'` with respect to the localization
`S` is everywhere defined, then it is the canonical functor
`F.totalRightDerived S.Q S : S.Localization ⥤ 𝒟'`, i.e. the Lean formalization of
`RF : S^{-1}\mathcal{D} ⟶ \mathcal{D}'`. The corresponding left-derived variant is recorded
below as a companion check. -/
#check (F.totalRightDerived S.Q S : S.Localization ⥤ 𝒟')

end Right

section Left

variable [F.HasPointwiseLeftDerivedFunctor S]

/- The canonical bridge from Definition `13.14.9` upgrades “pointwise everywhere defined” to the
global existence predicate for the total left derived functor. -/
recall Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor

/- Canonical owner recall: the left derived functor is the generic owner declaration
`Functor.totalLeftDerived`, specialized below to the localization functor `S.Q`. -/
recall Functor.totalLeftDerived

/- Companion check: the corresponding left derived functor everywhere defined on the localization
is `F.totalLeftDerived S.Q S : S.Localization ⥤ 𝒟'`. -/
#check (F.totalLeftDerived S.Q S : S.Localization ⥤ 𝒟')

end Left

end CategoryTheory
