import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_8_1
import StacksProject_2024.stacks_project.Chap12.Definition_12_27_5

open CategoryTheory
open TopologicalSpace
open scoped TopCat

universe u

noncomputable section

namespace TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Lemma 19.4.1:
- primary domain: enough injectives and functorial injective embeddings for categories of abelian
  sheaves on topological spaces;
- sampled owner declarations:
  `Ab(X)`,
  `EnoughInjectives`,
  `HasFunctorialInjectiveEmbeddings`,
  `Sheaf.isGrothendieckAbelian_of_essentiallySmall`,
  `hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian`;
- best owner abstraction: the source-facing notation `Ab(X)` from Definition 6.8.1, with the
  canonical owner-level properties `EnoughInjectives (Ab(X))` and
  `HasFunctorialInjectiveEmbeddings (Ab(X))`;
- primitive data: the Grothendieck-abelian owner on the sheaf category
  `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`;
- derived API: the canonical `EnoughInjectives` instance from mathlib and the Chapter 12 bridge
  `hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian`.

Source/core/bridge triage:
- `source-facing`: the Stacks notation `Ab(X)` for abelian sheaves on a topological space `X`;
- `core/canonical`: `EnoughInjectives (Ab(X))` and
  `HasFunctorialInjectiveEmbeddings (Ab(X))`;
- `bridge/view`: the Grothendieck-abelian sheaf owner specialized along
  `Opens.grothendieckTopology X`.

This item is a `bridge/view` recall: `Ab(X)` is already a Grothendieck abelian category via the
canonical sheaf owner, so enough injectives and functorial injective embeddings should be recalled
directly on `Ab(X)` rather than through a parallel local specialization wrapper. -/

private abbrev abelianSheaf_isGrothendieckAbelian :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/- Lemma 19.4.1: the category `Ab(X)` of abelian sheaves on a topological space has functorial
injective embeddings; this is the Chapter 12 owner bridge applied to the canonical
Grothendieck-abelian sheaf category `Ab(X)`. -/
#check
  (show HasFunctorialInjectiveEmbeddings (Ab(X)) from by
    change HasFunctorialInjectiveEmbeddings (TopCat.Sheaf AddCommGrpCat.{u} X)
    letI := abelianSheaf_isGrothendieckAbelian X
    simpa [TopCat.Sheaf] using
      (hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian :
        HasFunctorialInjectiveEmbeddings
          (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})))

/- Lemma 19.4.1: the same owner specialization yields enough injectives for `Ab(X)`. -/
#check
  (show EnoughInjectives (Ab(X)) from by
    change EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} X)
    letI := abelianSheaf_isGrothendieckAbelian X
    simpa [TopCat.Sheaf] using
      (inferInstance :
        EnoughInjectives
          (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})))

end TopCat
