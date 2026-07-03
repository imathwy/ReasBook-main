import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_19_4_1 (from Chap19) -/
open CategoryTheory
open TopologicalSpace
open scoped TopCat

universe u

namespace TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Lemma 19.4.1:
- primary domain: enough injectives and functorial injective embeddings for categories of abelian
  sheaves on topological spaces;
- sampled owner declarations:
  `Ab(X)`,
  `EnoughInjectives`,
  `HasFunctorialInjectiveEmbeddings`,
  `siteAbelianSheaf_hasEnoughInjectives`,
  `siteAbelianSheaf_hasFunctorialInjectiveEmbeddings`;
- best owner abstraction: the source-facing notation `Ab(X)` from Definition 6.8.1, with the
  canonical owner-level properties `EnoughInjectives (Ab(X))` and
  `HasFunctorialInjectiveEmbeddings (Ab(X))`;
- primitive data: the site-level enough-injectives theorem specialized to
  `Opens.grothendieckTopology X`;
- derived API: the corresponding functorial-injective-embedding instance on `Ab(X)`.

Source/core/bridge triage:
- `source-facing`: the Stacks notation `Ab(X)` for abelian sheaves on a topological space `X`;
- `core/canonical`: `EnoughInjectives (Ab(X))` and
  `HasFunctorialInjectiveEmbeddings (Ab(X))`;
- `bridge/view`: specialization of the site-level owners along `Opens.grothendieckTopology X`.

This item is a `bridge/view` recall: after importing `Theorem_19_7_4`, both owner-level
properties already exist canonically on `Ab(X)`, so the faithful refinement is to recall those
specializations directly rather than keep parallel local wrappers. -/

/- Lemma 19.4.1: the category `Ab(X)` of abelian sheaves on a topological space has functorial
injective embeddings; this is exactly the site-level owner instance specialized to
`Opens.grothendieckTopology X`. -/
#check
  (siteAbelianSheaf_hasFunctorialInjectiveEmbeddings (Opens.grothendieckTopology X) :
    HasFunctorialInjectiveEmbeddings (Ab(X)))

/- Lemma 19.4.1: the same specialization yields enough injectives for `Ab(X)`. -/
#check
  (siteAbelianSheaf_hasEnoughInjectives (Opens.grothendieckTopology X) :
    EnoughInjectives (Ab(X)))

end TopCat
