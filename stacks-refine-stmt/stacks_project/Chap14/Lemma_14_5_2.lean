import stacks_project.Chap14.Lemma_14_2_4
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open SimplexCategoryGenRel

/- Domain-style sampling for Lemma 14.5.2:
- primary domain: cosimplicial objects as functors on `SimplexCategory`, together with the
  functor-category equivalence induced by an equivalence of indexing categories;
- sampled owner API:
  `Functor.asEquivalence`,
  `Functor.whiskeringLeft`,
  `inferInstance : toSimplexCategory.IsEquivalence`,
  `CosimplicialObject.σ_naturality`,
  `CosimplicialObject.δ_naturality`,
  `CosimplicialObject.hom_ext`;
- best owner abstractions:
  `((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence` for the source-facing
  presentation of cosimplicial objects by generators and relations, and `CosimplicialObject` for
  the coface/codegeneracy and morphism API;
- primitive data: only the canonical functor
  `toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory`;
- derived API: the induced precomposition equivalence on cosimplicial objects via
  `Functor.whiskeringLeft` and `Functor.asEquivalence`, plus the naturality and extensionality
  lemmas for morphisms of cosimplicial objects;
- source/core/bridge triage:
  `source-facing`: the generators-and-relations presentation `SimplexCategoryGenRel ⥤ C`;
  `core/canonical`: `CosimplicialObject C := SimplexCategory ⥤ C`;
  `bridge/view`: precomposition along `toSimplexCategory`.
-/

-- Proof sketch: by the canonical instance from Lemma 14.2.4,
-- `toSimplexCategory` is an equivalence.
-- The induced source-change equivalence on functor categories is the canonical owner
-- `((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence`, and
-- `CosimplicialObject C` is definitionally `SimplexCategory ⥤ C`.
variable {C : Type u} [Category.{v} C]

/- Lemma 14.5.2: precomposition with the canonical functor
`toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory` is an
equivalence for every category `C`. This is the functor-category formulation of the statement that
cosimplicial objects in `C` are exactly sequences of objects with coface and codegeneracy maps
satisfying the cosimplicial identities, and that morphisms are degreewise families commuting with
these structure maps. The exact owner-level value is the canonical source-change equivalence
`((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence`, built by
`Functor.asEquivalence` from the generic whiskering-left equivalence instance induced from the
canonical instance `inferInstance : toSimplexCategory.IsEquivalence`. -/
#check
  ((Functor.whiskeringLeft _ _ C).obj toSimplexCategory).asEquivalence

/- Companion recall: the commutation of the degreewise components of a morphism of cosimplicial
objects with the coface maps is the canonical owner lemma `CosimplicialObject.δ_naturality`. -/
recall CosimplicialObject.δ_naturality

/- Companion recall: the commutation with the codegeneracy maps is the canonical owner lemma
`CosimplicialObject.σ_naturality`. -/
recall CosimplicialObject.σ_naturality

/- Companion recall: equality of morphisms of cosimplicial objects from their degreewise
components is already owned by `CosimplicialObject.hom_ext`. -/
recall CosimplicialObject.hom_ext

end CategoryTheory
