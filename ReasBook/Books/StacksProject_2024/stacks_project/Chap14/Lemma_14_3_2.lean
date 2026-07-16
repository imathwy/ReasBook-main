import StacksProject_2024.stacks_project.Chap14.Lemma_14_2_4
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.3.2:
- primary domain: simplicial objects as functors on `SimplexCategoryᵒᵖ`, together with the
  functor-category equivalence induced by an equivalence of indexing categories;
- sampled owner API:
  `inferInstance : SimplexCategoryGenRel.toSimplexCategory.IsEquivalence`,
  `Functor.asEquivalence`,
  `SimplicialObject.δ_naturality`,
  `SimplicialObject.σ_naturality`,
  `SimplicialObject.hom_ext`;
- best owner abstraction:
  `((Functor.whiskeringLeft _ _ C).obj SimplexCategoryGenRel.toSimplexCategory.op).asEquivalence`
  for the source-facing presentation of simplicial objects by generators and relations;
- primitive data: only the canonical functor
  `SimplexCategoryGenRel.toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory`;
- derived API: the induced precomposition equivalence on simplicial objects via
  `Functor.asEquivalence`, plus the naturality and extensionality lemmas for morphisms of
  simplicial objects;
- source/core/bridge triage:
  `source-facing`: the generators-and-relations presentation `SimplexCategoryGenRelᵒᵖ ⥤ C`;
  `core/canonical`: `SimplicialObject C := SimplexCategoryᵒᵖ ⥤ C`;
  `bridge/view`: precomposition along `SimplexCategoryGenRel.toSimplexCategory.op`.
-/

-- Proof sketch: by the canonical instance from Lemma 14.2.4,
-- `SimplexCategoryGenRel.toSimplexCategory` is an equivalence.
-- Precomposition with its opposite is again an equivalence on functor categories via
-- `whiskeringLeft`, and `SimplicialObject C` is definitionally `SimplexCategoryᵒᵖ ⥤ C`.
variable {C : Type u} [Category.{v} C]

/- Lemma 14.3.2: precomposition with the canonical functor
`SimplexCategoryGenRel.toSimplexCategory.op : SimplexCategoryGenRelᵒᵖ ⥤ SimplexCategoryᵒᵖ` is an
equivalence for every category `C`. This is the functor-category formulation of the statement that
simplicial objects in `C` are exactly sequences of objects with face and degeneracy maps
satisfying the simplicial identities, and that morphisms are degreewise families commuting with
these structure maps. The exact owner-level value is the canonical equivalence
`((Functor.whiskeringLeft _ _ C).obj SimplexCategoryGenRel.toSimplexCategory.op).asEquivalence`,
built by `Functor.asEquivalence` from the generic whiskering-left equivalence instance induced
from the canonical instance
`inferInstance : SimplexCategoryGenRel.toSimplexCategory.IsEquivalence`. -/
#check
  ((Functor.whiskeringLeft _ _ C).obj SimplexCategoryGenRel.toSimplexCategory.op).asEquivalence

/- Companion recall: the commutation of the degreewise components of a morphism of simplicial
objects with the face maps is the canonical owner lemma `SimplicialObject.δ_naturality`. -/
recall SimplicialObject.δ_naturality

/- Companion recall: the commutation with the degeneracy maps is the canonical owner lemma
`SimplicialObject.σ_naturality`. -/
recall SimplicialObject.σ_naturality

/- Companion recall: equality of morphisms of simplicial objects from their degreewise components
is already owned by `SimplicialObject.hom_ext`. -/
recall SimplicialObject.hom_ext

end CategoryTheory
