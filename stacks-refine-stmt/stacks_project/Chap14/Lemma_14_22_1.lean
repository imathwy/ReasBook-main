import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.22.1:
- primary domain: simplicial objects as a functor category over `SimplexCategoryᵒᵖ`;
- inspected owner declarations:
  `CategoryTheory.Abelian.functorCategoryAbelian`,
  `CategoryTheory.SimplicialObject`,
  `CategoryTheory.functorCategoryPreadditive`;
- best owner abstraction: the canonical abelian functor-category instance on `SimplicialObject A`;
- primitive data: only the ambient abelian structure on `A`;
- derived API: the induced abelian structure on simplicial objects;
- source/core/bridge triage: the numbered lemma is a `source-facing` recall of the canonical
  owner `Abelian (SimplicialObject A)`. -/

/- Owner recall: the abelian structure on simplicial objects is the canonical functor-category
instance specialized to `SimplexCategoryᵒᵖ ⥤ A`. -/
recall Abelian.functorCategoryAbelian

/- Lemma 14.22.1: simplicial objects in an abelian category form an abelian category. -/
#check (inferInstance : Abelian (SimplicialObject A))

end CategoryTheory
