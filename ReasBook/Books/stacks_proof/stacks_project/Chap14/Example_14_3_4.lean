import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory

section

variable (C : Type u) [Category.{v} C] (X : C)

/- Domain-style sampling for Example 14.3.4:
- primary domain: simplicial objects as presheaves on `SimplexCategory`;
- sampled owner API:
  `CategoryTheory.Functor.const`,
  `SimplicialObject.const`,
  `SimplicialObject.Augmented.const`,
  `CosimplicialObject.const`;
- best owner abstraction: the mathlib owner functor
  `SimplicialObject.const : C ⥤ SimplicialObject C`;
- source/core/bridge triage:
  `source-facing`: the textbook constant simplicial object on `X`;
  `core/canonical`: the owner functor `SimplicialObject.const`;
  `bridge/view`: the degreewise equalities showing that every term is `X` and every structure map
  is `𝟙 X`.

Primitive data are only the ambient category `C` and the object `X`. The degreewise object and map
descriptions are derived directly from the constant-functor owner, so this file should expose the
source-facing object `(SimplicialObject.const C).obj X` directly and keep the owner functor only
as companion context rather than introduce any parallel local wrapper.
-/

/- Example 14.3.4: the simplest simplicial object with value `X` is the constant simplicial
object `(SimplicialObject.const C).obj X`; equivalently, every term is `X` and every simplicial
structure map is `𝟙 X`. -/
#check ((SimplicialObject.const C).obj X)

/- Companion recall: the owner of constant simplicial objects is the functor
`SimplicialObject.const : C ⥤ SimplicialObject C`. -/
recall SimplicialObject.const

/- Companion check: each degree of the constant simplicial object is definitionally `X`. -/
#check (fun (Δ : SimplexCategoryᵒᵖ) ↦
  show ((SimplicialObject.const C).obj X).obj Δ = X from rfl)

/- Companion check: each simplicial structure map of the constant simplicial object is
definitionally `𝟙 X`. -/
#check (fun {Δ Δ' : SimplexCategoryᵒᵖ} (φ : Δ ⟶ Δ') ↦
  show ((SimplicialObject.const C).obj X).map φ = 𝟙 X from rfl)

end
