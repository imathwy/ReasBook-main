import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory
open scoped Simplicial

section

variable (C : Type u) [Category.{v} C] (X : C)
variable (n : ℕ)

/- Domain-style sampling for Example 14.5.4:
- primary domain: cosimplicial objects as functors on `SimplexCategory`;
- sampled owner API:
  `CosimplicialObject`,
  `CosimplicialObject.const`,
  `CosimplicialObject.Augmented.const`,
  `SimplicialObject.const`;
- best owner abstraction: the mathlib owner functor
  `CosimplicialObject.const : C ⥤ CosimplicialObject C`;
- source/core/bridge triage:
  `source-facing`: the textbook constant cosimplicial object on `X`;
  `core/canonical`: the owner functor `CosimplicialObject.const`;
  `bridge/view`: the degreewise equalities showing that every term is `X` and every structure map
  is `𝟙 X`.

Primitive data are only the ambient category `C` and the object `X`. The degreewise object and map
descriptions are derived directly from the constant-functor owner, so this file should expose the
source-facing object `(CosimplicialObject.const C).obj X` directly and keep the owner functor only
as companion context rather than introduce any parallel local wrapper.
-/

/- Example 14.5.4: the simplest cosimplicial object with value `X` is the constant cosimplicial
object `(CosimplicialObject.const C).obj X`; equivalently, every term is `X` and every
cosimplicial structure map is `𝟙 X`. -/
#check ((CosimplicialObject.const C).obj X)

/- Companion recall: the owner of constant cosimplicial objects is the functor
`CosimplicialObject.const : C ⥤ CosimplicialObject C`. -/
recall CosimplicialObject.const

/- Companion check: the degree `n` term of the constant cosimplicial object is definitionally
`X`. -/
#check (rfl : ((CosimplicialObject.const C).obj X) ^⦋n⦌ = X)

/- Companion check: each cosimplicial structure map of the constant cosimplicial object is
definitionally `𝟙 X`. -/
#check (fun {Δ Δ' : SimplexCategory} (φ : Δ ⟶ Δ') ↦
  show ((CosimplicialObject.const C).obj X).map φ = 𝟙 X from rfl)

end
