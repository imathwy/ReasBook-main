import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3

open Set
open scoped Rockafellar

universe u v

namespace SaddleFunction

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace U] [TopologicalSpace X] [LT α] [Bot α] [Top α]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.5 restricts the later discussion to interior points of `dom K`.
- `core/canonical`: Chapter 34 already owns the product domain as `SaddleFunction.dom K`, and
  mathlib already owns ordinary product interiors through `interior_prod_eq`.
- `bridge/view`: this file specializes those existing owners to the Chapter 34 domain and also
  records the ambient-to-intrinsic interior bridge at the same owner surface `dom K`.

Domain-style sampling used here:
- `SaddleFunction.dom₁` from `Chap07.Defn_34_3`;
- `SaddleFunction.dom₂` from `Chap07.Defn_34_3`;
- the Chapter 34 owner/notation `dom K` from `Chap07.Defn_34_3`;
- `interior_prod_eq` and `interior_subset_intrinsicInterior` from mathlib.

Primitive data vs derived API:
- primitive owner data already exist upstream: `dom₁ K`, `dom₂ K`, and `dom K`;
- derived API here: the ordinary-interior product description and ambient-to-intrinsic bridge for
  the existing owner `dom K`.

Layer target: `bridge/view`.
-/

/- Text 35.5.5 uses the already existing Chapter 34 owner `dom K`, while ordinary interior on a
product is the canonical mathlib theorem `interior_prod_eq`. -/
recall interior_prod_eq

@[simp] theorem interior_dom (K : U → X → α) :
    interior (dom K) = interior (dom₁ K) ×ˢ interior (dom₂ K) := by
  simpa [SaddleFunction.dom] using interior_prod_eq (s := dom₁ K) (t := dom₂ K)

@[simp] theorem mem_interior_dom {K : U → X → α} {p : U × X} :
    p ∈ interior (dom K) ↔
      p.1 ∈ interior (dom₁ K) ∧ p.2 ∈ interior (dom₂ K) := by
  simp [interior_dom]

@[simp] theorem mem_interior_dom_mk {K : U → X → α} {u : U} {v : X} :
    (u, v) ∈ interior (dom K) ↔
      u ∈ interior (dom₁ K) ∧ v ∈ interior (dom₂ K) := by
  exact mem_interior_dom (K := K) (p := (u, v))

end

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {U : Type u} {X : Type v} {E : Type*} {α : Type*}
variable [TopologicalSpace (U × X)]
variable [AddCommGroup E] [Module 𝕜 E] [AddTorsor E (U × X)]
variable [LT α] [Bot α] [Top α]

/-- Ambient interior of `dom K` sits inside the intrinsic interior of the same owner. -/
theorem interior_dom_subset_ri_dom {K : U → X → α} :
    interior (dom K) ⊆ ri[𝕜](dom K) :=
  interior_subset_intrinsicInterior

/-- Pointwise form of `interior_dom_subset_ri_dom`. -/
theorem mem_ri_dom_of_mem_interior_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ interior (dom K)) :
    p ∈ ri[𝕜](dom K) :=
  interior_dom_subset_ri_dom hp

end

end SaddleFunction
