import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_5

open Set
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.5.6 starts from the chapter domain hypothesis
  `p ∈ interior (dom K)` for saddle bifunctions.
- `core/canonical`: directional-derivative APIs act on the product function
  `Function.uncurry K` and consume the graph-domain owner `dom(uncurry K)`.
- `bridge/view`: this file records the direct owner bridge from the Chapter 34 saddle domain
  `dom K` (and its ambient/intrinsic interior variants) to the graph-domain owner
  `dom(uncurry K)`.

Ambient-vs-relative topology choice:
- The chapter clause `p ∈ interior (dom K)` is retained as source input.
- The intrinsic surface `p ∈ ri[𝕜](dom K)` is retained as the reusable topology owner.
- Both feed the same graph-domain target owner `dom(uncurry K)`.

Domain-style sampling used here:
- `SaddleFunction.dom`;
- `dom(uncurry K)`;
- `ri[𝕜](·)`;
- `interior_subset`.

Primitive data vs derived API:
- primitive owner data already exist upstream: `SaddleFunction.dom K`,
  `dom(uncurry K)`, and `ri[𝕜](dom K)`;
- derived API here: bridge lemmas from `dom K`, `interior (dom K)`, and `ri[𝕜](dom K)` into
  `dom(uncurry K)`.

Layer target: `bridge/view`.
-/

recall SaddleFunction.dom
recall SaddleFunction.mem_dom

/- Text 35.5.6 reuses the ambient-to-intrinsic `dom K` bridge from Text 35.5.5. -/
recall SaddleFunction.interior_dom_subset_ri_dom
recall SaddleFunction.mem_ri_dom_of_mem_interior_dom

namespace SaddleFunction

universe u v

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [LT α] [Bot α] [Top α]

/-- Bridge from the Chapter 34 product-domain owner to the graph-domain owner of `uncurry K`. -/
theorem mem_dom_uncurry_of_mem_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ dom K) :
    p ∈ dom(Function.uncurry K) := by
  exact (SaddleFunction.mem_dom.mp hp).2 p.1

end

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace (U × X)]
variable [LT α] [Bot α] [Top α]

/-- Interior points of the Chapter 34 product-domain owner are interior points for
`dom(uncurry K)`. -/
theorem interior_dom_subset_interior_dom_uncurry
    (K : U → X → α) :
    interior (dom K) ⊆ interior (dom(Function.uncurry K)) :=
  interior_mono (fun _ hp => mem_dom_uncurry_of_mem_dom hp)

/-- Pointwise form of `interior_dom_subset_interior_dom_uncurry`. -/
theorem mem_dom_uncurry_of_mem_interior_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ interior (dom K)) :
    p ∈ dom(Function.uncurry K) :=
  mem_dom_uncurry_of_mem_dom (interior_subset hp)

end

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {U : Type u} {X : Type v} {E : Type*} {α : Type*}
variable [TopologicalSpace (U × X)]
variable [AddCommGroup E] [Module 𝕜 E] [AddTorsor E (U × X)]
variable [LT α] [Bot α] [Top α]

/-- Intrinsic-interior bridge for Text 35.5.6 in subset form. -/
theorem ri_dom_subset_dom_uncurry
    {K : U → X → α} :
    ri[𝕜](dom K) ⊆ dom(Function.uncurry K) :=
  fun _ hp => mem_dom_uncurry_of_mem_dom (intrinsicInterior_subset hp)

/-- Pointwise form of `ri_dom_subset_dom_uncurry`. -/
theorem mem_dom_uncurry_of_mem_ri_dom
    {K : U → X → α} {p : U × X}
    (hp : p ∈ ri[𝕜](dom K)) :
    p ∈ dom(Function.uncurry K) :=
  ri_dom_subset_dom_uncurry hp

end

end SaddleFunction
