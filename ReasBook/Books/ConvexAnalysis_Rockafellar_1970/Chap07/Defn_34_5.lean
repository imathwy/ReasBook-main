import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8

universe u v

open scoped Rockafellar

namespace SaddleFunction

section

variable {U : Type u} {V : Type v}
variable {EU EV : Type*}
variable {α : Type*} [Preorder α] [Neg α]

/- Rockafellar-style notation for intrinsic closure at scalar layer `𝕜`. -/
scoped[Rockafellar] notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

/-!
Source/core/bridge triage:

- `source-facing`: Definition 34.5 introduces the notion of a simple concave-convex
  saddle-function through the two domain conditions on the slices `K(u, ·)` and `K(·, v)`.
- `core/canonical`: the Chapter 34 owner layer for the saddle-function domains is already
  `SaddleFunction.dom₁` and `SaddleFunction.dom₂` from `Defn_34_3`, while the one-variable slice
  effective domains are already owned by `dom(·)`.
- `bridge/view`: no new bridge owner is needed here; simplicity is a source-facing property
  stated directly in terms of those canonical domain owners.

Domain-style sampling used here:
- `SaddleFunction.dom₁` and `SaddleFunction.dom₂` from `Chap07.Defn_34_3`;
- `dom(·)` from `ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4`;
- the scoped intrinsic-closure notation `cl[𝕜](·)` for `intrinsicClosure 𝕜`;
- `dom(-g)` as the concave-side slice effective domain pattern already used throughout Chapter 6.

Primitive data vs derived API:
- primitive source datum: a bifunction `K : U → V → WithTopBot α` at the canonical ordered
  extended-codomain layer, on an intrinsic affine ambient layer for the
  relative-interior/closure operators;
- primitive owner reused from upstream: `dom₁` and `dom₂`;
- primitive source-facing property introduced here: `IsSimple`;
- derived API: the specification theorem `isSimple_iff` and projection lemmas for the two
  simplicity clauses, while the global domain owners are already provided canonically upstream.

Layer target: `source-facing`. This file adds the textbook simplicity predicate, owned directly by
the existing Chapter 34 saddle-function domain layer at the primitive codomain level needed for
`dom₁`, `dom₂`, and slice negation.
-/

/-- Definition 34.5's source-facing owner predicate: a concave-convex saddle-function is simple
when, for every `u ∈ ri[𝕜](dom₁ K)`, the effective domain of the convex slice `K(u, ·)` is
contained in `cl[𝕜](dom₂ K)`, and symmetrically for every `v ∈ ri[𝕜](dom₂ K)` the
effective domain of the concave slice `-K(·, v)` is contained in
`cl[𝕜](dom₁ K)`. -/
def IsSimple (𝕜 : Type*) [Ring 𝕜]
    [AddCommGroup EU] [Module 𝕜 EU] [TopologicalSpace U] [AddTorsor EU U]
    [AddCommGroup EV] [Module 𝕜 EV] [TopologicalSpace V] [AddTorsor EV V]
    (K : U → V → WithTopBot α) : Prop :=
  (∀ {u : U}, u ∈ ri[𝕜](dom₁ K) →
      dom(K u) ⊆ cl[𝕜](dom₂ K)) ∧
    ∀ {v : V}, v ∈ ri[𝕜](dom₂ K) →
      dom(-K(·, v)) ⊆ cl[𝕜](dom₁ K)

/-- Unpacking form of `IsSimple`: each side is the corresponding slice-domain containment clause
on `ri[𝕜](dom₁ K)` and `ri[𝕜](dom₂ K)`. -/
theorem isSimple_iff
    {𝕜 : Type*} [Ring 𝕜]
    [AddCommGroup EU] [Module 𝕜 EU] [TopologicalSpace U] [AddTorsor EU U]
    [AddCommGroup EV] [Module 𝕜 EV] [TopologicalSpace V] [AddTorsor EV V]
    {K : U → V → WithTopBot α} :
    IsSimple 𝕜 K ↔
      (∀ ⦃u : U⦄, u ∈ ri[𝕜](dom₁ K) →
        dom(K u) ⊆ cl[𝕜](dom₂ K)) ∧
      ∀ ⦃v : V⦄, v ∈ ri[𝕜](dom₂ K) →
        dom(-K(·, v)) ⊆ cl[𝕜](dom₁ K) :=
  Iff.rfl

/-- The right-slice clause of simplicity. -/
theorem IsSimple.right_slice_dom_subset
    {𝕜 : Type*} [Ring 𝕜]
    [AddCommGroup EU] [Module 𝕜 EU] [TopologicalSpace U] [AddTorsor EU U]
    [AddCommGroup EV] [Module 𝕜 EV] [TopologicalSpace V] [AddTorsor EV V]
    {K : U → V → WithTopBot α} (hK : IsSimple 𝕜 K)
    {u : U} (hu : u ∈ ri[𝕜](dom₁ K)) :
    dom(K u) ⊆ cl[𝕜](dom₂ K) :=
  hK.1 hu

/-- The left-slice clause of simplicity. -/
theorem IsSimple.left_slice_dom_subset
    {𝕜 : Type*} [Ring 𝕜]
    [AddCommGroup EU] [Module 𝕜 EU] [TopologicalSpace U] [AddTorsor EU U]
    [AddCommGroup EV] [Module 𝕜 EV] [TopologicalSpace V] [AddTorsor EV V]
    {K : U → V → WithTopBot α} (hK : IsSimple 𝕜 K)
    {v : V} (hv : v ∈ ri[𝕜](dom₂ K)) :
    dom(-K(·, v)) ⊆ cl[𝕜](dom₁ K) :=
  hK.2 hv

end

end SaddleFunction
