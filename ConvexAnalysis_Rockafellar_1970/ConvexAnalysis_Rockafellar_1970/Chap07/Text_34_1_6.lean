import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3

noncomputable section

universe u v w z

open scoped Rockafellar

namespace SaddleFunction

section ConvexDom₁

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid β] [PartialOrder β] [Bot β]
variable [Module 𝕜 β]
variable [IsOrderedCancelAddMonoid β]
variable [PosSMulStrictMono 𝕜 β]

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.6 states that the first-coordinate and second-coordinate effective
  domains of a concave-convex saddle-function are convex, and deduces convexity and
  finite-valuedness on the product domain.
- `core/canonical`: the chapter already owns the saddle-shape predicate
  `SaddleFunction.IsConcaveConvex 𝕜 K` together with the Chapter 34 source-facing domain owners
  `SaddleFunction.dom₁`, `SaddleFunction.dom₂`, and `SaddleFunction.dom` from `Defn_34_3`.
- `bridge/view`: for each fixed slice, the mathlib strict sublevel/superlevel convexity owners
  `ConvexOn.convex_lt` and `ConcaveOn.convex_gt` give convexity of the slice domain conditions;
  `convex_iInter` then packages the coordinate domains as intersections of those convex slices.

Primary mathematical domain:
- convex analysis of concave-convex saddle-functions and their coordinate effective domains.

Domain-style sampling used here:
- `SaddleFunction.IsConcaveConvex` from `Chap07.Definition33_0_1`;
- the Chapter 34 domain owners `SaddleFunction.dom₁`, `SaddleFunction.dom₂`, and
  `SaddleFunction.dom` from `Chap07.Defn_34_3`;
- `ConcaveOn.convex_gt` and `ConvexOn.convex_lt` from mathlib for strict slice domains;
- `convex_iInter` from mathlib for the coordinate-domain intersections.

Primitive data vs derived API:
- primitive source datum: a bifunction `K : U → X → β` into an ordered codomain with endpoints;
- primitive owner hypothesis: `IsConcaveConvex 𝕜 K`;
- derived API: convexity of `dom₁ K`, convexity of `dom₂ K`, convexity of
  `dom K = dom₁ K ×ˢ dom₂ K`, and finiteness of `K` on that domain.

Layer target: `source-facing`.
-/

-- Proof sketch: unpack `IsConcaveConvex 𝕜 K`. For each fixed `v`, use
-- `ConcaveOn.convex_gt` at level `⊥` to get convexity of the slice set
-- `{u | ⊥ < K u v}`, then intersect those convex slice domains over all `v`.
/-- Text 34.1.6 (1): the first-coordinate effective domain of a concave-convex saddle-function is
a convex set. -/
theorem convex_dom₁_of_isConcaveConvex
    {K : U → X → β} (hK : IsConcaveConvex 𝕜 K) :
    Convex 𝕜 (dom₁ K) := by
  rcases (isConcaveConvex_iff (𝕜 := 𝕜) K).1 hK with ⟨hConcave, _⟩
  simpa [dom₁, Set.iInter_setOf, Set.univ_inter] using
    (convex_iInter (fun v => (hConcave v).convex_gt (⊥ : β)))

end ConvexDom₁

section ConvexDom₂

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid β] [PartialOrder β] [Top β]
variable [Module 𝕜 β]
variable [IsOrderedCancelAddMonoid β]
variable [PosSMulStrictMono 𝕜 β]

-- Proof sketch: unpack `IsConcaveConvex 𝕜 K`. For each fixed `u`, apply
-- `ConvexOn.convex_lt` at level `⊤` to get convexity of the slice set
-- `{v | K u v < ⊤}`, then intersect those convex slice domains over all `u`.
/-- Text 34.1.6 (2): the second-coordinate effective domain of a concave-convex saddle-function is
a convex set. -/
theorem convex_dom₂_of_isConcaveConvex
    {K : U → X → β} (hK : IsConcaveConvex 𝕜 K) :
    Convex 𝕜 (dom₂ K) := by
  rcases (isConcaveConvex_iff (𝕜 := 𝕜) K).1 hK with ⟨_, hConvex⟩
  simpa [dom₂, Set.iInter_setOf, Set.univ_inter] using
    (convex_iInter (fun u => (hConvex u).convex_lt (⊤ : β)))

end ConvexDom₂

section ConvexEffectiveDomain

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid β] [PartialOrder β] [Bot β] [Top β]
variable [Module 𝕜 β]
variable [IsOrderedCancelAddMonoid β]
variable [PosSMulStrictMono 𝕜 β]

-- Proof sketch: `dom K` is definitionally `dom₁ K ×ˢ dom₂ K`, so its convexity
-- follows from the two preceding coordinate-domain convexity statements and the standard product
-- theorem for convex sets.
/-- Text 34.1.6 (3): consequently, `dom K = dom₁ K ×ˢ dom₂ K` is a convex set in the product
space. -/
theorem convex_dom_of_isConcaveConvex
    {K : U → X → β} (hK : IsConcaveConvex 𝕜 K) :
    Convex 𝕜 (dom K) := by
  exact
    (convex_dom₁_of_isConcaveConvex hK).prod
      (convex_dom₂_of_isConcaveConvex hK)

end ConvexEffectiveDomain

section FiniteOnEffectiveDomain

variable {U : Type u} {X : Type v} {β : Type w}
variable [LT β] [Bot β] [Top β]

/-- Text 34.1.6 (4): if `u ∈ dom₁ K` and `v ∈ dom₂ K`, then `K u v` is finite, i.e.
`⊥ < K u v` and `K u v < ⊤`. This is a direct consequence of the Chapter 34 coordinate-domain
owners and does not require the concave-convex shape hypothesis. -/
theorem bot_lt_and_lt_top_of_mem_dom₁_of_mem_dom₂
    {K : U → X → β} {u : U} {v : X}
    (hu : u ∈ dom₁ K) (hv : v ∈ dom₂ K) :
    ⊥ < K u v ∧ K u v < ⊤ :=
  ⟨hu v, hv u⟩

/-- Equivalent product-domain form of the finiteness clause in Text 34.1.6. -/
theorem bot_lt_and_lt_top_of_mem_dom
    {K : U → X → β} {p : U × X}
    (hp : p ∈ dom K) :
    ⊥ < K p.1 p.2 ∧ K p.1 p.2 < ⊤ := by
  rcases hp with ⟨hp₁, hp₂⟩
  exact bot_lt_and_lt_top_of_mem_dom₁_of_mem_dom₂ hp₁ hp₂

end FiniteOnEffectiveDomain

end SaddleFunction
