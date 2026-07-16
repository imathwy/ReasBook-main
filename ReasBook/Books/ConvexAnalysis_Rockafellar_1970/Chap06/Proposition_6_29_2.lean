import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8

universe u v w z

namespace Bifunction

open Function

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: this item identifies the bifunction domain `dom F` with
  the first-coordinate projection of the graph domain and then records the resulting convexity
  statement for convex bifunctions.
- `core/canonical`: the already-built owners available here are the Chapter 6 bifunction-domain
  owner `dom F` from Definition 6.29.8 and the Chapter 1 graph-domain notation
  `dom(uncurry F)` from Definition 6.29.7.
- `bridge/view`: the proposition is the direct owner bridge from `dom F` to the
  canonical graph-domain image.

Domain-style sampling used here:
- `dom(uncurry F)`;
- convexity of the graph-domain owner `dom(uncurry F)`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` into a codomain carrying `⊤` and `<`;
- source-facing owner available in this file: `dom F`;
- canonical owner available in this file: `dom(uncurry F)`.

Layer target: `bridge/view`, stated directly in the source-facing set language while reusing the
canonical graph-domain owner.
-/

/-- Membership in the bifunction domain is equivalent to the existence of a graph-domain point of
`uncurry F` above the same parameter. -/
@[simp] theorem mem_dom_iff_exists_mem_dom_uncurry
    {F : U → X → β} {u : U} :
    u ∈ dom F ↔ ∃ x : X, (u, x) ∈ dom(uncurry F) := by
  rw [mem_dom]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [uncurry] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [uncurry] using hx⟩

/-- Proposition 6.29.2: the set of parameters admitting a finite slice value is the
first-coordinate projection of the graph domain of the bifunction. -/
theorem dom_eq_image_fst_dom_uncurry (F : U → X → β) :
    dom F = Prod.fst '' dom(uncurry F) := by
  ext u
  constructor
  · intro hu
    rcases (mem_dom_iff_exists_mem_dom_uncurry (F := F) (u := u)).1 hu with ⟨x, hx⟩
    exact ⟨(u, x), hx, rfl⟩
  · rintro ⟨⟨u', x⟩, hx, rfl⟩
    exact (mem_dom_iff_exists_mem_dom_uncurry (F := F) (u := u')).2 ⟨x, hx⟩

end

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [Top β] [LT β]

-- Proof sketch: transport convexity from `dom(uncurry F)` to `dom F` across
-- `dom_eq_image_fst_dom_uncurry`.
/-- If the graph-domain owner `dom(uncurry F)` is convex, then the parameter-domain owner
`dom F` is convex. -/
theorem convex_dom {F : U → X → β}
    (hdom_uncurry : Convex 𝕜 (dom(uncurry F))) :
    Convex 𝕜 (dom F) := by
  rw [dom_eq_image_fst_dom_uncurry]
  rw [convex_iff_add_mem]
  rintro _ ⟨⟨u₁, x₁⟩, hx₁, rfl⟩ _ ⟨⟨u₂, x₂⟩, hx₂, rfl⟩ a b ha hb hab
  exact ⟨a • (u₁, x₁) + b • (u₂, x₂), hdom_uncurry hx₁ hx₂ ha hb hab, rfl⟩

end

end Bifunction
