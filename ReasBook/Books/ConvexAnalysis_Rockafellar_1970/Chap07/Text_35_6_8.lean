import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_5

universe u v

namespace SaddleFunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace U] [LT α] [Top α]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.8 concludes that an interior point of `dom K` yields interior
  membership in the effective domains of the first- and second-variable slices.
- `core/canonical`: the owner abstractions already exist upstream as `SaddleFunction.dom₂ K` and
  the one-variable slice-domain owner `dom(·)`, together with the primitive slice-domain bridges
  `dom_firstSlice_eq_univ` and `dom₂_subset_dom_secondSlice`.
- `bridge/view`: the first-slice clause first factors through the primitive owner fact
  `v ∈ dom₂ K`, because `dom_firstSlice_eq_univ` already upgrades that to full slice domain; a
  source-facing bridge then reuses this at `v ∈ interior (dom₂ K)`. The second-slice clause is
  the genuine interior bridge from `v ∈ interior (dom₂ K)`.

Domain-style sampling used here:
- `SaddleFunction.dom₂` and the slice-domain bridges
  `dom_firstSlice_eq_univ` / `dom₂_subset_dom_secondSlice` from `Chap07.Defn_34_3`;
- `SaddleFunction.mem_interior_dom` from `Chap07.Text_35_5_5`;
- `dom(·)` from `Chap01.Definition_4_4`;
- `interior_mono` from mathlib.

Primitive data vs derived API:
- primitive owner data already exist upstream: `dom₂ K` and the slice-domain bridges
  `dom_firstSlice_eq_univ` and `dom₂_subset_dom_secondSlice`;
- derived API here: the first-slice interior conclusion both from `v ∈ dom₂ K` and from
  `v ∈ interior (dom₂ K)`, and the second-slice interior conclusion from
  `v ∈ interior (dom₂ K)`.

Codomain owner level:
- the slice-domain owners above are already stated for a generic codomain carrying only `⊤` and
  `<`, so this file should stay on that same owner layer rather than specialize to
  `WithBotTop α`.

Layer target: `bridge/view`.

Redundant-source-assumption elimination:
- the textbook hypothesis `(u, v) ∈ interior (dom K)` is not kept in the main declarations,
  because `mem_interior_dom` isolates the second-coordinate owner information;
- the first-slice owner theorem does not keep the stronger interior hypothesis on `dom₂ K`,
  because `dom_firstSlice_eq_univ` already yields the full slice domain from plain
  `v ∈ dom₂ K`; a separate source-facing bridge recovers the interior-hypothesis form;
- the second-slice clause keeps the interior hypothesis `v ∈ interior (dom₂ K)`.
-/

/-- Text 35.6.8, owner form: if `v` lies in the second-coordinate domain of `K`, then every
first-variable slice `K(·, v)` has full effective domain, so any `u` lies in its
interior domain. -/
theorem interior_dom_firstSlice_eq_univ_of_mem_dom₂
    (K : U → X → α) {v : X} (hv : v ∈ dom₂ K) :
    interior (dom(K(·, v))) = Set.univ := by
  simp [dom_firstSlice_eq_univ K hv]

/-- Text 35.6.8, pointwise bridge: if `v` lies in the second-coordinate domain of `K`, then every
first-variable slice `K(·, v)` has full interior domain. -/
theorem mem_interior_dom_firstSlice_of_mem_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ dom₂ K) :
    u ∈ interior (dom(K(·, v))) := by
  simp [interior_dom_firstSlice_eq_univ_of_mem_dom₂ K hv]

end

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace U] [TopologicalSpace X] [LT α] [Top α]

/-- Text 35.6.8, source-facing bridge for the first slice: interior membership in `dom₂ K`
implies interior membership in the effective domain of every first-variable slice. -/
theorem mem_interior_dom_firstSlice_of_mem_interior_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ interior (dom₂ K)) :
    u ∈ interior (dom(K(·, v))) :=
  mem_interior_dom_firstSlice_of_mem_dom₂ (interior_subset hv)

end

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [TopologicalSpace X] [LT α] [Top α]

/-- Text 35.6.8, owner form: for each fixed `u`, the interior of the second-coordinate domain
`dom₂ K` is contained in the interior of the effective domain of the second-variable slice `K u`. -/
theorem interior_dom₂_subset_interior_dom_secondSlice
    (K : U → X → α) (u : U) :
    interior (dom₂ K) ⊆ interior (dom(K u)) :=
  interior_mono (dom₂_subset_dom_secondSlice (K := K) (u := u))

/-- Text 35.6.8, pointwise bridge: interior points of `dom₂ K` remain interior points in the
effective domain of each second-variable slice `K u`. -/
theorem mem_interior_dom_secondSlice_of_mem_interior_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ interior (dom₂ K)) :
    v ∈ interior (dom(K u)) :=
  interior_dom₂_subset_interior_dom_secondSlice K u hv

end

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {U : Type u} {X : Type v} {EV : Type*} {α : Type*}
variable [TopologicalSpace X]
variable [AddCommGroup EV] [Module 𝕜 EV] [AddTorsor EV X]
variable [LT α] [Top α]

/-- Intrinsic bridge for Text 35.6.8 on the textbook owner surface `riDom`: interior points of
`dom₂ K` lie in the intrinsic interior domain of each second-variable slice `K u`. -/
theorem interior_dom₂_subset_riDom_secondSlice
    (K : U → X → α) (u : U) :
    interior (dom₂ K) ⊆ riDom[𝕜](K u) := by
  intro v hv
  exact interior_subset_intrinsicInterior
    (interior_dom₂_subset_interior_dom_secondSlice K u hv)

/-- Pointwise intrinsic bridge for Text 35.6.8. -/
theorem mem_riDom_secondSlice_of_mem_interior_dom₂
    {K : U → X → α} {u : U} {v : X}
    (hv : v ∈ interior (dom₂ K)) :
    v ∈ riDom[𝕜](K u) :=
  interior_dom₂_subset_riDom_secondSlice K u hv

end

end SaddleFunction
