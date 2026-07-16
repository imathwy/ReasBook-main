import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1

universe u v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.8 introduces the effective domain of a bifunction `F` as the
  set of parameters `u` for which the slice `F u` is not identically `⊤`.
- `core/canonical`: the generalized program attached to `F` already owns the perturbation
  function `perturbationFunction F` from Definition 6.29.1, so its parameter domain should bridge
  to the chapter owner `dom(perturbationFunction F)`. At the slice level, Chapter 1 already fixes
  one-variable effective domains through the owner `dom(·)`.
- `bridge/view`: the defining slice condition is the nonemptiness of `dom(F u)`, and on the
  complete-lattice codomain layer this is exactly membership in `dom(perturbationFunction F)`. The
  source phrase “`F u` is not identically `+∞`” is the derived value-level criterion
  `∃ x, F u x < ⊤`.

Domain-style sampling used here:
- `effectiveDomain`, `dom(·)`, and `mem_effectiveDomain` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4`;
- `perturbationFunction` and `perturbationFunction_apply` from
  `ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1`;
- mathlib's canonical indexed-infimum bridge `iInf_lt_top`;
- `Set.Nonempty` as the canonical owner for nonempty slice effective domains.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- source-facing owner introduced here: `Bifunction.dom F`;
- canonical defining owner expression: `{u | (dom(F u)).Nonempty}`;
- core generalized-program owner under `[CompleteLattice β]`:
  `dom(perturbationFunction F)`;
- derived API: the nonempty-slice-domain membership test, the direct owner bridge to
  `dom(perturbationFunction F)`, the corresponding interior / relative-interior transport, and the
  source-facing existence criterion `∃ x, F u x < ⊤`.

Notation decision:
- the source-facing owner is exported through the scoped textbook surface `dom F`, so immediate
  downstream files can use the bifunction-domain notation without relying on namespace-local name
  resolution; the slice domains continue to use the Chapter 1 notation `dom(F u)`.

Layer target: `source-facing`, built directly from the existing one-variable effective-domain owner
and explicitly bridged to the chapter's core generalized-program owner
`dom(perturbationFunction F)`.
-/

/-- Definition 6.29.8: the domain of a bifunction `F` is the set of parameters `u` for which the
slice `F u` has nonempty effective domain, equivalently is not identically `⊤`. -/
def dom (F : U → X → β) : Set U :=
  {u | (dom(F u)).Nonempty}

/- Rockafellar's source-facing notation for the effective domain of a bifunction. -/
scoped[Rockafellar] prefix:max "dom " => Bifunction.dom

/-- A parameter lies in the domain of a bifunction exactly when the effective domain of the
corresponding slice is nonempty. -/
@[simp] theorem mem_dom {F : U → X → β} {u : U} :
    u ∈ dom F ↔ (dom(F u)).Nonempty :=
  Iff.rfl

/-- A parameter lies in the domain of a bifunction exactly when some value of the
corresponding slice is strictly below `⊤`. -/
@[simp] theorem mem_dom_iff_exists {F : U → X → β} {u : U} :
    u ∈ dom F ↔ ∃ x : X, F u x < ⊤ := by
  rw [mem_dom]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩

section

variable [Zero U]
variable {β : Type w} [Top β] [LT β]

/-- The generalized convex program attached to `F` is consistent exactly when the
zero perturbation belongs to the source-facing bifunction domain. -/
@[simp] theorem isConsistent_iff_zero_mem_dom (F : U → X → β) :
    IsConsistent F ↔ (0 : U) ∈ dom F := by
  rw [isConsistent_iff_exists_lt_top, mem_dom_iff_exists]

end

end

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β]

/-- A parameter lies in the effective domain of the perturbation function exactly when some slice
value of the bifunction is strictly below `⊤`. -/
@[simp] theorem mem_dom_perturbationFunction_iff_exists {F : U → X → β} {u : U} :
    u ∈ dom(perturbationFunction F) ↔ ∃ x : X, F u x < ⊤ := by
  rw [_root_.mem_effectiveDomain, perturbationFunction_apply]
  exact (iInf_lt_top : (⨅ x : X, F u x) < ⊤ ↔ ∃ x : X, F u x < ⊤)

/-- Membership in the effective domain of the perturbation function is exactly membership in the
source-facing bifunction domain. -/
@[simp] theorem mem_dom_perturbationFunction_iff_mem_dom
    {F : U → X → β} {u : U} :
    u ∈ dom(perturbationFunction F) ↔ u ∈ dom F := by
  rw [mem_dom_perturbationFunction_iff_exists, mem_dom_iff_exists]

/-- The generalized-program domain `dom(perturbationFunction F)` is exactly the source-facing
bifunction domain. -/
@[simp] theorem dom_perturbationFunction_eq_dom (F : U → X → β) :
    dom(perturbationFunction F) = dom F := by
  ext u
  simpa using mem_dom_perturbationFunction_iff_mem_dom

section

variable {𝕜 : Type z} {V : Type*} [Ring 𝕜]
variable [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace U] [AddTorsor V U]

/-- Transporting the source-facing bifunction domain to the chapter's canonical
generalized-program owner commutes with relative interior, on the theorem surface
`ri[𝕜](dom F)`. -/
theorem ri_dom_eq_riDom_perturbationFunction
    (F : U → X → β) :
    ri[𝕜](dom F) = riDom[𝕜](perturbationFunction F) := by
  rw [riDom_eq_intrinsicInterior_dom, dom_perturbationFunction_eq_dom]

/-- Relative-interior membership in the source-facing bifunction domain is exactly
relative-interior membership in the canonical generalized-program domain. -/
theorem mem_ri_dom_iff_mem_riDom_perturbationFunction
    {F : U → X → β} {u : U} :
    u ∈ ri[𝕜](dom F) ↔
      u ∈ riDom[𝕜](perturbationFunction F) := by
  rw [ri_dom_eq_riDom_perturbationFunction]

/-- Canonicalization bridge: relative interior of `dom(perturbationFunction F)` is rewritten to
the source-facing owner `ri[𝕜](dom F)`. -/
@[simp] theorem riDom_perturbationFunction_eq_ri_dom
    (F : U → X → β) :
    riDom[𝕜](perturbationFunction F) = ri[𝕜](dom F) := by
  exact (ri_dom_eq_riDom_perturbationFunction (𝕜 := 𝕜) (F := F)).symm

/-- Canonicalization bridge: relative-interior membership in
`dom(perturbationFunction F)` rewrites to membership in `ri[𝕜](dom F)`. -/
@[simp] theorem mem_riDom_perturbationFunction_iff_mem_ri_dom
    {F : U → X → β} {u : U} :
    u ∈ riDom[𝕜](perturbationFunction F) ↔ u ∈ ri[𝕜](dom F) := by
  rw [riDom_perturbationFunction_eq_ri_dom]

end

section

variable [TopologicalSpace U]

/-- Transporting the source-facing bifunction domain to the chapter's canonical
generalized-program owner commutes with ordinary interior. -/
theorem interior_dom_eq_interior_dom_perturbationFunction
    (F : U → X → β) :
    interior (dom F) = interior (dom(perturbationFunction F)) := by
  rw [dom_perturbationFunction_eq_dom]

/-- Interior membership in the source-facing bifunction domain is exactly interior
membership in the canonical generalized-program domain. -/
theorem mem_interior_dom_iff_mem_interior_dom_perturbationFunction
    {F : U → X → β} {u : U} :
    u ∈ interior (dom F) ↔
      u ∈ interior (dom(perturbationFunction F)) := by
  rw [interior_dom_eq_interior_dom_perturbationFunction]

/-- Canonicalization bridge: interior of `dom(perturbationFunction F)` is rewritten to the
source-facing owner `interior (dom F)`. -/
@[simp] theorem interior_dom_perturbationFunction_eq_interior_dom
    (F : U → X → β) :
    interior (dom(perturbationFunction F)) = interior (dom F) := by
  exact (interior_dom_eq_interior_dom_perturbationFunction (F := F)).symm

/-- Canonicalization bridge: interior membership in `dom(perturbationFunction F)` rewrites to
interior membership in `dom F`. -/
@[simp] theorem mem_interior_dom_perturbationFunction_iff_mem_interior_dom
    {F : U → X → β} {u : U} :
    u ∈ interior (dom(perturbationFunction F)) ↔ u ∈ interior (dom F) := by
  rw [interior_dom_perturbationFunction_eq_interior_dom]

end

end

end Bifunction
