import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_4

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [Preorder 𝕜]
variable {E : Type u} [Sub E]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.1 compares the effective domain of the subdifferential with the
  effective domain and relative interior of the original function.
- `core/canonical`: the owner abstractions are `dom∂[Y](f)`, `dom(f)`, `riDom[𝕜](f)`, and
  intrinsic nonemptiness of `_root_.subdifferentialAt` at pairing level `Y`.
- `bridge/view`: the source set `{x | ∂f(x) ≠ ∅}` is already the canonical graph-domain owner
  `dom∂[Y](f)` from Definition 5.24.1, so this item compares existing owners
  rather than introducing a new wrapper.

Domain-style sampling used here:
- `dom∂[·](·)` and `mem_domSubdifferential_iff_nonempty` from
  `Items/Chap05/Definition_5_24_1.lean`;
- `dom(·)` and `riDom[𝕜](·)` from `Items/Chap01/Definition_4_4.lean`.

Primitive data vs derived API:
- primitive inputs: `dom(f).Nonempty` for the right inclusion and owner-level nonemptiness of
  `(∂[Y]f(x)).Nonempty` on `riDom[𝕜](f)` for the left inclusion;
- derived outputs: the left inclusion `riDom[𝕜](f) ⊆ dom∂[Y](f)`, the right
  inclusion `dom∂[Y](f) ⊆ dom(f)`, and the summarized sandwich statement.

Layer target: `bridge/view`.

Semantic-fidelity audit:
- the core owner-level statements are reduced to exact inclusion hypotheses:
  `dom(f).Nonempty` and intrinsic nonemptiness of `(∂[Y]f(x)).Nonempty` on
  `riDom[𝕜](f)`;
- the source-facing convex/proper specialization is provided separately via Theorem 23.4 in the
  pairing-level bridge section below;
- the source notation `dom ∂f` is exposed through the parser-stable surface `dom∂[Y](f)` on
  the canonical owner `(subdifferentialGraph (Y := Y) f).dom`, rather than through a new wrapper
  definition.
-/

-- Proof sketch: choose `y ∈ dom(f)` from the nonemptiness hypothesis. If `x ∈ dom∂[Y](f)`,
-- then some `xStar ∈ subdifferentialAt f x Y` satisfies the global subgradient inequality.
-- Evaluate that inequality at `y` to force `f x < ⊤`, hence `x ∈ dom(f)`.
/-- Any point where the subdifferential is nonempty belongs to the effective domain of the
function. -/
theorem domSubdifferential_subset_dom
    {f : E → WithTopBot 𝕜} (hdom : dom(f).Nonempty) :
    dom∂[Y](f) ⊆ dom(f) := by
  intro x hx
  rw [mem_domSubdifferential_iff_nonempty (Y := Y)] at hx
  rcases hx with ⟨xStar, hxStar⟩
  rcases hdom with ⟨y, hy⟩
  by_contra hx_dom
  have hfx_top : f x = ⊤ := by
    have : ¬ f x < ⊤ := by
      simpa [mem_effectiveDomain] using hx_dom
    simpa [lt_top_iff_ne_top] using this
  have hy_top : f y = ⊤ := by
    have : (⊤ : WithTopBot 𝕜) ≤ f y := by
      simpa [hfx_top] using (mem_subdifferentialAt_pairing.mp hxStar) y
    simpa using this
  exact (mem_effectiveDomain.mp hy).ne hy_top

end

section

variable {𝕜 : Type v} [Ring 𝕜] [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

-- Proof sketch: this is exactly the canonical domain-membership characterization
-- `x ∈ dom∂[Y](f) ↔ (∂[Y]f(x)).Nonempty`, specialized to points in
-- `riDom[𝕜](f)`.
/-- Any owner-side proof that `(∂[Y]f(x)).Nonempty` on `riDom[𝕜](f)` yields
the inclusion `riDom[𝕜](f) ⊆ dom∂[Y](f)`. -/
theorem riDom_subset_domSubdifferential
    {f : E → WithTopBot 𝕜}
    (hsub_riDom : ∀ ⦃x : E⦄, x ∈ riDom[𝕜](f) → (∂[Y]f(x)).Nonempty) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) := by
  intro x hx
  exact (mem_domSubdifferential_iff_nonempty (Y := Y)).2 (hsub_riDom hx)

-- Proof sketch: combine the two previous inclusion theorems.
/-- The canonical domain owner `dom∂[Y](f)` lies between `riDom[𝕜](f)` and `dom(f)` whenever
subdifferentials are nonempty on `riDom[𝕜](f)` and `dom(f)` is nonempty. -/
theorem domSubdifferential_between_riDom_and_dom
    {f : E → WithTopBot 𝕜}
    (hsub_riDom : ∀ ⦃x : E⦄, x ∈ riDom[𝕜](f) → (∂[Y]f(x)).Nonempty)
    (hdom : dom(f).Nonempty) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) ∧ dom∂[Y](f) ⊆ dom(f) :=
  ⟨riDom_subset_domSubdifferential hsub_riDom,
    domSubdifferential_subset_dom hdom⟩

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

-- Proof sketch: Theorem 23.4 gives intrinsic nonemptiness of `∂[Y]f(x)` on
-- `riDom[𝕜](f)`. Feed that owner-level input directly to the primitive inclusion theorem.
/-- Every point of the relative interior of the effective domain lies in the effective domain of
the subdifferential graph for a proper convex function. -/
theorem riDom_subset_domSubdifferential_of_convex_proper
    {f : E → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) := by
  apply _root_.riDom_subset_domSubdifferential (f := f)
  intro x hx
  simpa using (_root_.subdifferentialAt_nonempty_of_mem_riDom
    (Y := Y) hf_convex hf_proper hx)

-- Proof sketch: combine the convex/proper left inclusion with the owner-side right inclusion.
/-- Remark 5.24.1: although the effective domain of the subdifferential need not be convex, its
canonical domain owner `dom∂[Y](f)` lies between `ri[𝕜](dom f)` and `dom(f)`. -/
theorem domSubdifferential_between_riDom_and_dom_of_convex_proper
    {f : E → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    riDom[𝕜](f) ⊆ dom∂[Y](f) ∧ dom∂[Y](f) ⊆ dom(f) :=
  ⟨riDom_subset_domSubdifferential_of_convex_proper hf_convex hf_proper,
    domSubdifferential_subset_dom hf_proper.nonempty_dom⟩

end
