import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Example_23_4_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Remark_5_24_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_2_1

noncomputable section

open scoped Rockafellar

universe u

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.2.1 draws two consequences from the definition of essential strict
  convexity and the Chapter 23 subdifferential-domain sandwich: strict convexity on `ri(dom f)`,
  and the caution that `dom ∂f` need not be convex.
- `core/canonical`: the owner abstractions are `Function.IsEssentiallyStrictlyConvex`,
  `StrictConvexOn 𝕜 C f`, `riDom[𝕜](f)`, and the canonical subdifferential-domain owner
  `dom∂[Y](f)`.
- `bridge/view`: the text's `dom ∂f` is expressed directly by the established notation
  `dom∂[Y](f)`;
  no parallel wrapper for the subdifferential domain is introduced.

Domain-style sampling used here:
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `StrictConvexOn` from mathlib's convex-function owner layer;
- `Function.realBranch` from `Chap02.Theorem_10_4`;
- `riDom(·)` from `Chap01.Definition_4_4`;
- `dom∂[·](·)` and `mem_subdifferentialGraph_dom` from `Chap05.Definition_5_24_1`.

Primitive data vs derived API:
- primitive owner data: an essentially strictly convex function `f`;
- derived API: strict convexity of the real branch on `riDom(f)`, and the existential caution that
  `dom∂[Y](f)` need not itself be convex even inside the closed/proper/convex owner layer.

Layer target:
- `Function.IsEssentiallyStrictlyConvex.strictConvexOn_riDom`: `bridge/view`, derived from the
  owner field over the Chapter 23 inclusion `riDom[𝕜](f) ⊆ dom∂[Y](f)`;
- `Function.IsEssentiallyStrictlyConvex.strictConvexOn_realBranch_riDom`: `bridge/view`,
  expressing the finite real branch as a companion view;
- `subdifferentiabilityCounterexample_not_convex_domSubdifferential`: `bridge/view`, translating
  Example 23.4.2 from the graph-domain owner to `dom∂(·)`;
- `exists_nonconvex_domSubdifferential`: a companion existence statement inside
  `Function.IsClosedProperConvex`, not a second owner.
-/

namespace Function

section

variable {𝕜 : Type _}
variable [Field 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜] [DecidableLT 𝕜]
variable {E : Type u}
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousConstSMul 𝕜 E]

namespace IsEssentiallyStrictlyConvex

-- Proof sketch: `riDom(f)` is convex by Theorem 6.2. Apply the defining strict-convexity field
-- of `hf` to the convex set `riDom[𝕜](f)` once the owner-level bridge
-- `riDom[𝕜](f) ⊆ dom∂[Y](f)` is
-- provided.
/-- Primitive owner-level bridge for Text 26.2.1: an essentially strictly convex function is
strictly convex on `ri(dom f)` as soon as `riDom[𝕜](f) ⊆ dom∂[Y](f)` is available. -/
theorem strictConvexOn_riDom_of_subset
    {f : E → WithBotTop 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f)
    (hri : riDom[𝕜](f) ⊆ dom∂[Y](f)) :
    StrictConvexOn 𝕜 riDom[𝕜](f) f := by
  rcases hf with ⟨hconvex, _hproper, hstrictOn⟩
  exact hstrictOn (Convex.intrinsicInterior hconvex.convex_dom) hri

end IsEssentiallyStrictlyConvex

end

section

variable {𝕜 : Type _}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace IsEssentiallyStrictlyConvex

-- Proof sketch: apply the primitive owner-level bridge above with the canonical inclusion
-- `riDom[𝕜](f) ⊆ dom∂[Y](f)` from Remark 5.24.1 for proper convex functions.
/-- Text 26.2.1: whenever the Chapter 23/Remark 5.24.1 inclusion
`riDom[𝕜](f) ⊆ dom∂[Y](f)` is available for proper convex functions, an essentially strictly convex
function is strictly convex on `ri(dom f)`. -/
theorem strictConvexOn_riDom
    {f : E → WithBotTop 𝕜} {Y : Type _} [HasPairing E Y 𝕜]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f) :
    StrictConvexOn 𝕜 riDom[𝕜](f) f := by
  rcases hf with ⟨hconvex, hproper, hstrictOn⟩
  exact strictConvexOn_riDom_of_subset (hf := ⟨hconvex, hproper, hstrictOn⟩)
    (_root_.riDom_subset_domSubdifferential_of_convex_proper
      (Y := Y) hconvex hproper)

end IsEssentiallyStrictlyConvex

end

section

variable {E : Type u}
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousConstSMul ℝ E]

namespace IsEssentiallyStrictlyConvex

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in
private theorem strictConvexOn_real_of_coe
    {C : Set E} {g : E → ℝ}
    (h : StrictConvexOn ℝ C (fun x ↦ ((g x : ℝ) : WithBotTop ℝ))) :
    StrictConvexOn ℝ C g := by
  rcases h with ⟨hC_convex, hineq⟩
  refine ⟨hC_convex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hltE :
      (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
        a • (((g x : ℝ) : WithBotTop ℝ)) + b • (((g y : ℝ) : WithBotTop ℝ)) :=
    hineq hx hy hxy ha hb hab
  have hltCoe :
      (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
        (((a * g x + b * g y : ℝ) : WithBotTop ℝ)) := by
    change (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
      (((a : ℝ) : WithBotTop ℝ) * (((g x : ℝ) : WithBotTop ℝ)) +
        ((b : ℝ) : WithBotTop ℝ) * (((g y : ℝ) : WithBotTop ℝ)))
    simpa [smul_eq_mul] using hltE
  exact (WithBotTop.coe_lt_coe).1 hltCoe

-- Proof sketch: first use the canonical owner-level theorem
-- `strictConvexOn_riDom_of_subset` on `f : E → WithBotTop ℝ`; then identify `f` with its finite
-- real branch on `riDom(f)` using `dom∂[Y](f) ⊆ dom(f)`.
/-- Real-branch bridge for Text 26.2.1: once `riDom(f) ⊆ dom∂[Y](f)` is known, strict convexity
of the extended-value owner `f` on `riDom(f)` transfers to strict convexity of `f.realBranch`. -/
theorem strictConvexOn_realBranch_riDom_of_subset
    {f : E → WithBotTop ℝ} {Y : Type _} [HasPairing E Y ℝ]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f)
    (hri : riDom(f) ⊆ dom∂[Y](f)) :
    StrictConvexOn ℝ riDom(f) f.realBranch := by
  rcases hf with ⟨hconvex, hproper, hstrictOn⟩
  have hf' : Function.IsEssentiallyStrictlyConvex (Y := Y) f := ⟨hconvex, hproper, hstrictOn⟩
  have hstrict : StrictConvexOn ℝ riDom(f) f := by
    simpa using
      (strictConvexOn_riDom_of_subset (𝕜 := ℝ) (Y := Y) (f := f) hf' hri)
  have hdomSub : dom∂[Y](f) ⊆ dom(f) :=
    _root_.domSubdifferential_subset_dom (Y := Y) hproper.nonempty_dom
  have hEq : Set.EqOn f (fun x ↦ ((f.realBranch x : ℝ) : WithBotTop ℝ)) riDom(f) := by
    intro x hx
    have hxdomSub : x ∈ dom∂[Y](f) := hri hx
    have hxdom : x ∈ dom(f) := hdomSub hxdomSub
    have hneTop : f x ≠ ⊤ := ne_of_lt (mem_effectiveDomain.mp hxdom)
    have hneBot : f x ≠ ⊥ := hproper.ne_bot x
    simpa [Function.realBranch] using (EReal.coe_toReal hneTop hneBot).symm
  exact strictConvexOn_real_of_coe (hstrict.congr hEq)

end IsEssentiallyStrictlyConvex

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsEssentiallyStrictlyConvex

-- Proof sketch: combine `strictConvexOn_realBranch_riDom_of_subset` with the canonical Chapter 23
-- inclusion from Remark 5.24.1.
/-- Text 26.2.1 (real-branch view): an essentially strictly convex function is strictly convex on
`ri(dom f)` after passing to the finite branch `f.realBranch`. -/
theorem strictConvexOn_realBranch_riDom
    {f : E → WithBotTop ℝ} {Y : Type _} [HasPairing E Y ℝ]
    (hf : Function.IsEssentiallyStrictlyConvex (Y := Y) f) :
    StrictConvexOn ℝ riDom(f) f.realBranch := by
  rcases hf with ⟨hconvex, hproper, hstrictOn⟩
  have hf' : Function.IsEssentiallyStrictlyConvex (Y := Y) f := ⟨hconvex, hproper, hstrictOn⟩
  refine strictConvexOn_realBranch_riDom_of_subset (Y := Y) hf' ?_
  simpa using _root_.riDom_subset_domSubdifferential_of_convex_proper
    (Y := Y) hconvex hproper

end IsEssentiallyStrictlyConvex

end

end Function

-- Proof sketch: Example 23.4.2 gives an explicit function on `R²` whose subdifferentiability
-- locus is not convex. Via Definition 5.24.1, that locus is exactly the canonical owner
-- `dom∂(f)`.
/-- Example 23.4.2: the canonical subdifferential-domain owner `dom∂(f)` is not convex for the
closed proper convex counterexample function. -/
theorem subdifferentiabilityCounterexample_not_convex_domSubdifferential :
    ¬ Convex ℝ dom∂(subdifferentiabilityCounterexample) := by
  intro hconv
  have hconv' :
      Convex ℝ (_root_.subdifferentialGraph subdifferentiabilityCounterexample).dom := hconv
  rw [← Function.subdifferentialGraph_dom_eq_intrinsic (f := subdifferentiabilityCounterexample)]
    at hconv'
  exact not_convex_subdifferentialGraph_dom hconv'

/-- The subdifferential domain `dom∂(f)` need not be convex even for a closed proper convex
function. -/
theorem exists_nonconvex_domSubdifferential :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
      (f : E → WithBotTop ℝ),
      Function.IsClosedProperConvex (𝕜 := ℝ) f ∧ ¬ Convex ℝ dom∂(f) := by
  refine ⟨EuclideanSpace ℝ (Fin 2), inferInstance, inferInstance,
    subdifferentiabilityCounterexample, ?_⟩
  constructor
  · simpa using subdifferentiabilityCounterexample_isClosedProperConvex
  · exact subdifferentiabilityCounterexample_not_convex_domSubdifferential
