import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_24
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_29_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar
open Function

universe u v

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 (U × X)]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.29.4 compares the closure of a convex bifunction with the closures of
  its slices on `ri[𝕜](dom F)`, and compares the parameter domains of `F` and `cl F`.
- `core/canonical`: the Chapter 6 owners already present are `Bifunction.closure`,
  `Bifunction.perturbationFunction`, and `Bifunction.dom`; for the domain clauses, the raw owner
  abstraction is the graph function `uncurry F`, together with the Chapter 2 closure-domain owner
  theorems for `cl(uncurry F)` and the Chapter 6 projection bridge
  `dom_eq_image_fst_dom_uncurry`.
- `bridge/view`: the slice infimum identity is expressed on the canonical row-infimum owner
  `perturbationFunction`, while the slice-closure identity keeps the source-facing equality
  `cl F u = cl(F u)` and the domain clauses project graph-domain statements
  back to parameter
  domains.

Primary mathematical domain:
- convex extended-scalar-valued bifunctions, with finite-dimensionality imposed at the graph-owner
  layer `U × X`.

Domain-style sampling used here:
- `Bifunction.closure` and `Bifunction.closure_apply` from `Definition_6_29_24`;
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.dom` and `Bifunction.dom_eq_image_fst_dom_uncurry` from
  `Definition_6_29_8`/`Proposition_6_29_2`;
- `(uncurry F).IsConvex 𝕜` from `Definition_6_29_4`;
- `(uncurry F).IsProper` from `Definition_6_29_6`;
- `Function.subset_dom_lowerSemicontinuousHull` and
  `Function.IsConvex.closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper` from
  `Chap02.Corollary_7_4_1`;
- `image_closure_subset_closure_image` for projecting graph-domain closure to parameter-domain
  closure;
- the Chapter 2 owners `cl(·)` and `ri[𝕜](·)`.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner hypotheses: convexity of the graph function, and for the domain-closure clause
  properness of the graph function;
- derived API: slice-wise closure equality, slice-infimum equality, and the two parameter-domain
  inclusions.

Layer target: `source-facing`, split into atomic owner-level clauses rather than a conjunction.
-/

-- Proof sketch: pass from the convex graph function `uncurry F` on `U × X` to its
-- closure on the product, then specialize the Chapter 2 segment-limit/relative-interior closure
-- theorem to the vertical slice over `u ∈ ri[𝕜](dom F)`.
/-- Theorem 6.29.4 (1): for a convex bifunction `F`, the `u`-slice of the bifunction closure
`cl F` agrees with the Chapter 2 closure `cl(F u)` of the slice whenever
`u ∈ ri[𝕜](dom F)`. -/
theorem closure_slice_eq_lowerSemicontinuousHull_of_mem_ri_dom
    {F : U → X → WithBotTop 𝕜} (hF : convᵇ[𝕜](F))
    {u : U} (hu : u ∈ ri[𝕜](dom F)) :
    cl F u = cl(F u) := sorry

-- Proof sketch: apply clause `(1)` to identify the slice `(cl F) u` with
-- `cl(F u)`, then use the one-variable fact that taking the Chapter 2
-- closure does not change the infimum of a convex slice on the relative interior of its effective
-- domain.
/-- Theorem 6.29.4 (2): for a convex bifunction `F`, the infimum of the slice of `cl F` at `u`
equals the infimum of the original slice at every `u ∈ ri[𝕜](dom F)`, written on the canonical
row-infimum owner as `perturbationFunction (cl F) u = perturbationFunction F u`. -/
theorem perturbationFunction_closure_eq_perturbationFunction_of_mem_ri_dom
    {F : U → X → WithBotTop 𝕜} (hF : convᵇ[𝕜](F))
    {u : U} (hu : u ∈ ri[𝕜](dom F)) :
    perturbationFunction (cl F) u = perturbationFunction F u := sorry

end

section

variable {U : Type u} {X : Type v}
variable {α : Type*}
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [Nonempty α]
variable [TopologicalSpace (U × X)]

-- Proof sketch: the graph-function closure `cl(uncurry F)` can only enlarge the
-- effective domain of the graph function. Projecting that inclusion onto the parameter space gives
-- `dom F ⊆ dom(cl F)`. The textbook's extra properness hypothesis is redundant here.
/-- Theorem 6.29.4 (3): passing from a bifunction to its closure can only enlarge the parameter
domain. This is the source inclusion `dom F ⊆ dom(cl F)`. -/
theorem subset_dom_closure (F : U → X → WithBotTop α) :
    dom F ⊆ dom (cl F) := by
  intro u hu
  rw [mem_dom_iff_exists_mem_dom_uncurry] at hu ⊢
  rcases hu with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simpa [uncurry_closure] using
    (Function.subset_dom_lowerSemicontinuousHull (uncurry F) hx)

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 (U × X)]

-- Proof sketch: apply the Chapter 2 domain-closure theorem to the convex proper graph function
-- `uncurry F`, obtaining `dom(cl(uncurry F)) ⊆ closure(dom(uncurry F))`, and then
-- project this inclusion onto the parameter factor to identify the source parameter domains.
/-- Theorem 6.29.4 (4): if the graph function of a convex bifunction `F` is proper, then the
parameter domain of `cl F` is contained in the closure of the parameter domain of `F`. -/
theorem dom_closure_subset_closure_dom_of_isProper
    {F : U → X → WithBotTop 𝕜} (hF_convex : convᵇ[𝕜](F))
    (hF_proper : properᵇ(F)) :
    dom (cl F) ⊆ _root_.closure (dom F) := by
  intro u hu
  rw [dom_eq_image_fst_dom_uncurry] at hu
  rcases hu with ⟨⟨u, x⟩, hx, rfl⟩
  have hx' : (u, x) ∈ _root_.effectiveDomain (cl(uncurry F)) := by
    simpa [uncurry_closure] using hx
  have hgraph :
      _root_.closure (_root_.effectiveDomain (cl(uncurry F))) =
        _root_.closure (_root_.effectiveDomain (uncurry F)) :=
    hF_convex.closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper hF_proper
  have hx_closure : (u, x) ∈ _root_.closure (_root_.effectiveDomain (uncurry F)) := by
    rw [← hgraph]
    exact subset_closure hx'
  have hu_closure :
      u ∈ _root_.closure (Prod.fst '' _root_.effectiveDomain (uncurry F)) :=
    image_closure_subset_closure_image continuous_fst ⟨(u, x), hx_closure, rfl⟩
  simpa [dom_eq_image_fst_dom_uncurry] using hu_closure

end

end Bifunction
