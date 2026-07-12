import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_8

noncomputable section

open scoped Pointwise Rockafellar Topology

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core triage for this item.

- `source-facing`: Corollary 5.24.2 asserts upper semicontinuity of the directional derivative on
  `interior (dom(f)) × E` and the local upper-semicontinuity of the subdifferential map near an
  interior point of `dom(f)`.
- `core/canonical`: the owner declarations already present upstream are
  `Function.directionalDerivativeAt`, `_root_.subdifferentialAt`, the chapter effective-domain
  owner `dom(·)`, and the convergence theorem
  `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex` together with
  `Function.eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex`
  from Theorem 5.24.8; for this item's primary theorem surfaces, the intrinsic-domain owner is
  `riDom[𝕜](f)`.
- `bridge/view`: the ambient `interior (dom(f))` forms are retained only as thin wrappers from the
  intrinsic owner layer via `interior_subset_intrinsicInterior`.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- `Function.limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex` from
  `Chap05/Theorem_5_24_8`;
- `_root_.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `UpperSemicontinuousOn` from mathlib's semicontinuity API.

Primitive data vs derived API:
- primitive source data: a convex function `f` finite on the intrinsic domain owner
  `riDom[𝕜](f)` (owner `f.IsFiniteOn (riDom[𝕜](f))`) and a point in `riDom[𝕜](f)`;
- derived API: upper semicontinuity of `(x, y) ↦ directionalDerivativeAt f x y` on
  `riDom[𝕜](f) × E`, and the local closed-ball inclusion for the canonical dual
  subdifferential.

Layer target:
- clause `(1)`: `core/canonical`, with an ambient-interior bridge;
- clause `(2)`: `core/canonical`, with an ambient-interior bridge.

Ambient-assumption minimization:
- the directional-derivative clause uses only the finite-dimensional normed-space layer
  already required by Theorem 5.24.8, exposed at the scalar-generic layer `𝕜`;
- the canonical subdifferential inclusion stays at the dual owner
  `_root_.subdifferentialAt`, with explicit pairing codomain parameter `Y`.
-/

namespace Function

variable {f : E → WithTopBot 𝕜}

-- Proof sketch: apply Theorem 5.24.8 to the constant sequence `fSeq i = f` on the open convex set
-- `riDom[𝕜](f)`, then pass from the resulting limsup inequality along convergent sequences
-- in `riDom[𝕜](f) × E` to the canonical product-space predicate `UpperSemicontinuousOn`.
/-- Corollary 5.24.2 (1), intrinsic-domain primitive owner form: if `f` is convex and finite on
`riDom[𝕜](f)`, then `(x, y) ↦ directionalDerivativeAt f x y` is upper semicontinuous on
`riDom[𝕜](f) ×ˢ Set.univ`. -/
theorem upperSemicontinuousOn_directionalDerivativeAt_on_riDom_of_isFiniteOn
    (hf_convex : f.IsConvex 𝕜) (hf_finite_riDom : f.IsFiniteOn (riDom[𝕜](f))) :
    UpperSemicontinuousOn
      (Function.uncurry (directionalDerivativeAt f))
      (riDom[𝕜](f) ×ˢ Set.univ) := sorry

/-- Corollary 5.24.2 (1), intrinsic-domain source-facing form specialized to proper convex
functions. -/
theorem upperSemicontinuousOn_directionalDerivativeAt_on_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    UpperSemicontinuousOn
      (Function.uncurry (directionalDerivativeAt f))
      (riDom[𝕜](f) ×ˢ Set.univ) := by
  refine
    upperSemicontinuousOn_directionalDerivativeAt_on_riDom_of_isFiniteOn
      (f := f) hf_convex ?_
  intro x hx
  exact ⟨intrinsicInterior_subset hx, hf_proper.ne_bot x⟩

/-- Corollary 5.24.2 (1), source-facing ambient bridge: the intrinsic-domain theorem yields the
ambient interior-domain form. -/
theorem upperSemicontinuousOn_directionalDerivativeAt_on_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    UpperSemicontinuousOn
      (Function.uncurry (directionalDerivativeAt f))
      (interior (dom(f)) ×ˢ Set.univ) := by
  refine
    (upperSemicontinuousOn_directionalDerivativeAt_on_riDom
      (f := f) hf_convex hf_proper).mono ?_
  intro p hp
  exact ⟨interior_subset_intrinsicInterior (𝕜 := 𝕜) hp.1, hp.2⟩

variable {Y : Type (max u v)} [NormedAddCommGroup Y] [HasPairing E Y 𝕜]

-- Proof sketch: specialize the set-valued upper-semicontinuity theorem of Theorem 5.24.8 to the
-- constant sequence `fSeq i = f` on `riDom[𝕜](f)`.
/-- Corollary 5.24.2 (2), intrinsic-domain primitive owner form: if `f` is convex and finite on
`riDom[𝕜](f)`, then for every `x ∈ riDom[𝕜](f)` and every `ε > 0` there is `δ > 0` such that
every `z ∈ Metric.closedBall x δ` satisfies
`∂[Y]f(z) ⊆ ∂[Y]f(x) + Metric.closedBall (0 : Y) ε`. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom_of_isFiniteOn
    (hf_convex : f.IsConvex 𝕜) (hf_finite_riDom : f.IsFiniteOn (riDom[𝕜](f)))
    {x : E} (hx : x ∈ riDom[𝕜](f)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂[Y]f(z)) ⊆ (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := sorry

/-- Corollary 5.24.2 (2), intrinsic-domain source-facing form specialized to proper convex
functions. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : E} (hx : x ∈ riDom[𝕜](f)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂[Y]f(z)) ⊆ (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := by
  refine
    exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom_of_isFiniteOn
      (f := f) (Y := Y) hf_convex ?_ hx ε hε
  intro u hu
  exact ⟨intrinsicInterior_subset hu, hf_proper.ne_bot u⟩

/-- Corollary 5.24.2 (2), source-facing ambient bridge: the intrinsic-domain theorem yields the
ambient interior-domain form. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_interior_dom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    {x : E} (hx : x ∈ interior (dom(f))) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂[Y]f(z)) ⊆ (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := by
  exact
    exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_riDom
      (f := f) (Y := Y) hf_convex hf_proper
      (x := x) (interior_subset_intrinsicInterior (𝕜 := 𝕜) hx) ε hε

end Function

end
