import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {𝕜 : Type v} [Preorder 𝕜]
variable {E : Type u}

namespace Function

/-- Finite-valuedness on a set at the chapter codomain layer. This keeps the source-facing
finiteness data (`x ∈ dom(f)` and `f x ≠ ⊥`) as one reusable owner. -/
abbrev IsFiniteOn (f : E → WithTopBot 𝕜) (C : Set E) : Prop :=
  ∀ x, x ∈ C → x ∈ dom(f) ∧ f x ≠ ⊥

end Function

end

section

open Filter
open scoped Pointwise Rockafellar Topology

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.8 is a continuity theorem for directional derivatives and
  subdifferentials under pointwise convergence of convex functions on a convex set with intrinsic
  relative-openness owner `IsRelativelyOpen 𝕜 C`, where all functions are finite.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.directionalDerivativeAt`, `_root_.subdifferentialAt`,
  `convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit` / its one-sided uniform consequence
  from Chapter 10, and the support-function containment criterion
  `closure_subset_closure_iff_supportFunction_le` from Chapter 13.
- `bridge/view`: the public theorem keeps Rockafellar's pointwise-convergence hypotheses, but its
  conclusions are written directly in the existing Chapter 23 owners rather than through a local
  duplicate directional-derivative or subgradient package.

Domain-style sampling used here:
- `convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit` from
  `Items/Chap02/Theorem_10_8`;
- `eventually_le_add_of_limsup_le_of_convexOn_on_closed_bounded` from
  `Items/Chap02/Corollary_10_8_1`;
- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from
  `Items/Chap05/Lemma_23_0_1`;
- `closure_subset_closure_iff_supportFunction_le` from
  `Items/Chap03/Corollary_13_1_1`.

Primitive data vs derived API:
- primitive source data: the convex functions `fSeq i` and `f`, the convex region `C` with
  intrinsic relative-openness owner `IsRelativelyOpen 𝕜 C` on which they are finite, encoded
  canonically by `x ∈ dom(f)` / `x ∈ dom(fSeq i)` together with exclusion of the value `⊥`, the
  pointwise convergence on `C`, and convergent sequences `xSeq → x` inside `C` and `ySeq → y`;
- derived API: the upper-semicontinuity inequality for `directionalDerivativeAt`; the companion
  closed-ball containment theorem below is pairing-parametric on a normed dual-side codomain.

Layer target: `source-facing`. The theorem is not collapsed to a pure
`TendstoLocallyUniformlyOn` owner statement, because the source item itself is explicitly about
 directional derivatives and subdifferentials under pointwise convergence.

Ambient-assumption minimization:
- Chapter 23's directional-derivative and dual-subdifferential owners already live on
  `WithTopBot 𝕜` over a scalar-generic normed-space layer, so the theorem surface follows that
  owner level directly;
- no inner-product identification is part of the primary statement layer; the companion
  closed-ball clause below stays at the same scalar layer and is pairing-parametric in a normed
  dual-side codomain `Y`.
-/

namespace Function

variable {C : Set E}
variable (fSeq : ℕ → E → WithTopBot 𝕜) (f : E → WithTopBot 𝕜)

/- Local bridge so theorem surfaces stay on `WithTopBot` while reusing chapter scalar action. -/
local instance instSMulWithTopBot_theorem5248 : SMul 𝕜 (WithTopBot 𝕜) :=
  (show SMul 𝕜 (WithBotTop 𝕜) from inferInstance)

-- Proof sketch: restrict the convex functions to the convex region `C` with intrinsic
-- relative-openness owner `IsRelativelyOpen 𝕜 C`, pass to the Chapter 10
-- pointwise-convergence owner on finite scalar-valued convex functions, and then compare the
-- resulting directional-difference quotients along the affine lines
-- `xSeq i + t • ySeq i`.
/-- Theorem 5.24.8, directional-derivative form: if convex extended-real-valued functions
`fSeq i` converge pointwise on a convex set `C` with intrinsic relative-openness owner
`IsRelativelyOpen 𝕜 C` to a limit `f` with `ConvexOn 𝕜 C f`, and all of these functions are
finite on `C`, then
directional derivatives are upper semicontinuous along convergent base-point and direction
sequences inside `C`. -/
theorem limsup_directionalDerivativeAt_le_of_tendsto_on_relativelyOpen_convex
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hf_convexOn : ConvexOn 𝕜 C f) (hfSeq_convexOn : ∀ i, ConvexOn 𝕜 C (fSeq i))
    (hf_finite : f.IsFiniteOn C)
    (hfSeq_finite : ∀ i, (fSeq i).IsFiniteOn C)
    (hlimit : ∀ x, x ∈ C → Tendsto (fun i ↦ fSeq i x) atTop (𝓝 (f x)))
    {x : E} (hx : x ∈ C) {xSeq : ℕ → E} (hxSeq_mem : ∀ i, xSeq i ∈ C)
    (hxSeq : Tendsto xSeq atTop (𝓝 x))
    {y : E} {ySeq : ℕ → E} (hySeq : Tendsto ySeq atTop (𝓝 y)) :
    limsup (fun i ↦ directionalDerivativeAt (fSeq i) (xSeq i) (ySeq i)) atTop ≤
      directionalDerivativeAt f x y := by
  sorry


variable {C : Set E}
variable (fSeq : ℕ → E → WithTopBot 𝕜) (f : E → WithTopBot 𝕜)
variable {Y : Type (max u v)} [NormedAddCommGroup Y] [HasPairing E Y 𝕜]

-- Proof sketch: use the directional theorem with a constant direction to obtain eventual support-
-- function domination on the unit closed ball, then rewrite the support term for the ball and
-- invoke the Chapter 13 support-function containment criterion.
/-- Theorem 5.24.8, subdifferential form: under the same hypotheses (with intrinsic
relative-openness owner `IsRelativelyOpen 𝕜 C`), every `ε > 0` eventually forces the
pairing-level subdifferential `∂[Y]fSeq i(xSeq i)` to lie in the
Minkowski sum of `∂[Y]f(x)` with the closed `Y`-ball of radius `ε`. -/
theorem eventually_subdifferentialAt_subset_add_closedBall_of_tendsto_on_relativelyOpen_convex
    (hC_open : IsRelativelyOpen 𝕜 C)
    (hf_convexOn : ConvexOn 𝕜 C f) (hfSeq_convexOn : ∀ i, ConvexOn 𝕜 C (fSeq i))
    (hf_finite : f.IsFiniteOn C)
    (hfSeq_finite : ∀ i, (fSeq i).IsFiniteOn C)
    (hlimit : ∀ x, x ∈ C → Tendsto (fun i ↦ fSeq i x) atTop (𝓝 (f x)))
    {x : E} (hx : x ∈ C) {xSeq : ℕ → E} (hxSeq_mem : ∀ i, xSeq i ∈ C)
    (hxSeq : Tendsto xSeq atTop (𝓝 x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀,
      (∂[Y]fSeq i(xSeq i)) ⊆
        (∂[Y]f(x)) + Metric.closedBall (0 : Y) ε := by
  sorry

end Function

end
