import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_3_1_9 (from Chap03) -/
/- Lemma 3.1.9 lies in the product-space extended-valued subdifferential domain.

Primary domain:
- convex analysis of `WithTop ℝ`-valued functions on intrinsic `L²` products of real
  inner-product spaces.

Sampled owner-style declarations:
- `subdifferential` in `Definition_3_1_5`, the chapter owner for extended-valued subgradients;
- `partialGradientFst` in `Lemma_3_9`, the source-facing first-slice gradient owner;
- `partialSubdifferentialSnd` in `Lemma_3_9`, the source-facing second-slice subdifferential
  owner;
- `subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds` in
  `Lemma_3_9`, the exact upstream neighborhood-form theorem for this source fact.

Best owner abstraction:
- the exact upstream theorem
  `subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds`
  from `Lemma_3_9`, already stated on the canonical ambient owner `subdifferential`.

Primitive data:
- none in this file; the source-facing slice owners and the theorem already live upstream.

Derived API:
- this recall-only source-facing entry point.

Source/core/bridge triage:
- source-facing: Lemma 3.1.9's product-space subdifferential formula;
- core/canonical: `subdifferential`;
- bridge/view: the neighborhood-form theorem in `Lemma_3_9`.

The previous version introduced a second public theorem shell with a weaker linewise continuity
hypothesis than the canonical owner theorem in `Lemma_3_9`. Since the exact source fact already
lives upstream on the correct owner surface, this file should be recall-only and should reuse that
theorem directly rather than maintain a semantically shifted parallel wrapper.
-/

/- Lemma 3.1.9 is the upstream neighborhood-form theorem
`subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds` from
`Lemma_3_9`. -/

recall subdifferential_eq_image_partialGradientFst_partialSubdifferentialSnd_of_nhds

/-! ### Theorem_3_1_9 (from Chap03) -/
universe u v w

noncomputable section

/- Theorem 3.1.9 lies in the convex-composition domain.

Sampled owner-style declarations in this domain:
- mathlib `ConvexOn`
- mathlib `ConvexOn.comp`
- chapter theorem `ConvexOn.comp_of_monotoneOn`
- mathlib `Monotone.monotoneOn`

Best owner abstraction:
- source-facing layer here: the whole-space specialization
- chapter bridge owner: `ConvexOn.comp_of_monotoneOn`
- core/canonical: mathlib `ConvexOn.comp`

Primitive data:
- a convex set `domψ`
- an inner map `ψ : X → Y`
- an outer map `φ : Y → Z`
- convexity of `ψ` on `domψ`
- convexity of `φ` on all of `Y`
- monotonicity of `φ` on all of `Y`

Derived API:
- convexity of the composition `φ ∘ ψ` on `domψ`

Source/core/bridge triage:
- source-facing: convexity of `φ ∘ ψ` on `domψ` under whole-space assumptions on `φ`
- core/canonical: `ConvexOn.comp`
- bridge/view reused here: `ConvexOn.comp_of_monotoneOn`

Whole-space convexity of `φ` does not by itself restrict to `ConvexOn 𝕜 (ψ '' domψ) φ`, because
that would additionally require convexity of the image set `ψ '' domψ`. The chapter already
packages the correct owner-level bridge for this stronger whole-space hypothesis as
`ConvexOn.comp_of_monotoneOn`, so this file should specialize that chapter theorem rather than
maintain a second parallel proof body.
-/

namespace ConvexOn

section

variable {𝕜 : Type u} [Semiring 𝕜] [PartialOrder 𝕜]
variable {X : Type v} [AddCommMonoid X] [SMul 𝕜 X]
variable {Y : Type w} [AddCommMonoid Y] [PartialOrder Y] [SMul 𝕜 Y]
variable {Z : Type*} [AddCommMonoid Z] [PartialOrder Z] [SMul 𝕜 Z]
variable {domψ : Set X} {ψ : X → Y} {φ : Y → Z}

/-- Theorem 3.1.9: if `ψ` is convex on its domain `domψ ⊆ X`, and `φ : Y → Z` is convex and
nondecreasing on all of `Y`, then the composition `x ↦ φ (ψ x)` is convex on `domψ`. -/
-- Proof sketch: combine the convex upper bound for `ψ` with monotonicity of `φ`, then apply the
-- whole-space convexity inequality for `φ`.
  theorem comp_of_monotone (hφ : ConvexOn 𝕜 Set.univ φ) (hψ : ConvexOn 𝕜 domψ ψ)
    (hφ_mono : Monotone φ) :
    ConvexOn 𝕜 domψ (φ ∘ ψ) := by
  have hψ_maps : Set.MapsTo ψ domψ Set.univ := by
    intro x hx
    simp
  simpa using comp_of_monotoneOn hφ hψ (hφ_mono.monotoneOn Set.univ) hψ_maps

end

end ConvexOn

end

/-! ### Lemma_3_1_10 (from Chap03) -/
/- Lemma 3.1.10 is a recall-only bridge in the chapter's extended-valued convex-analysis /
continuous-subgradient-selection domain.

Primary domain:
- convex analysis of `WithTop ℝ`-valued functions on real inner-product spaces, with a continuous
  local selection of pointwise subgradients.

Relevant sampled declarations in this domain:
- `subdifferential` from `Definition_3_1_5`, the chapter owner for extended-valued subgradients;
- `withTopRealPart` from `Definition_3_3`, the canonical real-valued representative on `dom f`;
- `HasGradientAt`, the canonical gradient owner for differentiability with a specified gradient;
- `hasGradientAt_withTopRealPart_of_continuous_subgradient_selection` from `Lemma_3_10`, the
  exact upstream owner theorem for this source item.

Best owner abstraction:
- the exact upstream owner theorem
  `hasGradientAt_withTopRealPart_of_continuous_subgradient_selection` from `Lemma_3_10`.

Primitive data:
- none in this recall file; the actual source-facing assumptions already live in `Lemma_3_10`.

Derived API recalled here:
- the owner `HasGradientAt` conclusion for the selected subgradient;
- the derived differentiability consequence;
- the derived gradient-identification consequence.

Source/core/bridge triage:
- source-facing: Lemma 3.1.10's differentiability statement from a continuous local subgradient
  selection;
- core/canonical: `subdifferential`, `withTopRealPart`, and `HasGradientAt`;
- bridge/view: the derived `DifferentiableAt` and gradient-equality consequences.

The previous version drifted into the unrelated finite pointwise-supremum / active-set API from
`Lemma_3_1_13`. This file instead reuses the actual `Lemma_3_10` owner family directly and keeps
the later numbered item aligned with its true source mathematics.
-/

recall hasGradientAt_withTopRealPart_of_continuous_subgradient_selection
recall differentiableAt_withTopRealPart_of_continuous_subgradient_selection
recall gradient_eq_of_continuous_subgradient_selection

/-! ### Theorem_3_1_10 (from Chap03) -/
/- Theorem 3.1.10 lies in the chapter's two-function minimax-linearization domain.

Sampled owner-style declarations:
- `constrainedSublevelSet`
- `ClosedConvexOn`
- `IsMinimaxLinearizationParameter`
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets`

Best owner abstraction:
- source-facing:
  Theorem 3.1.10 as the Euclidean textbook presentation of the bounded-sublevel-set minimax
  statement
- core/canonical:
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view:
  this file only, which recalls the earlier owner theorem instead of exporting a second local
  theorem or a non-exported `example`

Primitive data:
- a feasible set `Q : Set E`
- two real-valued objectives `f₁`, `f₂ : E → ℝ`
- closed convexity of their `WithTop` lifts on `Q`
- boundedness of the constrained sublevel sets of the pointwise maximum
  `x ↦ max (f₁ x) (f₂ x)` on `Q`

Derived API:
- the minimizing parameter `lam : unitInterval`
- the owner predicate
  `IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam`

Source/core/bridge triage:
- source-facing: the textbook Euclidean presentation of the two-function minimax statement
- core/canonical: `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: this numbered file, which reuses the earlier owner theorem directly

The earlier file already owns the exact mathematical content with the chapter's canonical
`constrainedSublevelSet` API. This file therefore recalls that theorem directly rather than
maintaining a parallel local wrapper or a non-exported restatement.
-/

/- Theorem 3.1.10: if `f₁` and `f₂` are real-valued functions whose canonical `WithTop` lifts are
closed and convex on a feasible set `Q`, and every constrained sublevel set of the pointwise
maximum `x ↦ max (f₁ x) (f₂ x)` on `Q` is bounded, then there exists a parameter
`λ* ∈ [0, 1]` for which the constrained minimum value of `x ↦ max (f₁ x) (f₂ x)` on `Q` equals
that of the convex combination `x ↦ λ* f₁ x + (1 - λ*) f₂ x`; Lean records this conclusion by the
owner predicate `IsMinimaxLinearizationParameter` on the subtype `Q`. -/
recall exists_minimax_parameter_of_bounded_constrainedSublevelSets

/-! ### Theorem_3_1_11 (from Chap03) -/
noncomputable section

open scoped Topology
open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.11 lies in the chapter's extended-valued convex local-regularity domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions, together with the metric-topological bridge
  from interior membership to contained balls.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite-value representative;
- `Set.interior` and `Metric.mem_nhds_iff`, the canonical topological owners turning interior
  membership into an explicit contained ball;
- `ConvexOn.locallyLipschitzOn_interior` in mathlib, the canonical local-regularity owner for
  convex real-valued functions on the interior of a convex set;
- `LipschitzWith.isBounded_image`, the canonical bounded-image theorem used after obtaining a
  Lipschitz ball.

Best owner abstraction:
- core/canonical: the topological interior owner `interior (dom f)` for the contained-ball
  bridge, together with `ConvexOn.locallyLipschitzOn_interior` on
  `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- source-facing: an explicit metric ball in `dom f`, then Lipschitz and bounded-image
  consequences around interior points of `dom f`;
- bridge/view: the passage from neighborhood statements to concrete metric balls via
  `Metric.mem_nhds_iff` and `Metric.mem_nhdsWithin_iff`.

Primitive data:
- for the source-facing ball-existence bridge: only the interior-point witness
  `hx0 : x0 ∈ interior (dom f)`;
- for the convex-analytic consequences: the convexity witness
  `hf : ConvexOn ℝ (dom f) (withTopRealPart f)` together with the same interior-point witness.

Derived API:
- a metric ball around `x0` contained in `dom f`;
- a common metric ball contained in `dom f` on which `withTopRealPart f` is Lipschitz;
- boundedness of the image of that same ball under `withTopRealPart f`.

Source/core/bridge triage:
- source-facing: the explicit-ball statements recorded below;
- core/canonical: `interior (dom f)` for the purely topological bridge, and
  `ConvexOn.locallyLipschitzOn_interior` for the convex local-regularity owner;
- bridge/view: shrinking neighborhood conclusions to explicit balls.

The previous version kept the raw set `{x | f x < ⊤}`, the ad hoc representative
`fun x ↦ (f x).untopD 0`, a renamed local copy of the mathlib owner theorem, and a purely
topological interior-ball bridge inside the unrelated `ConvexOn` namespace. This refinement
reuses the chapter owners `dom` and `withTopRealPart`, drops the duplicate theorem shell in favor
of a direct recall, weakens the convex-analytic consequences from the concrete model
`EuclideanSpace ℝ (Fin n)` to the canonical finite-dimensional real normed-space layer actually
used by the owner theorem, and places the interior-ball bridge on the weaker `dom`/topological
owner surface it genuinely belongs to.
-/

/- Theorem 3.1.11's main owner is mathlib's `ConvexOn.locallyLipschitzOn_interior`; in the
chapter, it is applied to `C = dom f` and `f = withTopRealPart f`. -/
recall ConvexOn.locallyLipschitzOn_interior

variable {E : Type u}

/-- An interior point of the effective domain admits a metric ball contained in the effective
domain. -/
-- Proof sketch: `x₀ ∈ interior (dom f)` means exactly that `dom f` is a neighborhood of `x₀`;
-- `Metric.mem_nhds_iff` then produces a metric ball contained in `dom f`.
theorem exists_ball_subset_effectiveDomain_of_mem_interior
    [PseudoMetricSpace E] {f : E → WithTop ℝ} {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f := by
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r, hr, hrsub⟩
  exact ⟨r, hr, hrsub.trans interior_subset⟩

namespace ConvexOn

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- At an interior point of the effective domain, the finite-value representative is Lipschitz on
some metric ball around that point, and that ball stays inside the effective domain. -/
-- Proof sketch: apply the owner theorem `hf.locallyLipschitzOn_interior` at `x₀`, then use
-- `Metric.mem_nhdsWithin_iff` to shrink the neighborhood within `interior (dom f)` to a metric
-- ball. Since that smaller ball still lies in `interior (dom f)`, it is also contained in
-- `dom f`.
theorem exists_ball_lipschitzOnWith_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      ∃ K : NNReal, LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r) := by
  obtain ⟨K, t, ht, hK⟩ := hf.locallyLipschitzOn_interior hx0
  rcases Metric.mem_nhdsWithin_iff.1 ht with ⟨r₁, hr₁, hr₁sub⟩
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r₂, hr₂, hr₂sub⟩
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, K, hK.mono ?_⟩
  · intro y hy
    exact interior_subset <|
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro y hy
    exact hr₁sub ⟨Metric.ball_subset_ball (min_le_left _ _) hy,
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/-- A convex extended-real-valued function has bounded finite-value image on some ball around any
interior point of its effective domain. -/
-- Proof sketch: obtain a Lipschitz ball from
-- `exists_ball_lipschitzOnWith_of_mem_interior`; that same ball is already known to lie in
-- `dom f`. In a finite-dimensional real normed space, metric balls are bounded, and
-- `LipschitzWith.isBounded_image` bounds the image of that ball under `withTopRealPart f`.
theorem exists_ball_isBounded_image_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      Bornology.IsBounded (withTopRealPart f '' Metric.ball x0 r) := by
  obtain ⟨r, hr, hball, K, hK⟩ := exists_ball_lipschitzOnWith_of_mem_interior hf hx0
  have hclosed :
      Bornology.IsBounded (Metric.closedBall (withTopRealPart f x0) (K * r)) :=
    Metric.isBounded_closedBall
  refine ⟨r, hr, hball, hclosed.subset ?_⟩
  rintro z ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall]
  exact (hK.dist_le_mul y hy x0 (Metric.mem_ball_self hr)).trans <|
    mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hy).le K.coe_nonneg

end ConvexOn

/-! ### Lemma_3_1_12 (from Chap03) -/
noncomputable section

open scoped Pointwise Topology WithTopConvexAnalysis

universe u

/- Lemma 3.1.12 lies in the chapter's weighted-sum / subdifferential calculus for closed convex
`WithTop ℝ`-valued functions on the intrinsic ambient spaces already used by the chapter owners.

Sampled owner declarations:
- `dom` and `withTopRealPart` from `Definition_3_3`
- `ClosedConvexOn` and `ClosedConvexFunction` from `Definition_3_1_1_5`
- `subdifferential` and the notation `∂ f(x)` from `Definition_3_1_5`
- `ClosedConvexOn.nonneg_smul` and `ClosedConvexOn.add_inter` from `Theorem_3_1_5`

Best owner abstraction:
- the canonical pointwise weighted sum
  `((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)`

Primitive data:
- the scalars `α₁`, `α₂`
- the functions `f₁`, `f₂`

Derived API:
- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`
- `ClosedConvexFunction.nonneg_weighted_add`
- `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos`
- `subdifferential_nonneg_weighted_add_eq_of_pos`

Source/core/bridge triage:
- source-facing: the numbered weighted-sum conclusions of Lemma 3.1.12
- core/canonical:
  `dom`, `ClosedConvexOn`, `ClosedConvexFunction`, `subdifferential`,
  pointwise scalar multiplication, and pointwise addition
- bridge/view: the positive-weight effective-domain identity for the canonical weighted sum

The previous local wrapper changed the mathematics at zero weights by forcing finiteness on
`dom f₁ ∩ dom f₂`. This refinement removes that duplicate wheel and states the lemma directly for
the canonical pointwise weighted sum. Strict positivity now appears exactly on the domain,
interior-domain, and subdifferential formulas where the common-domain identity is valid; the
closed-convex statement itself remains at the correct nonnegative-weight level. -/

section WeightedAdd

variable {X : Type u}

section ClosedConvex

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
variable {f₁ f₂ : X → WithTop ℝ} {α₁ α₂ : ℝ}

/-- The nonnegative weighted pointwise sum of two closed convex functions is again a closed convex
function. -/
-- Proof sketch: apply the canonical owner rules `ClosedConvexOn.nonneg_smul` and
-- `ClosedConvexOn.add_inter` to the positive-weight case, and split the zero-weight cases to the
-- corresponding single-summand scalar-multiple statements.
theorem ClosedConvexFunction.nonneg_weighted_add
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 ≤ α₁)
    (hα₂ : 0 ≤ α₂) :
    ClosedConvexFunction ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) := sorry

end ClosedConvex

section EffectiveDomainInterior

variable [TopologicalSpace X]
variable {f₁ f₂ : X → WithTop ℝ} {α₁ α₂ : ℝ}

/-- Under strictly positive weights, the effective domain of the canonical weighted pointwise sum
is exactly the common effective domain of the two summands. -/
-- Proof sketch: positivity forces every occurrence of `⊤` in either summand to remain `⊤` after
-- scalar multiplication, so finiteness of the pointwise sum is equivalent to simultaneous
-- finiteness of both summands.
theorem withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) =
      dom f₁ ∩ dom f₂ := sorry

/-- Lemma 3.1.12 (1): under strictly positive weights, the interior of the effective domain of the
canonical weighted pointwise sum equals the intersection of the interiors of the summand domains.
-/
-- Proof sketch: rewrite the effective domain using
-- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`, then apply the canonical
-- topological identity `interior (A ∩ B) = interior A ∩ interior B`.
theorem interior_effectiveDomain_nonneg_weighted_add_eq_of_pos
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)) =
      interior (dom f₁) ∩ interior (dom f₂) := sorry

end EffectiveDomainInterior

section Subdifferential

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {f₁ f₂ : V → WithTop ℝ} {α₁ α₂ : ℝ}

/-- Lemma 3.1.12 (2): if `f₁` and `f₂` are closed convex and `α₁, α₂ > 0`, then at every interior
point of the effective domain of the canonical weighted pointwise sum, its subdifferential equals
the Minkowski sum of the scaled pointwise subdifferentials. -/
-- Proof sketch: use `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos` to place `x` in the
-- common interior effective domain of the summands. There the ordinary weighted sum is finite, so
-- the directional-derivative sum rule and the support-function description of subdifferentials
-- identify the subdifferential of the weighted sum with the weighted Minkowski sum.
theorem subdifferential_nonneg_weighted_add_eq_of_pos
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂)
    {x : V}
    (hx : x ∈ interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))) :
    ∂ (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))(x) =
      α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) := sorry

end Subdifferential

end WeightedAdd

end

/-! ### Theorem_3_1_12 (from Chap03) -/
universe u

noncomputable section

open Filter Set
open scoped Topology WithTopConvexAnalysis

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-
Theorem 3.1.12 lies in the chapter's convex directional-derivative bridge domain.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite real representative of an `ℝ ∪ {+∞}`-valued function;
- `ConvexOn.comp_affineMap`, the canonical way to pass convexity to the one-variable directional
  slice;
- `ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior` in mathlib
  `Analysis/Convex/Deriv.lean`, the owner theorem for one-sided derivatives of convex real-valued
  functions on an interval-like interior domain.

Best owner abstraction:
- core/canonical: the one-variable convex derivative theorem
  `ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior` applied to the affine slice
  `α ↦ x + α • p`;
- bridge/view: the source-facing secant-slope limit statement below, together with eventual
  finiteness of the ray in `dom f`.

Primitive data:
- a convexity witness `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- an interior point `hx : x ∈ interior (dom f)`.

Derived API:
- eventual finiteness of `x + α • p` for `α ↓ 0`;
- convergence of the finite real secant slopes.

Source/core/bridge triage:
- source-facing: the secant-slope limit theorem below;
- core/canonical: the mathlib one-variable derivative theorem on the directional slice;
- bridge/view: the affine-line reduction from `E` to `ℝ`.
-/
/-- Theorem 3.1.12: a convex `ℝ ∪ {+∞}`-valued function has a finite one-sided directional
derivative in every direction at every interior point of its effective domain. -/
-- Proof sketch: apply the monotonicity argument for the positive secant slopes
-- `α ↦ (withTopRealPart f (x + α • p) - withTopRealPart f x) / α` of a convex function. The
-- interior-point hypothesis gives a backward point on the same affine line, which yields a
-- uniform lower bound on these slopes; hence they admit a finite right limit in `ℝ`.
theorem exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x p : E} (hx : x ∈ interior (dom f)) :
    ∃ d : ℝ,
      (∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f) ∧
        Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + p)
  let S : Set ℝ := g ⁻¹' dom f
  let φ : ℝ → ℝ := withTopRealPart f ∘ g
  have hg_apply (α : ℝ) : g α = x + α • p := by
    simpa [g, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x (x + p) α)
  have hconv : ConvexOn ℝ S φ := by
    simpa [S, φ, g] using
      hf.comp_affineMap (AffineMap.lineMap x (x + p))
  have hcont : Continuous g := by
    simpa [g] using
      (AffineMap.lineMap_continuous : Continuous (AffineMap.lineMap x (x + p) : ℝ →ᵃ[ℝ] E))
  have h0dom : ∀ᶠ α : ℝ in 𝓝 (0 : ℝ), g α ∈ dom f :=
    hcont.continuousAt.eventually_mem
      (by simpa [g] using
        (mem_interior_iff_mem_nhds.mp hx))
  have hS_nhds : S ∈ 𝓝 (0 : ℝ) := by
    simpa [S] using h0dom
  have hS0 : (0 : ℝ) ∈ interior S := mem_interior_iff_mem_nhds.mpr hS_nhds
  let d : ℝ := sInf (slope φ 0 '' {α ∈ S | 0 < α})
  have hderiv : HasDerivWithinAt φ d (Ioi (0 : ℝ)) 0 := by
    simpa [d] using hconv.hasDerivWithinAt_sInf_slope_of_mem_interior hS0
  have hIoi : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), g α ∈ dom f :=
    h0dom.filter_mono nhdsWithin_le_nhds
  have hdom_eventually : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f := by
    filter_upwards [hIoi] with α hα
    simpa [hg_apply α] using hα
  have hslope : Tendsto (slope φ 0) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    exact
      (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp)).mp hderiv
  have htendsto :
      Tendsto
        (fun α : ℝ ↦
          (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    simpa [φ, Function.comp, hg_apply, slope_fun_def_field] using hslope
  exact ⟨d, hdom_eventually, htendsto⟩

end

/-! ### Lemma_3_1_13 (from Chap03) -/
universe u v

open scoped WithTopConvexAnalysis

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/- Lemma 3.1.13 is a recall-only bridge in the chapter's finite-family pointwise-supremum /
subdifferential calculus domain for `WithTop ℝ`-valued convex functions.

Primary domain:
- finite nonempty pointwise suprema of closed convex extended-real-valued functions on the
  chapter's intrinsic ambient spaces.

Relevant sampled declarations in this domain:
- `pointwiseSupremumOn`
- `activePointwiseSupremumOnIndices`
- `ClosedConvexFunction`
- `subdifferential`

Best owner abstraction:
- the chapter owner `pointwiseSupremumOn`, specialized in `Lemma_3_13` to the finite set
  `Set.univ`.

Primitive data:
- none in this recall file; the imported owner surface already carries the only primitive
  mathematical inputs, namely a nonempty finite index type together with a family
  `φ : X → ι → WithTop ℝ`.

Derived API recalled here:
- the finite-supremum bridge `pointwiseSupremumOn_univ_eq_sup'`
- the finite active-set bridge
- the closed-convex, interior-domain, and active-subdifferential theorems for the `Set.univ`
  specialization

Source/core/bridge triage:
- source-facing: the finite-family specialization of Lemma 3.13
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`,
  `ClosedConvexFunction`, and `subdifferential`
- bridge/view: `pointwiseSupremumOn_univ_eq_sup'`,
  `mem_activePointwiseSupremumOnIndices_univ_iff`, and this numbered recall surface

This file now recalls the owner-centered `Set.univ` specialization instead of maintaining a
parallel finite-maximum wrapper layer.
-/

recall pointwiseSupremumOn_univ_eq_sup'
recall mem_activePointwiseSupremumOnIndices_univ_iff
recall closedConvexFunction_pointwiseSupremumOn_univ
recall interior_dom_pointwiseSupremumOn_univ
recall subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials

/-! ### Theorem_3_1_13 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.13 is source-facing in the chapter's affine-hyperplane strong-separation domain.

Primary domain:
- strong separation of disjoint closed convex subsets of a finite-dimensional real inner-product
  space when one side is bounded.

Relevant sampled declarations:
- `AreStronglySeparable` in `Definition_3_12`, the chapter owner predicate for two-set strong
  separation by an affine hyperplane;
- mathlib `geometric_hahn_banach_compact_closed` and
  `geometric_hahn_banach_closed_compact`, the canonical strict-separation owners for compact/closed
  convex sets by continuous linear functionals;
- mathlib `Metric.isCompact_of_isClosed_isBounded` together with
  `FiniteDimensional.proper_real`, the finite-dimensional bounded-to-compact bridge.

Best owner abstraction:
- `AreStronglySeparable`

Primitive data:
- the sets `Q₁`, `Q₂`;
- closedness, convexity, disjointness, and one-sided boundedness on a nonempty side.

Derived API:
- the bounded-to-compact bridge in proper real inner-product spaces;
- the functional-to-hyperplane conversion through `InnerProductSpace.toDual`.

Source/core/bridge triage:
- source-facing: the textbook bounded-one-side strong-separation theorem, stated intrinsically on
  nontrivial proper real inner-product spaces with finite-dimensional `ℝⁿ` available as a
  specialization;
- core/canonical: the chapter owner `AreStronglySeparable` together with mathlib's compact/closed
  Hahn--Banach separation theorems;
- bridge/view: this file, which converts the source boundedness hypothesis to the canonical
  compactness input and then transports the resulting functional separator to the chapter's
  vector-normal hyperplane API.
-/

variable [ProperSpace E] [Nontrivial E]

/-- Theorem 3.1.13: if `Q₁, Q₂` are closed convex subsets of a nontrivial proper real
inner-product space with empty intersection, and one nonempty side is bounded, then they admit a
strongly separating hyperplane. Specializing to finite-dimensional Euclidean spaces recovers the
textbook `ℝⁿ` statement. -/
-- Proof sketch: if the bounded nonempty side faces an empty set, choose any nonzero normal and
-- place the affine level strictly beyond the bounded image of that side under the induced
-- functional. Otherwise, a closed bounded set is compact in a proper space, so the bounded side
-- can be fed to mathlib's compact/closed Hahn--Banach separation theorem. The resulting
-- continuous linear functional is represented by a vector through `InnerProductSpace.toDual`, and
-- the strict bounds are recentered at the midpoint between the two separating levels to produce
-- the chapter owner `AreStronglySeparable`.
theorem areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side
    (Q₁ Q₂ : Set E)
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdisj : Disjoint Q₁ Q₂)
    (hbounded : (Q₁.Nonempty ∧ Bornology.IsBounded Q₁) ∨
      (Q₂.Nonempty ∧ Bornology.IsBounded Q₂)) :
    AreStronglySeparable Q₁ Q₂ := by
  rw [areStronglySeparable_iff]
  rcases hbounded with ⟨hQ₁_nonempty, hQ₁_bounded⟩ | ⟨hQ₂_nonempty, hQ₂_bounded⟩
  · rcases Set.eq_empty_or_nonempty Q₂ with rfl | hQ₂_nonempty
    · obtain ⟨g, hg⟩ := exists_ne (0 : E)
      let f : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) g
      rcases (hQ₁_bounded.image f).bddAbove with ⟨M, hM⟩
      refine ⟨g, hg, M + 1, ?_⟩
      constructor
      · intro x hx
        have hfxle : f x ≤ M := hM ⟨x, hx, rfl⟩
        simpa [f] using lt_of_le_of_lt hfxle (by linarith : M < M + 1)
      · intro y hy
        simp at hy
    · obtain ⟨f, u, v, hQ₁_lt, huv, hQ₂_lt⟩ :=
        geometric_hahn_banach_compact_closed hQ₁_convex
          (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded)
          hQ₂_convex hQ₂_closed hdisj
      let g : E := (InnerProductSpace.toDual ℝ E).symm f
      refine ⟨g, ?_, (u + v) / 2, ?_⟩
      · intro hg
        have hf : f = 0 := by
          calc
            f = (InnerProductSpace.toDual ℝ E) g := by simp [g]
            _ = 0 := by simp [hg]
        rcases hQ₁_nonempty with ⟨x, hx⟩
        rcases hQ₂_nonempty with ⟨y, hy⟩
        have hxlt : 0 < u := by simpa [hf] using hQ₁_lt x hx
        have hygt : v < 0 := by simpa [hf] using hQ₂_lt y hy
        linarith
      · constructor
        · intro x hx
          have hxltu : f x < u := hQ₁_lt x hx
          have hu_mid : u < (u + v) / 2 := by linarith
          change inner ℝ g x < (u + v) / 2
          simpa [g] using hxltu.trans hu_mid
        · intro y hy
          have hvlty : v < f y := hQ₂_lt y hy
          have hmid_v : (u + v) / 2 < v := by linarith
          change (u + v) / 2 < inner ℝ g y
          simpa [g] using hmid_v.trans hvlty
  · rcases Set.eq_empty_or_nonempty Q₁ with rfl | hQ₁_nonempty
    · obtain ⟨g, hg⟩ := exists_ne (0 : E)
      let f : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) g
      rcases (hQ₂_bounded.image f).bddBelow with ⟨m, hm⟩
      refine ⟨g, hg, m - 1, ?_⟩
      constructor
      · intro x hx
        simp at hx
      · intro y hy
        have hmle : m ≤ f y := hm ⟨y, hy, rfl⟩
        change m - 1 < inner ℝ g y
        simpa [f] using lt_of_lt_of_le (by linarith : m - 1 < m) hmle
    · obtain ⟨f, u, v, hQ₁_lt, huv, hQ₂_lt⟩ :=
        geometric_hahn_banach_closed_compact hQ₁_convex hQ₁_closed
          hQ₂_convex (Metric.isCompact_of_isClosed_isBounded hQ₂_closed hQ₂_bounded) hdisj
      let g : E := (InnerProductSpace.toDual ℝ E).symm f
      refine ⟨g, ?_, (u + v) / 2, ?_⟩
      · intro hg
        have hf : f = 0 := by
          calc
            f = (InnerProductSpace.toDual ℝ E) g := by simp [g]
            _ = 0 := by simp [hg]
        rcases hQ₁_nonempty with ⟨x, hx⟩
        rcases hQ₂_nonempty with ⟨y, hy⟩
        have hxlt : 0 < u := by simpa [hf] using hQ₁_lt x hx
        have hygt : v < 0 := by simpa [hf] using hQ₂_lt y hy
        linarith
      · constructor
        · intro x hx
          have hxltu : f x < u := hQ₁_lt x hx
          have hu_mid : u < (u + v) / 2 := by linarith
          change inner ℝ g x < (u + v) / 2
          simpa [g] using hxltu.trans hu_mid
        · intro y hy
          have hvlty : v < f y := hQ₂_lt y hy
          have hmid_v : (u + v) / 2 < v := by linarith
          change (u + v) / 2 < inner ℝ g y
          simpa [g] using hmid_v.trans hvlty

end

/-! ### Lemma_3_1_14 (from Chap03) -/
noncomputable section

open Set
open scoped WithTopConvexAnalysis

universe u v

variable {ι : Type u} {X : Type v}

/- Lemma 3.1.14 sits in the chapter's extended-valued convex-analysis domain of subset-indexed
pointwise suprema and constrained subdifferentials.

Sampled owner declarations:
- `pointwiseSupremumOn`
- `pointwiseSupremumOnEffectiveDomain`
- `ClosedConvexOn.pointwise_sSup`
- `constrainedSubdifferential`

Best owner abstraction:
- the subset-indexed pointwise-supremum owner surface from `Theorem_3_1_8`, together with the
  earlier owner notions `ClosedConvexOn` and `constrainedSubdifferential`

Primitive data:
- the owner pointwise-supremum object `pointwiseSupremumOn Δ φ`
- the owner finite-value domain `pointwiseSupremumOnEffectiveDomain Q Δ φ`
- the earlier chapter owners `ClosedConvexOn` and `constrainedSubdifferential`

Derived API in this file:
- the active-index set `activePointwiseSupremumOnIndices Δ φ x`
- the membership bridge `mem_activePointwiseSupremumOnIndices_iff`
- the active-slice convex-hull inclusion theorem

Source/core/bridge triage:
- source-facing: `activePointwiseSupremumOnIndices`,
  `convexHull_activePointwiseSupremumOnSubdifferentials_subset`
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`,
  `ClosedConvexOn`, `constrainedSubdifferential`, `ClosedConvexOn.pointwise_sSup`
- bridge/view: `mem_activePointwiseSupremumOnIndices_iff`

This file therefore adds only the active-slice layer from the source text and reuses the earlier
chapter owners directly instead of re-declaring them locally. Its source-facing inclusion theorem
inherits the intrinsic real-inner-product-space ambient assumptions already required by
`constrainedSubdifferential`, instead of freezing that theorem to the textbook Euclidean model. -/

/-- The active parameter set `I(x)` for the subset-indexed pointwise supremum over `Δ`. -/
def activePointwiseSupremumOnIndices
    (Δ : Set ι) (φ : X → ι → WithTop ℝ) (x : X) : Set ι :=
  {y | y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x}

/-- Membership in `activePointwiseSupremumOnIndices Δ φ x` means that `y ∈ Δ` attains the
pointwise supremum value at `x`. -/
@[simp]
theorem mem_activePointwiseSupremumOnIndices_iff
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {y : ι} :
    y ∈ activePointwiseSupremumOnIndices Δ φ x ↔
      y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x :=
  Iff.rfl

variable {E : Type v} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 3.1.14, active-slice inclusion part: at every
`x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ`, the constrained subdifferential of
`pointwiseSupremumOn Δ φ` over `pointwiseSupremumOnEffectiveDomain Q Δ φ` contains the convex
hull of the constrained subdifferentials of the active slices `y ∈ I(x)`.

The closed-convex part of Lemma 3.1.14 is the separate owner theorem
`ClosedConvexOn.pointwise_sSup`. -/
-- Proof sketch: every `g ∈ constrainedSubdifferential Q (fun z ↦ φ z y) x` with active `y`
-- satisfies the subgradient inequality for `pointwiseSupremumOn Δ φ` because
-- `pointwiseSupremumOn Δ φ z ≥ φ z y` for all `z ∈ Q` and activity gives
-- `φ x y = pointwiseSupremumOn Δ φ x`. The target constrained subdifferential is convex, so it
-- contains the convex hull of the union of those active-slice subdifferentials.
theorem convexHull_activePointwiseSupremumOnSubdifferentials_subset
    {Q : Set E} {Δ : Set ι} {φ : E → ι → WithTop ℝ} {x : E}
    (hx : x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ) :
    convexHull ℝ
        (⋃ y ∈ activePointwiseSupremumOnIndices Δ φ x,
          ∂[Q] (fun z ↦ φ z y) (x)) ⊆
      ∂[pointwiseSupremumOnEffectiveDomain Q Δ φ] (pointwiseSupremumOn Δ φ) (x) := sorry

end

/-! ### Theorem_3_1_14 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.14 is a recall-only file in the chapter's affine-hyperplane support domain.

Relevant sampled declarations:
- `AffineHyperplane`
- `AffineHyperplane.IsSupporting`
- `IsSupportingHyperplane`
- `exists_supporting_hyperplane_at_boundary_point_of_closed_convex`

Best owner abstraction:
- the earlier source-facing theorem
  `exists_supporting_hyperplane_at_boundary_point_of_closed_convex`, built on the chapter's
  `AffineHyperplane` owner API.

Source/core/bridge triage:
- source-facing: this numbered theorem item;
- core/canonical: the earlier chapter theorem with the same mathematical content;
- bridge/view: this later theorem name, which is only a textual restatement of the same result.

Primitive data:
- the closed convex set `Q` and the boundary point `x₀`.

Derived API:
- the coordinate witness `(g, γ)` together with membership in `hyperplane g γ` and the predicate
  `IsSupportingHyperplane Q g γ`.

This file previously duplicated the exact theorem surface already provided by
`Theorem_3_1_4_2.lean`. It now reuses that earlier declaration directly instead of keeping a
second parallel theorem with the same statement under a different name.
-/
recall exists_supporting_hyperplane_at_boundary_point_of_closed_convex
    [FiniteDimensional ℝ E] (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E}
    (hx₀ : x₀ ∈ frontier Q) :
    ∃ g : E, ∃ γ : ℝ, x₀ ∈ hyperplane g γ ∧ IsSupportingHyperplane Q g γ

end

/-! ### Lemma_3_1_15 (from Chap03) -/
/- Lemma 3.1.15 lies in the chapter's real-valued subdifferential / positive-homogeneity domain.

Primary domain:
- subdifferentials of positively homogeneous real-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `IsSubgradientAt` in `Definition_3_1_5`, the chapter owner predicate for extended-valued
  subgradients;
- `subdifferential` in `Definition_3_1_5`, the derived owner set-valued API;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner predicate for positive
  homogeneity;
- `subdifferential_eq_subdifferential_zero_of_posHomogeneous` in `Lemma_3_15`, the existing
  chapter theorem for this source fact.

Best owner abstraction:
- `subdifferential_eq_subdifferential_zero_of_posHomogeneous`, organized around
  `subdifferential (fun y ↦ (f y : WithTop ℝ))` and `IsPositivelyHomogeneousOn 1 Set.univ f`.

Primitive data:
- a real inner-product space `E`;
- a real-valued function `f : E → ℝ`;
- the positive-homogeneity owner hypothesis `IsPositivelyHomogeneousOn 1 Set.univ f`.

Derived API:
- the subdifferential identity at `x` in terms of the origin subdifferential and the touching
  condition `inner ℝ g x = f x`.

Source/core/bridge triage:
- source-facing: Lemma 3.1.15's description of the subdifferential of a positively
  `1`-homogeneous function;
- core/canonical: `IsSubgradientAt`, `subdifferential`, and `IsPositivelyHomogeneousOn`;
- bridge/view: none beyond the coercion `fun y ↦ (f y : WithTop ℝ)` already absorbed by the owner
  theorem in `Lemma_3_15`.

The previous version duplicated a real-valued subgradient predicate, a real-valued
subdifferential, and a parallel theorem with an extra convexity hypothesis. That convexity
hypothesis is mathematically redundant here, and the owner theorem in `Lemma_3_15` already states
the source fact canonically. This file therefore recalls that theorem directly instead of keeping a
second local wrapper API. -/

recall subdifferential_eq_subdifferential_zero_of_posHomogeneous

/-! ### Theorem_3_1_15 (from Chap03) -/
noncomputable section

open scoped Topology
open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Theorem 3.1.15: an interior effective-domain point admits a closed ball still
contained in the interior of the effective domain. -/
lemma exists_closedBall_subset_interior_of_mem_interior
    {f : E → WithTop ℝ} {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ rho > 0, Metric.closedBall x0 rho ⊆ interior (dom f) := by
  -- Shrink the open interior neighborhood so the whole closed ball still stays inside it.
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r, hr, hrsub⟩
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro y hy
  exact hrsub (Metric.closedBall_subset_ball (half_lt_self hr) hy)

/-- Helper for Theorem 3.1.15: the base epigraph point over a closed ball around `x0` is a
boundary point of that constrained epigraph. -/
lemma basepoint_mem_frontier_constrainedEpigraph_closedBall
    {f : E → WithTop ℝ} {x0 : E} {rho : ℝ} (hrho : 0 < rho)
    (hball : Metric.closedBall x0 rho ⊆ interior (dom f)) :
    (x0, withTopRealPart f x0) ∈
      frontier (constrainedEpigraph (Metric.closedBall x0 rho) f) := by
  have hx0_ball : x0 ∈ Metric.closedBall x0 rho := Metric.mem_closedBall_self hrho.le
  have hx0_dom : x0 ∈ dom f := interior_subset (hball hx0_ball)
  rw [frontier_eq_closure_inter_closure]
  constructor
  · -- The basepoint itself lies in the constrained epigraph, hence in its closure.
    exact subset_closure <| mem_constrainedEpigraph_iff.2
      ⟨hx0_ball, by
        simpa using le_of_eq (coe_withTopRealPart (f := f) hx0_dom).symm⟩
  · -- Lowering only the height coordinate leaves every neighborhood through the complement.
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    refine ⟨(x0, withTopRealPart f x0 - ε / 2), ?_, ?_⟩
    · intro hmem
      rcases mem_constrainedEpigraph_iff.1 hmem with ⟨_, hle⟩
      have hlt : withTopRealPart f x0 - ε / 2 < withTopRealPart f x0 := by
        linarith
      rw [← coe_withTopRealPart hx0_dom] at hle
      have hle_real : withTopRealPart f x0 ≤ withTopRealPart f x0 - ε / 2 := by
        exact_mod_cast hle
      linarith
    · rw [Prod.dist_eq, dist_self, max_eq_right]
      · rw [Real.dist_eq]
        have hhalf_lt : ε / 2 < ε := by
          linarith
        simpa [abs_of_nonneg (by linarith : 0 ≤ ε / 2)] using hhalf_lt
      · exact dist_nonneg

local notation "Z" => WithLp 2 (E × ℝ)
local notation "eZ" => WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ

/-- Helper for Theorem 3.1.15: on the real height coordinate, the real inner product is ordinary
multiplication. -/
lemma real_inner_scalar_eq_mul (a t : ℝ) : inner ℝ a t = a * t := by
  exact RCLike.inner_apply' (𝕜 := ℝ) a t

/-- Helper for Theorem 3.1.15: transport the raw-product frontier point to the `L²` product
owner used by the supporting-hyperplane theorem. -/
lemma basepoint_mem_frontier_constrainedEpigraph_closedBall_prodL2
    {f : E → WithTop ℝ} {x0 : E} {rho : ℝ} (hrho : 0 < rho)
    (hball : Metric.closedBall x0 rho ⊆ interior (dom f)) :
    WithLp.toLp 2 (x0, withTopRealPart f x0) ∈
      frontier (eZ ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) := by
  let e : Z ≃L[ℝ] E × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  -- Transport the raw frontier statement across the product `L²` homeomorphism.
  have hraw :
      (x0, withTopRealPart f x0) ∈
        frontier (constrainedEpigraph (Metric.closedBall x0 rho) f) :=
    basepoint_mem_frontier_constrainedEpigraph_closedBall hrho hball
  have hpre :
      e.toHomeomorph ⁻¹' frontier (constrainedEpigraph (Metric.closedBall x0 rho) f) =
        frontier (e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) :=
    Homeomorph.preimage_frontier e.toHomeomorph
      (constrainedEpigraph (Metric.closedBall x0 rho) f)
  have hraw' :
      e.symm (x0, withTopRealPart f x0) ∈
        frontier (e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) := by
    rw [← hpre]
    exact hraw
  simpa using hraw'

/-- Helper for Theorem 3.1.15: rewrite the supporting-hyperplane inequality on the `L²` product
owner into the pair-coordinate inequality used by the textbook epigraph argument. -/
lemma supporting_hyperplane_component_inequality_prodL2
    {Q : Set Z} {n : Z} {γ : ℝ}
    (hQ : IsSupportingHyperplane Q n γ)
    {x : E} {τ : ℝ} (hz : WithLp.toLp 2 (x, τ) ∈ Q) :
    inner ℝ n.fst x + n.snd * τ ≤ γ := by
  -- Rewrite the ambient `WithLp` inner product into the pair coordinates `(x, τ)`.
  have hineq : inner ℝ n (WithLp.toLp 2 (x, τ)) ≤ γ := hQ.le_offset hz
  have hineq' : inner ℝ n.fst x + inner ℝ n.snd τ ≤ γ := by
    simpa [WithLp.prod_inner_apply] using hineq
  rw [real_inner_scalar_eq_mul] at hineq'
  exact hineq'

/-- Helper for Theorem 3.1.15: the supporting normal of the local constrained epigraph has
strictly negative height component. -/
lemma supporting_hyperplane_snd_neg_of_constrainedEpigraph_closedBall
    {f : E → WithTop ℝ} {x0 : E} {rho : ℝ} (hrho : 0 < rho)
    (hball : Metric.closedBall x0 rho ⊆ interior (dom f))
    {n : Z} {γ : ℝ}
    (hz0 : WithLp.toLp 2 (x0, withTopRealPart f x0) ∈ hyperplane n γ)
    (hsupport : IsSupportingHyperplane
      (eZ ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) n γ) :
    n.snd < 0 := by
  let e : Z ≃L[ℝ] E × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  have hx0_ball : x0 ∈ Metric.closedBall x0 rho := Metric.mem_closedBall_self hrho.le
  have hx0_dom : x0 ∈ dom f := interior_subset (hball hx0_ball)
  have hcontact : inner ℝ n.fst x0 + n.snd * withTopRealPart f x0 = γ := by
    -- The supporting hyperplane meets the constrained epigraph at the basepoint.
    have hcontact' : inner ℝ n.fst x0 + inner ℝ n.snd (withTopRealPart f x0) = γ := by
      simpa [WithLp.prod_inner_apply] using hz0
    rw [real_inner_scalar_eq_mul] at hcontact'
    exact hcontact'
  have hsnd_nonpos : n.snd ≤ 0 := by
    -- Testing the support inequality along the vertical ray gives the nonpositive sign.
    have hz1 :
        WithLp.toLp 2 (x0, withTopRealPart f x0 + 1) ∈
          e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f := by
      have hmem :
          (x0, withTopRealPart f x0 + 1) ∈
            constrainedEpigraph (Metric.closedBall x0 rho) f := by
        exact mem_constrainedEpigraph_iff.2
          ⟨hx0_ball, by
            rw [← coe_withTopRealPart (f := f) hx0_dom]
            exact_mod_cast (show withTopRealPart f x0 ≤ withTopRealPart f x0 + 1 by linarith)⟩
      simpa [Set.preimage, e] using hmem
    have hineq1 :
        inner ℝ n.fst x0 + n.snd * (withTopRealPart f x0 + 1) ≤ γ :=
      supporting_hyperplane_component_inequality_prodL2 hsupport hz1
    linarith
  by_contra hsnd_nonneg
  have hsnd_zero : n.snd = 0 := by linarith
  have hfst_ne_zero : n.fst ≠ 0 := by
    intro hfst_zero
    apply hsupport.ne_zero
    apply e.injective
    change (n.fst, n.snd) = (0, 0)
    simp [hfst_zero, hsnd_zero]
  let s : ℝ := rho / (2 * ‖n.fst‖)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact div_pos hrho (mul_pos zero_lt_two (norm_pos_iff.mpr hfst_ne_zero))
  have hs_norm : ‖s • n.fst‖ = rho / 2 := by
    dsimp [s]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
    have hcalc : (rho / (2 * ‖n.fst‖)) * ‖n.fst‖ = rho / 2 := by
      field_simp [norm_ne_zero_iff.mpr hfst_ne_zero]
    simpa using hcalc
  let xPlus : E := x0 + s • n.fst
  have hxPlus_ball : xPlus ∈ Metric.closedBall x0 rho := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hxPlus_dist : ‖xPlus - x0‖ = rho / 2 := by
      simp [xPlus, hs_norm, sub_eq_add_neg, add_assoc]
    linarith [hxPlus_dist, hrho]
  have hxPlus_dom : xPlus ∈ dom f := interior_subset (hball hxPlus_ball)
  have hzPlus :
      WithLp.toLp 2 (xPlus, withTopRealPart f xPlus) ∈
        e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f := by
    have hmem :
        (xPlus, withTopRealPart f xPlus) ∈
          constrainedEpigraph (Metric.closedBall x0 rho) f := by
      exact mem_constrainedEpigraph_iff.2
        ⟨hxPlus_ball, by
          simpa using le_of_eq (coe_withTopRealPart (f := f) hxPlus_dom).symm⟩
    simpa [Set.preimage, e] using hmem
  have hineqPlus :
      inner ℝ n.fst xPlus + n.snd * withTopRealPart f xPlus ≤ γ :=
    supporting_hyperplane_component_inequality_prodL2 hsupport hzPlus
  have hcontr : s * ‖n.fst‖ ^ 2 ≤ 0 := by
    rw [hsnd_zero] at hineqPlus hcontact
    have hxPlus_shift :
        inner ℝ n.fst xPlus = inner ℝ n.fst x0 + s * ‖n.fst‖ ^ 2 := by
      -- Moving in the `n.fst` direction changes the supporting functional by `s ‖n.fst‖²`.
      dsimp [xPlus]
      rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    linarith
  have hstrict : 0 < s * ‖n.fst‖ ^ 2 := by
    have hnorm_sq_pos : 0 < ‖n.fst‖ ^ 2 := by
      positivity
    positivity
  linarith

/-- Helper for Theorem 3.1.15: a local affine support inequality on a closed ball extends to the
whole effective domain by convexity along segments from `x0`. -/
lemma global_support_of_local_support_closedBall
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ dom f) {rho : ℝ} (hrho : 0 < rho) {g : E}
    (hlocal : ∀ ⦃x : E⦄, x ∈ Metric.closedBall x0 rho →
      withTopRealPart f x0 + inner ℝ g (x - x0) ≤ withTopRealPart f x) :
    ∀ ⦃y : E⦄, y ∈ dom f →
      withTopRealPart f x0 + inner ℝ g (y - x0) ≤ withTopRealPart f y := by
  intro y hy
  by_cases hy_eq : y = x0
  · subst hy_eq
    simp
  · let t : ℝ := min 1 (rho / ‖y - x0‖)
    let z : E := (1 - t) • x0 + t • y
    have hy_sub_ne : y - x0 ≠ 0 := sub_ne_zero.mpr hy_eq
    have hnorm_pos : 0 < ‖y - x0‖ := norm_pos_iff.mpr hy_sub_ne
    have ht_pos : 0 < t := by
      exact lt_min zero_lt_one (div_pos hrho hnorm_pos)
    have ht_le_one : t ≤ 1 := min_le_left _ _
    have hz_eq : z - x0 = t • (y - x0) := by
      dsimp [z, t]
      simp [sub_eq_add_neg, add_comm, add_left_comm, smul_add, add_smul]
    have hz_dom : z ∈ dom f := by
      -- Follow the segment from `x0` to `y` inside the convex effective domain.
      dsimp [z, t]
      exact hf.1 hx0 hy (sub_nonneg.mpr ht_le_one) ht_pos.le (by linarith)
    have hz_closedBall : z ∈ Metric.closedBall x0 rho := by
      rw [Metric.mem_closedBall, dist_eq_norm, hz_eq, norm_smul, Real.norm_of_nonneg ht_pos.le]
      have ht_mul : t * ‖y - x0‖ ≤ rho := by
        have hmul :
            t * ‖y - x0‖ ≤ (rho / ‖y - x0‖) * ‖y - x0‖ :=
          mul_le_mul_of_nonneg_right (min_le_right 1 (rho / ‖y - x0‖)) hnorm_pos.le
        have hrewrite : (rho / ‖y - x0‖) * ‖y - x0‖ = rho := by
          field_simp [hnorm_pos.ne']
        simpa [hrewrite, mul_comm, mul_left_comm, mul_assoc] using hmul
      simpa using ht_mul
    have hlocal_z : withTopRealPart f x0 + inner ℝ g (z - x0) ≤ withTopRealPart f z :=
      hlocal hz_closedBall
    have hconv_z :
        withTopRealPart f z ≤
          (1 - t) * withTopRealPart f x0 + t * withTopRealPart f y := by
      dsimp [z, t]
      exact hf.2 hx0 hy (sub_nonneg.mpr ht_le_one) ht_pos.le (by linarith)
    have hlocal_y :
        withTopRealPart f x0 + t * inner ℝ g (y - x0) ≤ withTopRealPart f z := by
      simpa [hz_eq, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hlocal_z
    have hscaled :
        t * (withTopRealPart f x0 + inner ℝ g (y - x0)) ≤ t * withTopRealPart f y := by
      nlinarith
    nlinarith

/-- Helper for Theorem 3.1.15: convexity gives a Lipschitz ball around every interior point of
the effective domain. -/
lemma exists_lipschitz_ball_subset_effectiveDomain_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      ∃ K : NNReal, LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r) := by
  -- Start from the canonical local-Lipschitz theorem on the interior and shrink to a metric ball.
  obtain ⟨K, s, hs, hK⟩ := hf.locallyLipschitzOn_interior hx0
  rcases Metric.mem_nhdsWithin_iff.1 hs with ⟨r1, hr1, hr1sub⟩
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r2, hr2, hr2sub⟩
  refine ⟨min r1 r2, lt_min hr1 hr2, ?_, K, hK.mono ?_⟩
  · intro y hy
    exact interior_subset <| hr2sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro y hy
    exact hr1sub ⟨Metric.ball_subset_ball (min_le_left _ _) hy,
      hr2sub (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/-- Helper for Theorem 3.1.15: the supporting hyperplane of the local closed-ball epigraph yields
an affine lower support on that closed ball. -/
lemma exists_local_affine_support_on_closedBall_of_convexOn_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ rho > 0, ∃ g : E, ∀ ⦃x : E⦄, x ∈ Metric.closedBall x0 rho →
      withTopRealPart f x0 + inner ℝ g (x - x0) ≤ withTopRealPart f x := by
  -- Route correction: keep the textbook support-hyperplane proof, but transport the constrained
  -- epigraph once to the `WithLp 2 (E × ℝ)` owner before applying Theorem 3.1.14.
  obtain ⟨r, hr, hball_dom, K, hK⟩ :=
    exists_lipschitz_ball_subset_effectiveDomain_of_mem_interior hf hx0
  let rho : ℝ := r / 2
  let e : Z ≃L[ℝ] E × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  have hrho : 0 < rho := by
    dsimp [rho]
    exact half_pos hr
  have hclosed_subset_ball : Metric.closedBall x0 rho ⊆ Metric.ball x0 r := by
    dsimp [rho]
    exact Metric.closedBall_subset_ball (half_lt_self hr)
  have hball :
      Metric.closedBall x0 rho ⊆ interior (dom f) := by
    intro y hy
    have hy_ball : y ∈ Metric.ball x0 r := hclosed_subset_ball hy
    exact mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hy_ball) hball_dom
  have hcont_closedBall : ContinuousOn (withTopRealPart f) (Metric.closedBall x0 rho) :=
    hK.continuousOn.mono hclosed_subset_ball
  have hdom_closedBall : Metric.closedBall x0 rho ⊆ dom f := fun y hy ↦ interior_subset (hball hy)
  have hclosed_raw :
      IsClosed (constrainedEpigraph (Metric.closedBall x0 rho) f) := by
    rw [constrainedEpigraph_eq_epigraph_withTopRealPart hdom_closedBall]
    exact IsClosed.epigraph Metric.isClosed_closedBall hcont_closedBall
  have hconvOn_closedBall : ConvexOn ℝ (Metric.closedBall x0 rho) (withTopRealPart f) :=
    by
      refine ⟨convex_closedBall x0 rho, ?_⟩
      intro x hx y hy a b ha hb hab
      exact hf.2 (hdom_closedBall hx) (hdom_closedBall hy) ha hb hab
  have hconv_raw :
      Convex ℝ (constrainedEpigraph (Metric.closedBall x0 rho) f) := by
    rw [constrainedEpigraph_eq_epigraph_withTopRealPart hdom_closedBall]
    exact (convexOn_iff_convex_epigraph).1 hconvOn_closedBall
  let Qrho : Set Z := e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f
  have hz0_frontier :
      WithLp.toLp 2 (x0, withTopRealPart f x0) ∈ frontier Qrho := by
    simpa [Qrho] using
      basepoint_mem_frontier_constrainedEpigraph_closedBall_prodL2 hrho hball
  have hclosed_Qrho : IsClosed Qrho := by
    simpa [Qrho] using hclosed_raw.preimage e.continuous
  have hconv_Qrho : Convex ℝ Qrho := by
    simpa [Qrho] using hconv_raw.linear_preimage e.toLinearMap
  obtain ⟨n, γ, hz0, hsupport⟩ :=
    exists_supporting_hyperplane_at_boundary_point_of_closed_convex
      Qrho hclosed_Qrho hconv_Qrho hz0_frontier
  have hsnd_neg :
      n.snd < 0 :=
    supporting_hyperplane_snd_neg_of_constrainedEpigraph_closedBall hrho hball hz0 hsupport
  let g : E := (-n.snd)⁻¹ • n.fst
  refine ⟨rho, hrho, g, ?_⟩
  intro x hx
  have hx_dom : x ∈ dom f := hdom_closedBall hx
  have hz :
      WithLp.toLp 2 (x, withTopRealPart f x) ∈ Qrho := by
    have hmem :
        (x, withTopRealPart f x) ∈ constrainedEpigraph (Metric.closedBall x0 rho) f := by
      exact mem_constrainedEpigraph_iff.2
        ⟨hx, by
          simpa using le_of_eq (coe_withTopRealPart (f := f) hx_dom).symm⟩
    simpa [Qrho, Set.preimage, e] using hmem
  have hineq :
      inner ℝ n.fst x + n.snd * withTopRealPart f x ≤ γ :=
    supporting_hyperplane_component_inequality_prodL2 hsupport hz
  have hcontact :
      inner ℝ n.fst x0 + n.snd * withTopRealPart f x0 = γ := by
    -- Rewrite the contact condition at the basepoint into the pair coordinates.
    have hcontact' : inner ℝ n.fst x0 + inner ℝ n.snd (withTopRealPart f x0) = γ := by
      simpa [WithLp.prod_inner_apply] using hz0
    rw [real_inner_scalar_eq_mul] at hcontact'
    exact hcontact'
  let a : ℝ := -n.snd
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have hdiff0 :
      inner ℝ n.fst x - inner ℝ n.fst x0 ≤
        n.snd * (withTopRealPart f x0 - withTopRealPart f x) := by
    linarith
  have hdiff0' :
      inner ℝ n.fst x - inner ℝ n.fst x0 ≤
        a * (withTopRealPart f x - withTopRealPart f x0) := by
    dsimp [a]
    have hrewrite :
        n.snd * (withTopRealPart f x0 - withTopRealPart f x) =
          (-n.snd) * (withTopRealPart f x - withTopRealPart f x0) := by
      ring
    rw [hrewrite] at hdiff0
    exact hdiff0
  have hdiff :
      inner ℝ n.fst (x - x0) ≤ a * (withTopRealPart f x - withTopRealPart f x0) := by
    simpa [inner_sub_right] using hdiff0'
  have hscaled : a⁻¹ * inner ℝ n.fst (x - x0) ≤ withTopRealPart f x - withTopRealPart f x0 := by
    have hmul :
        a⁻¹ * inner ℝ n.fst (x - x0) ≤
          a⁻¹ * (a * (withTopRealPart f x - withTopRealPart f x0)) :=
      mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr ha_pos.le)
    simpa [ha_pos.ne', mul_assoc] using hmul
  -- Divide by the positive height coefficient and rewrite the result as the affine support claim.
  have hgineq : inner ℝ g (x - x0) ≤ withTopRealPart f x - withTopRealPart f x0 := by
    simpa [g, a, real_inner_smul_left] using hscaled
  linarith

/-- Helper for Theorem 3.1.15: a convex function admits a subgradient at every interior point of
its effective domain. -/
lemma subdifferential_nonempty_of_convexOn_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    (∂ f(x0)).Nonempty := by
  -- The supporting hyperplane of the local closed-ball epigraph yields a local affine support.
  obtain ⟨rho, hrho, g, hlocal⟩ :=
    exists_local_affine_support_on_closedBall_of_convexOn_of_mem_interior hf hx0
  refine ⟨g, mem_subdifferential_iff.mpr ?_⟩
  constructor
  · exact interior_subset hx0
  · intro y hy
    -- Convexity propagates the local affine support to every point of the effective domain.
    have hglobal :=
      global_support_of_local_support_closedBall hf (interior_subset hx0) hrho hlocal hy
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart (interior_subset hx0)]
    exact_mod_cast hglobal

/-- Helper for Theorem 3.1.15: every subgradient at `x0` is bounded in norm by any local
Lipschitz constant on a ball around `x0`. -/
lemma norm_le_of_mem_subdifferential_of_lipschitz_ball
    {f : E → WithTop ℝ} {x0 g : E} {r : ℝ} {K : NNReal}
    (hr : 0 < r) (hball : Metric.ball x0 r ⊆ dom f)
    (hK : LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r))
    (hg : g ∈ ∂ f(x0)) :
    ‖g‖ ≤ K := by
  by_cases hg_zero : g = 0
  · simp [hg_zero]
  · let u : E := ‖g‖⁻¹ • g
    let y : E := x0 + (r / 2) • u
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      calc
        ‖‖g‖⁻¹ • g‖ = |‖g‖⁻¹| * ‖g‖ := norm_smul _ _
        _ = ‖g‖⁻¹ * ‖g‖ := by
          rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        _ = 1 := by
          field_simp [norm_ne_zero_iff.mpr hg_zero]
    have hy_dist : dist y x0 = r / 2 := by
      rw [dist_eq_norm]
      calc
        ‖y - x0‖ = ‖(r / 2) • u‖ := by
          simp [y, u, sub_eq_add_neg, add_assoc]
        _ = |r / 2| * ‖u‖ := norm_smul _ _
        _ = r / 2 := by
          rw [abs_of_nonneg (by linarith : 0 ≤ r / 2)]
          simp [hu_norm]
    have hy_ball : y ∈ Metric.ball x0 r := by
      rw [Metric.mem_ball]
      linarith [hy_dist, hr]
    have hx0_ball : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hr
    have hx0_dom : x0 ∈ dom f := (mem_subdifferential_iff.mp hg).mem_dom
    have hy_dom : y ∈ dom f := hball hy_ball
    have hsub : f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ) :=
      (mem_subdifferential_iff.mp hg).2 hy_dom
    have hy_sub : y - x0 = (r / 2) • u := by
      simp [y, u, sub_eq_add_neg, add_assoc]
    have hinner :
        inner ℝ g (y - x0) = (r / 2) * ‖g‖ := by
      rw [hy_sub, real_inner_smul_right]
      dsimp [u]
      calc
        (r / 2) * inner ℝ g (‖g‖⁻¹ • g) = (r / 2) * (‖g‖⁻¹ * inner ℝ g g) := by
          rw [real_inner_smul_right]
        _ = (r / 2) * ‖g‖ := by
          rw [real_inner_self_eq_norm_sq]
          field_simp [norm_ne_zero_iff.mpr hg_zero]
    have hlower :
        (r / 2) * ‖g‖ ≤ withTopRealPart f y - withTopRealPart f x0 := by
      rw [← coe_withTopRealPart hy_dom, ← coe_withTopRealPart hx0_dom, hinner] at hsub
      have hreal : withTopRealPart f x0 + (r / 2) * ‖g‖ ≤ withTopRealPart f y := by
        exact_mod_cast hsub
      linarith
    have hdist :
        dist (withTopRealPart f y) (withTopRealPart f x0) ≤ K * dist y x0 :=
      hK.dist_le_mul y hy_ball x0 hx0_ball
    have hupper_abs :
        |withTopRealPart f y - withTopRealPart f x0| ≤ K * (r / 2) := by
      simpa [Real.dist_eq, hy_dist] using hdist
    have hupper :
        withTopRealPart f y - withTopRealPart f x0 ≤ K * (r / 2) := by
      exact le_trans (le_abs_self _) hupper_abs
    nlinarith

/- Theorem 3.1.15 lies in the chapter's extended-valued convex-subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on finite-dimensional real inner-product spaces.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative;
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients and their set-valued envelope;
- `ConvexOn.locallyLipschitzOn_interior` in mathlib, the canonical local regularity theorem for
  convex real-valued functions on the interior of a convex set;
- `exists_supporting_affineHyperplane_at_boundary_point_of_closed_convex` in `Theorem_3_1_4_2`,
  the chapter's owner-level supporting-hyperplane theorem on finite-dimensional real
  inner-product spaces.

Best owner abstraction:
- source-facing theorem on the existing owner surface
  `ConvexOn ℝ (dom f) (withTopRealPart f)` and `∂ f(x0)`.

Primitive data:
- the convexity hypothesis `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- the interior-domain hypothesis `hx0 : x0 ∈ interior (dom f)`.

Derived API:
- nonemptiness and boundedness of `∂ f(x0)`.

Source/core/bridge triage:
- source-facing: the textbook theorem that interior effective-domain points admit a nonempty
  bounded subdifferential;
- core/canonical: the owner declarations `dom`, `withTopRealPart`, and `subdifferential`;
- bridge/view: local Lipschitz control from `ConvexOn.locallyLipschitzOn_interior` and the
  finite-dimensional supporting-hyperplane bridge from `Theorem_3_1_4_2`.

The previous file rebuilt local copies of the effective domain, the subgradient predicate, and the
subdifferential set, even though those notions are already owned upstream in `Definition_3_1_5`.
The neighboring source-facing subdifferential files already live on the intrinsic real
inner-product-space owner layer rather than a local `EuclideanSpace ℝ (Fin n)` model. This
refinement aligns Theorem 3.1.15 with that owner layer, keeping the same mathematics while
deleting the remaining concrete-model wrapper.
-/

/-- Theorem 3.1.15, generalized from the textbook Euclidean setting: if an `ℝ ∪ {+∞}`-valued
convex function on a finite-dimensional real inner-product space is finite at an interior point
`x₀` of its effective domain, then the subdifferential `∂f(x₀)` is nonempty and bounded. The
textbook statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: local convex regularity gives a neighborhood of `x₀` on which the finite-value
-- representative `withTopRealPart f` is Lipschitz. A supporting hyperplane to the epigraph at
-- `(f x₀, x₀)` then yields one subgradient, and the same local Lipschitz bound controls the norm
-- of every subgradient.
theorem subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    (∂ f(x0)).Nonempty ∧ Bornology.IsBounded (∂ f(x0)) := by
  -- First produce one subgradient by supporting a local closed-ball epigraph.
  have hnonempty : (∂ f(x0)).Nonempty :=
    subdifferential_nonempty_of_convexOn_of_mem_interior hf hx0
  -- Then use the local Lipschitz ball from Theorem 3.1.11 to bound every subgradient uniformly.
  obtain ⟨r, hr, hball, K, hK⟩ :=
    exists_lipschitz_ball_subset_effectiveDomain_of_mem_interior hf hx0
  refine ⟨hnonempty, (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : E) K)).subset ?_⟩
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_subdifferential_of_lipschitz_ball hr hball hK hg

end
