import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter

universe u v

namespace Function

section

open scoped Topology

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [CompleteSpace 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.7 is recorded below in the Euclidean gradient bridge: on an open
  convex set `C`, pointwise convergence of a sequence of finite differentiable convex functions to
  a finite differentiable limit forces uniform convergence of gradients on every closed bounded
  subset of `C`.
- `core/canonical`: the mathematically intrinsic owner is Fréchet differentiation,
  `fderiv 𝕜`, not Euclidean gradient. The canonical theorems in this file are therefore the
  `fderiv` convergence owners below, stated at scalar-generic `𝕜`.
- `bridge/view`: `∇` is obtained from `fderiv` by the Riesz map in real inner-product spaces, so
  the gradient theorems are thin bridge views derived from the canonical `fderiv` owner.

Domain-style sampling used here:
- `ConvexOn 𝕜 C`;
- `DifferentiableOn 𝕜 _ C`;
- `TendstoLocallyUniformlyOn` as the canonical convergence owner;
- `fderiv 𝕜` as the intrinsic derivative owner;
- compact-subset specialization via
  `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`.

Primitive data vs derived API:
- primitive source data: the open set `C`, the differentiable limit function `f`, the convex
  differentiable sequence `fSeq`, and pointwise convergence `fSeq i x → f x` on `C`;
- derived API: locally uniform convergence of `fderiv`, then uniform convergence of `fderiv` on
  compact subsets, and finally the Euclidean gradient closed-bounded specialization in the bridge
  section.

Layer target: the canonical owner-level API in this item is `fderiv`; the textbook gradient
surface remains available as a bridge.
-/

variable {C : Set E} (hC_open : IsOpen C)
variable {f : E → 𝕜} (hf_diff : DifferentiableOn 𝕜 f C)
variable {fSeq : ℕ → E → 𝕜}
variable (hfSeq_convex : ∀ i, ConvexOn 𝕜 C (fSeq i))
variable (hfSeq_diff : ∀ i, DifferentiableOn 𝕜 (fSeq i) C)

include hC_open hf_diff hfSeq_convex hfSeq_diff

-- Proof sketch: combine Chapter 10 local-uniform convex convergence with Chapter 25 directional
-- differentiability/continuity tools at the intrinsic Fréchet-derivative owner level.
/-- Canonical owner-level companion to Theorem 25.7: on an open convex set `C`, locally uniform
convergence of finite differentiable convex functions to a finite differentiable limit function
forces locally uniform convergence of the Fréchet-derivative map on `C`; convexity of the limit is
automatic. -/
theorem tendstoLocallyUniformlyOn_fderiv_of_tendstoLocallyUniformlyOn_on_open
    (hloc : TendstoLocallyUniformlyOn fSeq f atTop C) :
    TendstoLocallyUniformlyOn (fun i x ↦ fderiv 𝕜 (fSeq i) x) (fderiv 𝕜 f) atTop C := sorry

-- Proof sketch: restrict locally uniform `fderiv` convergence to a compact subset and use the
-- compact/local-uniform equivalence.
/-- Compact-subset specialization of the canonical owner theorem: under locally uniform convergence
of function values on `C`, the Fréchet derivatives converge uniformly on each compact subset
`S ⊆ C`. -/
theorem tendstoUniformlyOn_fderiv_on_compact_of_tendstoLocallyUniformlyOn_on_open
    (hloc : TendstoLocallyUniformlyOn fSeq f atTop C)
    {S : Set E} (hS_compact : IsCompact S) (hS_subset : S ⊆ C) :
    TendstoUniformlyOn (fun i x ↦ fderiv 𝕜 (fSeq i) x) (fderiv 𝕜 f) atTop S := by
  have hfderiv_loc :
      TendstoLocallyUniformlyOn (fun i x ↦ fderiv 𝕜 (fSeq i) x) (fderiv 𝕜 f) atTop S :=
    (tendstoLocallyUniformlyOn_fderiv_of_tendstoLocallyUniformlyOn_on_open
      hC_open hf_diff hfSeq_convex hfSeq_diff hloc).mono hS_subset
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS_compact).1 hfderiv_loc

-- Proof sketch: first upgrade pointwise convergence on `C` to the canonical local-uniform
-- convergence owner on `C`, then apply the canonical `fderiv` compact-subset theorem above.
/-- Pointwise-limit form of the canonical owner theorem: on an open convex set `C`, if
`fSeq i → f` pointwise on `C`, then Fréchet derivatives converge uniformly on each compact
subset `S ⊆ C`; convexity of the limit is automatic. -/
theorem tendstoUniformlyOn_fderiv_on_compact_of_pointwiseLimit_on_open
    (hlimit : ∀ z ∈ C, Tendsto (fun i ↦ fSeq i z) atTop (𝓝 (f z)))
    {S : Set E} (hS_compact : IsCompact S) (hS_subset : S ⊆ C) :
    TendstoUniformlyOn (fun i x ↦ fderiv 𝕜 (fSeq i) x) (fderiv 𝕜 f) atTop S := by
  have hC_ri : IsRelativelyOpen 𝕜 C := hC_open.isRelativelyOpen
  have hloc :
      TendstoLocallyUniformlyOn fSeq f atTop C :=
    (convexOn_and_tendstoLocallyUniformlyOn_of_pointwiseLimit
      fSeq hC_ri hfSeq_convex hlimit).2
  exact
    tendstoUniformlyOn_fderiv_on_compact_of_tendstoLocallyUniformlyOn_on_open
      hC_open hf_diff hfSeq_convex hfSeq_diff hloc hS_compact hS_subset

omit hC_open hf_diff hfSeq_convex hfSeq_diff

end

section

open scoped Gradient Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {C : Set E} (hC_open : IsOpen C)
variable {f : E → ℝ} (hf_diff : DifferentiableOn ℝ f C)
variable {fSeq : ℕ → E → ℝ}
variable (hfSeq_convex : ∀ i, ConvexOn ℝ C (fSeq i))
variable (hfSeq_diff : ∀ i, DifferentiableOn ℝ (fSeq i) C)

include hC_open hf_diff hfSeq_convex hfSeq_diff

-- Proof sketch: specialize the canonical `fderiv` owner theorem to `𝕜 = ℝ`, then post-compose
-- with the inverse Riesz map `(InnerProductSpace.toDual ℝ E).symm` and simplify using
-- `gradient = (toDual.symm ∘ fderiv)`.
/-- Euclidean bridge view of the canonical `fderiv` theorem: locally uniform convergence of values
on an open convex set forces locally uniform convergence of gradients. -/
theorem tendstoLocallyUniformlyOn_gradient_of_tendstoLocallyUniformlyOn_on_open
    (hloc : TendstoLocallyUniformlyOn fSeq f atTop C) :
    TendstoLocallyUniformlyOn (fun i x ↦ ∇ (fSeq i) x) (∇ f) atTop C := by
  simpa [gradient] using
    ((InnerProductSpace.toDual ℝ E).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn
      (tendstoLocallyUniformlyOn_fderiv_of_tendstoLocallyUniformlyOn_on_open
        hC_open hf_diff hfSeq_convex hfSeq_diff hloc))

-- Proof sketch: restrict the gradient locally-uniform convergence to the closed bounded subset
-- `S`. In finite-dimensional Euclidean space, `S` is compact by Heine-Borel, so locally uniform
-- convergence on `S` is uniform convergence on `S`.
/-- Closed-bounded-set bridge form of Theorem 25.7: under locally uniform convergence of function
values on `C`, gradients converge uniformly on every closed bounded subset `S ⊆ C`. -/
theorem tendstoUniformlyOn_gradient_on_closed_bounded_of_tendstoLocallyUniformlyOn_on_open
    (hloc : TendstoLocallyUniformlyOn fSeq f atTop C)
    {S : Set E} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S) (hS_subset : S ⊆ C) :
    TendstoUniformlyOn (fun i x ↦ ∇ (fSeq i) x) (∇ f) atTop S := by
  have hgrad_loc :
      TendstoLocallyUniformlyOn (fun i x ↦ ∇ (fSeq i) x) (∇ f) atTop S :=
    (tendstoLocallyUniformlyOn_gradient_of_tendstoLocallyUniformlyOn_on_open
      hC_open hf_diff hfSeq_convex hfSeq_diff hloc).mono hS_subset
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS_compact).1 hgrad_loc

-- Proof sketch: first apply the canonical pointwise-to-`fderiv` theorem on compact subsets, then
-- specialize to `𝕜 = ℝ` and post-compose with the inverse Riesz map to recover gradients.
/-- Theorem 25.7 (Euclidean bridge form): on an open convex set `C`, if a sequence of finite
 differentiable convex functions converges pointwise to a finite differentiable limit function,
then the gradients converge uniformly on every closed bounded subset of `C`; convexity of the
limit is automatic. -/
theorem tendstoUniformlyOn_gradient_on_closed_bounded_of_pointwiseLimit_on_open
    (hlimit : ∀ z ∈ C, Tendsto (fun i ↦ fSeq i z) atTop (𝓝 (f z)))
    {S : Set E} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S) (hS_subset : S ⊆ C) :
    TendstoUniformlyOn (fun i x ↦ ∇ (fSeq i) x) (∇ f) atTop S := by
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hfderiv_unif :
      TendstoUniformlyOn (fun i x ↦ fderiv ℝ (fSeq i) x) (fderiv ℝ f) atTop S :=
    tendstoUniformlyOn_fderiv_on_compact_of_pointwiseLimit_on_open
      hC_open hf_diff hfSeq_convex hfSeq_diff hlimit hS_compact hS_subset
  simpa [gradient] using
    ((InnerProductSpace.toDual ℝ E).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn
      hfderiv_unif)

omit hC_open hf_diff hfSeq_convex hfSeq_diff

end

end Function
