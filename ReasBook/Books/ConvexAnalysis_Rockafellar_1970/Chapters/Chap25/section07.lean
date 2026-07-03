import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_25_7_1 (from Chap05) -/
noncomputable section

open Filter
open scoped Topology

section

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 25.7.1 is the one-dimensional interval form of Theorem 25.7. It
  asserts pointwise convergence of ordinary derivatives on an open interval, and then uniform
  convergence on each closed bounded subinterval.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.tendstoUniformlyOn_fderiv_on_compact_of_pointwiseLimit_on_open`,
  `Function.tendstoLocallyUniformlyOn_fderiv_of_tendstoLocallyUniformlyOn_on_open`,
  `ConvexOn ℝ I`, `DifferentiableOn ℝ _ I`, and the scalar bridge
  `fderiv_apply_one_eq_deriv`.
- `bridge/view`: this file is the one-dimensional bridge from the canonical Fréchet-derivative
  owner to ordinary derivatives via evaluation at `1`.

Domain-style sampling used here:
- `Function.tendstoUniformlyOn_fderiv_on_compact_of_pointwiseLimit_on_open` from Theorem 25.7;
- `Function.tendstoLocallyUniformlyOn_fderiv_of_tendstoLocallyUniformlyOn_on_open` from
  Theorem 25.7;
- `fderiv_apply_one_eq_deriv` from mathlib's derivative API.

Primitive data vs derived API:
- primitive source data: an open set `I ⊆ ℝ`, a differentiable limit function `f : ℝ → ℝ`, a
  sequence `fSeq` of convex differentiable functions on `I`, and pointwise convergence
  `fSeq i t → f t` on `I`;
- derived API: pointwise convergence of the ordinary derivatives on `I`, and uniform convergence
  of those derivatives on compact subsets `J ⊆ I`, hence in particular on compact convex subsets,
  i.e. on closed bounded subintervals; convexity of the limit is inherited from Theorem 25.7.

Layer target: `bridge/view`, because the canonical higher-dimensional owner is already Theorem
25.7 at the `fderiv` level, and this item only translates that owner into the one-dimensional
derivative language of the text.
-/

variable {I : Set ℝ} (hI_open : IsOpen I)
variable {f : ℝ → ℝ} (hf_diff : DifferentiableOn ℝ f I)
variable {fSeq : ℕ → ℝ → ℝ}
variable (hfSeq_convex : ∀ i, ConvexOn ℝ I (fSeq i))
variable (hfSeq_diff : ∀ i, DifferentiableOn ℝ (fSeq i) I)
variable (hlimit : ∀ t ∈ I, Tendsto (fun i ↦ fSeq i t) atTop (𝓝 (f t)))

include hI_open hf_diff hfSeq_convex hfSeq_diff hlimit

-- Proof sketch: apply the canonical `fderiv` compact-subset theorem from Theorem 25.7 to the
-- singleton `{t}`. In one dimension, evaluating Fréchet derivatives at `1` gives ordinary
-- derivatives (`fderiv_apply_one_eq_deriv`), and uniform convergence on `{t}` is pointwise
-- convergence at `t`.
/-- Corollary 25.7.1 (1): on an open set `I ⊆ ℝ`, hence in particular on an open interval, if
convex differentiable functions `fSeq i` converge pointwise to a differentiable function `f`, then
the ordinary derivatives converge pointwise on `I`; convexity of `f` is automatic. -/
theorem tendsto_deriv_of_pointwiseLimit_on_open
    (t : ℝ) (ht : t ∈ I) :
    Tendsto (fun i ↦ deriv (fSeq i) t) atTop (𝓝 (deriv f t)) := by
  have hsingle :
      TendstoUniformlyOn (fun i y ↦ fderiv ℝ (fSeq i) y) (fderiv ℝ f) atTop ({t} : Set ℝ) :=
    tendstoUniformlyOn_fderiv_on_compact_of_pointwiseLimit_on_open
      hI_open hf_diff hfSeq_convex hfSeq_diff hlimit
      isCompact_singleton (Set.singleton_subset_iff.2 ht)
  have hfderiv : Tendsto (fun i ↦ fderiv ℝ (fSeq i) t) atTop (𝓝 (fderiv ℝ f t)) := by
    simpa using hsingle.tendsto_at (by simp)
  have happly :
      Tendsto (fun i ↦ (fderiv ℝ (fSeq i) t : ℝ →L[ℝ] ℝ) 1) atTop
        (𝓝 ((fderiv ℝ f t : ℝ →L[ℝ] ℝ) 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous.continuousAt.tendsto.comp hfderiv
  simpa [fderiv_apply_one_eq_deriv] using happly

-- Proof sketch: specialize the canonical `fderiv` compact-subset theorem of Theorem 25.7 to `J`,
-- then post-compose with evaluation at `1` to rewrite Fréchet derivatives as ordinary derivatives.
/-- Corollary 25.7.1 (2): on every compact subset `J ⊆ I`, hence in particular on every compact
convex subset, equivalently on every closed bounded subinterval of `I`, the derivatives
`deriv (fSeq i)` converge uniformly to `deriv f`; convexity of the limit is automatic. -/
theorem tendstoUniformlyOn_deriv_of_pointwiseLimit_on_compact
    {J : Set ℝ} (hJ_compact : IsCompact J) (hJI : J ⊆ I) :
    TendstoUniformlyOn (fun i t ↦ deriv (fSeq i) t) (deriv f) atTop J := by
  have hfderiv :
      TendstoUniformlyOn (fun i t ↦ fderiv ℝ (fSeq i) t) (fderiv ℝ f) atTop J :=
    tendstoUniformlyOn_fderiv_on_compact_of_pointwiseLimit_on_open
      hI_open hf_diff hfSeq_convex hfSeq_diff hlimit hJ_compact hJI
  have happly :
      TendstoUniformlyOn
        (fun i t ↦ (fderiv ℝ (fSeq i) t : ℝ →L[ℝ] ℝ) 1)
        (fun t ↦ (fderiv ℝ f t : ℝ →L[ℝ] ℝ) 1)
        atTop J :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).uniformContinuous.comp_tendstoUniformlyOn hfderiv
  simpa [fderiv_apply_one_eq_deriv] using happly

end Function

end

/-! ### Theorem_25_7 (from Chap05) -/
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
