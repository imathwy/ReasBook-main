import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_7

-- Declarations for this item will be appended below by the statement pipeline.

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
