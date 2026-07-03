import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_26_7 (from Chap05) -/
noncomputable section

open Filter
open scoped Gradient

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 26.7 characterizes co-finiteness of a finite differentiable convex
  scalar-valued function by the cocompact divergence of the norm of its gradient, together with
  the equivalent
  sequence formulation `‖x i‖ → ∞ ⇒ ‖∇ f (x i)‖ → ∞`.
- `core/canonical`: the owner abstraction for co-finiteness is the chapter class
  `Function.IsCofinite`, and the canonical codomain bridge from finite scalar-valued functions to
  that owner is `Function.toWithTopBot` (with `toEReal` as the `ℝ`-specialized view). At the
  differential layer, the primitive canonical owner is the Fréchet derivative `fderiv`; the
  invariant filter expression of "at infinity" is `Filter.cocompact`.
- `bridge/view`: the source's sequence condition `‖x i‖ → ∞` is the normed-space presentation of
  tending to `cocompact`, and the source gradient norm `‖∇ f x‖` is the Euclidean bridge view of
  `‖fderiv ℝ f x‖` through `InnerProductSpace.toDual`.

Domain-style sampling used here:
- `Function.IsCofinite` from Text 13.3.1;
- `Function.toWithTopBot` from Definition 4.4;
- mathlib's `fderiv` owner together with the Euclidean `gradient` / `∇` bridge from
  `Analysis.Calculus.Gradient.Basic`;
- mathlib's `tendsto_norm_atTop_iff_cobounded` and `tendsto_norm_cocompact_atTop` normed-filter
  APIs.

Primitive data vs derived API:
- primitive source data are a finite scalar-valued function `f : E → 𝕜`, its global convexity
  `ConvexOn 𝕜 Set.univ f`, and differentiability `Differentiable 𝕜 f`;
- co-finiteness is not redefined here: it is the owner predicate
  `f.toWithTopBot.IsCofinite`;
- the cocompact `fderiv`-norm criterion is the main statement;
- the sequence formulation and the gradient-norm restatements are derived bridge API from that
  invariant cocompact owner statement.

Layer target: the owner statement is canonicalized to the derivative/pairing layer
(`NormedSpace` + `fderiv`) while keeping the source-facing real inner-product gradient theorem as
  a bridge specialization on proper real inner-product spaces; no concrete coordinate model such
as `EuclideanSpace ℝ (Fin n)` is used.
-/

section CocompactSeq

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

private theorem tendsto_cocompact_atTop_iff_forall_seq_tendsto_atTop
    {g : E → ℝ} :
    Tendsto g (cocompact E) atTop ↔
      ∀ x : ℕ → E,
        Tendsto (fun n ↦ ‖x n‖) atTop atTop →
          Tendsto (fun n ↦ g (x n)) atTop atTop := by
  letI : IsCountablyGenerated (cocompact E) := by
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
    infer_instance
  have hseq (x : ℕ → E) :
      Tendsto x atTop (cocompact E) ↔ Tendsto (fun n ↦ ‖x n‖) atTop atTop := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have htendsto :
      Tendsto g (cocompact E) atTop ↔
        ∀ x : ℕ → E, Tendsto x atTop (cocompact E) → Tendsto (g ∘ x) atTop atTop :=
    Filter.tendsto_iff_seq_tendsto
  refine htendsto.trans ?_
  constructor
  · intro hg x hx
    exact hg x ((hseq x).mpr hx)
  · intro hg x hx
    exact hg x ((hseq x).mp hx)

end CocompactSeq

section

variable {𝕜 : Type*} {E : Type*} [NormedLinearOrderedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]

/-- Lemma 26.7, owner-level cocompact form at the primitive derivative layer: a finite
differentiable convex scalar-valued function is co-finite if and only if the operator norm of
its Fréchet derivative tends to `+∞` along the cocompact filter. -/
theorem toWithTopBot_isCofinite_iff_tendsto_norm_fderiv_cocompact
    {f : E → 𝕜} (hf_convex : ConvexOn 𝕜 Set.univ f) (hf_diff : Differentiable 𝕜 f) :
    f.toWithTopBot.IsCofinite ↔
      Tendsto (fun x ↦ ‖fderiv 𝕜 f x‖) (cocompact E) atTop := by
  sorry

/-- Sequence companion at the primitive derivative layer: co-finiteness is equivalent to saying
that every sequence with `‖x n‖ → +∞` has `‖fderiv 𝕜 f (x n)‖ → +∞`. -/
theorem toWithTopBot_isCofinite_iff_forall_tendsto_norm_fderiv_atTop
    {f : E → 𝕜} (hf_convex : ConvexOn 𝕜 Set.univ f) (hf_diff : Differentiable 𝕜 f) :
    f.toWithTopBot.IsCofinite ↔
      ∀ x : ℕ → E,
        Tendsto (fun n ↦ ‖x n‖) atTop atTop →
          Tendsto (fun n ↦ ‖fderiv 𝕜 f (x n)‖) atTop atTop := by
  rw [toWithTopBot_isCofinite_iff_tendsto_norm_fderiv_cocompact hf_convex hf_diff]
  exact tendsto_cocompact_atTop_iff_forall_seq_tendsto_atTop

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

private theorem norm_gradient_eq_norm_fderiv {f : E → ℝ} :
    (fun x ↦ ‖∇ f x‖) = fun x ↦ ‖fderiv ℝ f x‖ := by
  funext x
  simp [gradient]

private theorem norm_gradient_eq_norm_fderiv_apply {f : E → ℝ} (x : E) :
    ‖∇ f x‖ = ‖fderiv ℝ f x‖ := by
  simpa using congrArg (fun g : E → ℝ => g x) (norm_gradient_eq_norm_fderiv (f := f))

/-- Lemma 26.7, source-facing Euclidean bridge: in proper real inner-product spaces,
the co-finiteness criterion can be written with the norm of the gradient. -/
theorem toWithTopBot_isCofinite_iff_tendsto_norm_gradient_cocompact
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f) :
    f.toWithTopBot.IsCofinite ↔
      Tendsto (fun x ↦ ‖∇ f x‖) (cocompact E) atTop := by
  simpa only [norm_gradient_eq_norm_fderiv (f := f)] using
    (toWithTopBot_isCofinite_iff_tendsto_norm_fderiv_cocompact
      (f := f) hf_convex hf_diff)

/-- Sequence companion of the Euclidean bridge form: in proper real inner-product
spaces, Lemma 26.7 is equivalently the source statement
`‖x n‖ → +∞ ⇒ ‖∇ f (x n)‖ → +∞`. -/
theorem toWithTopBot_isCofinite_iff_forall_tendsto_norm_gradient_atTop
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f) :
    f.toWithTopBot.IsCofinite ↔
      ∀ x : ℕ → E,
        Tendsto (fun n ↦ ‖x n‖) atTop atTop →
          Tendsto (fun n ↦ ‖∇ f (x n)‖) atTop atTop := by
  constructor
  · intro hcof x hx
    have hfd :
        Tendsto (fun n ↦ ‖fderiv ℝ f (x n)‖) atTop atTop :=
      (toWithTopBot_isCofinite_iff_forall_tendsto_norm_fderiv_atTop
        (f := f) hf_convex hf_diff).1 hcof x hx
    simpa [norm_gradient_eq_norm_fderiv_apply (f := f)] using hfd
  · intro hcof
    refine (toWithTopBot_isCofinite_iff_forall_tendsto_norm_fderiv_atTop
      (f := f) hf_convex hf_diff).2 ?_
    intro x hx
    have hgrad :
        Tendsto (fun n ↦ ‖∇ f (x n)‖) atTop atTop := hcof x hx
    simpa [norm_gradient_eq_norm_fderiv_apply (f := f)] using hgrad

end

end Function

end
