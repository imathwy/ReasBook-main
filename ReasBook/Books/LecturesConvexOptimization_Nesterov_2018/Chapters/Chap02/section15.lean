import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_15 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strong convexity on convex subsets of a complete real inner-product space,
expressed through intrinsic Loewner lower bounds on the Hessian operator.

Sampled owner-style declarations before refining this file:
* project `hessian` in `Definition_1_4_16`
* mathlib `StrongConvexOn`
* project `strongConvexOnWith_normSeminorm_iff` in `Definition_2_14`
* project `interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound` in
  `Theorem_2_12`

Best owner abstraction on the intrinsic Hilbert-space layer:
* `StrongConvexOn Q μ f`

Primitive data:
* the convex set `Q` with nonempty interior
* the parameter `μ > 0`
* continuity of `f` on `Q`
* `C²` regularity of `f` on `interior Q`

Derived API:
* the pointwise Loewner lower bound `μ • id ℝ E ≤ hessian f x`, obtained by rewriting the
  quadratic-form criterion already owned by `Theorem_2_12`
* the ambient-norm bridge back to the chapter source-facing owner
  `StrongConvexOnWith (normSeminorm ℝ E) μ Q f`

Source/core/bridge triage:
* source-facing: the intrinsic Hessian characterization of strong convexity
* core/canonical: `StrongConvexOn Q μ f`
* bridge/view: the comparison with `StrongConvexOnWith (normSeminorm ℝ E) μ Q f`
-/

section

variable {μ : ℝ} {Q : Set E} {f : E → ℝ}
variable (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
variable (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q))

-- Proof sketch: rewrite `μ • id ≤ H` as nonnegativity of `H - μ • id` using the Loewner order
-- from `ContinuousLinearMap.le_def`, then use `ContinuousLinearMap.nonneg_iff_isPositive` and the
-- self-adjointness of the Hessian of a `C²` real function to identify positivity of
-- `H - μ • id` with nonnegativity of its quadratic form. Combine this intrinsic operator
-- reformulation with `interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound`
-- and the ambient-norm bridge `strongConvexOnWith_normSeminorm_iff`.

/-- Helper for Definition 2.15: at an interior point, the Loewner lower bound on the Hessian is
equivalent to the corresponding quadratic-form inequality. -/
lemma hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
    (hμ : 0 < μ) (hf_C2 : ContDiffOn ℝ 2 f (interior Q))
    {x : E} (hx : x ∈ interior Q) :
    μ • (1 : E →L[ℝ] E) ≤ hessian f x ↔
      ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x h) h := by
  -- Rewrite the order relation as positivity of the shifted Hessian operator.
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
  constructor
  · intro hshift h
    -- The quadratic form of the shifted operator is exactly the Hessian form minus `μ ‖h‖²`.
    have hh : 0 ≤ inner ℝ ((hessian f x - μ • (1 : E →L[ℝ] E)) h) h := hshift.2 h
    simpa [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_assoc, mul_left_comm,
      mul_comm] using hh
  · intro hquad
    -- Symmetry comes from the `C²` Hessian symmetry and the identity operator is symmetric.
    refine ⟨?_, ?_⟩
    · exact
        (fderiv_gradient_isSymmetric_of_contDiffAt
          (hf_C2.contDiffAt (isOpen_interior.mem_nhds hx))).sub
          (ContinuousLinearMap.isPositive_one.smul_of_nonneg hμ.le).isSymmetric
    · intro h
      -- The assumed quadratic-form bound rewrites directly to positivity of `∇²f(x) - μ id`.
      have hh : μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x h) h := hquad h
      simpa [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_assoc,
        mul_left_comm, mul_comm] using sub_nonneg.mpr hh

/-- Helper for Definition 2.15: strong convexity on `Q` is equivalent to the interior Hessian
quadratic-form lower bound. -/
lemma strongConvexOn_iff_hessian_quadratic_form_lower_bound
    (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
    (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    StrongConvexOn Q μ f ↔
      ∀ x ∈ interior Q, ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x h) h := by
  constructor
  · intro hstrong
    -- Strong convexity gives the corrected tangent inequality at every interior base point.
    have hlower :
        ∀ x : E, x ∈ interior Q → ∀ y : E, y ∈ Q →
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      intro x hx y hy
      have hxQ : x ∈ Q := interior_subset hx
      have hC2x : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (isOpen_interior.mem_nhds hx)
      have hdiffx : DifferentiableAt ℝ f x :=
        (hC2x.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt one_ne_zero
      have hgradx : HasGradientAt f (∇ f x) x := hdiffx.hasGradientAt
      exact
        StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
          (hf := hstrong) hxQ hy hgradx
    -- Theorem 2.12 converts the lower tangent inequality into the Hessian lower bound.
    simpa using
      (interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound
        (p := normSeminorm ℝ E) (Q := Q) (f := f) μ hQ_conv hf_cont hf_C2).1 hlower
  · intro hquad
    -- First recover strong convexity on the open owner domain `interior Q`.
    have hstrongWith_int : StrongConvexOnWith (normSeminorm ℝ E) μ (interior Q) f := by
      refine
        (StrongConvexOnWith.iff_hessian_quadratic_form_lower_bound
          (p := normSeminorm ℝ E) (U := interior Q) (f := f)
          hμ isOpen_interior hQ_conv.interior hf_C2).2 ?_
      simpa using hquad
    have hstrong_int : StrongConvexOn (interior Q) μ f := by
      exact (strongConvexOnWith_normSeminorm_iff.mp hstrongWith_int).2
    rcases hQ_int with ⟨x₀, hx₀⟩
    have hx₀Q : x₀ ∈ Q := interior_subset hx₀
    refine ⟨hQ_conv, ?_⟩
    intro x hx y hy a b ha hb hab
    let xt : ℝ → E := fun t ↦ (1 - t) • x + t • x₀
    let yt : ℝ → E := fun t ↦ (1 - t) • y + t • x₀
    let zt : ℝ → E := fun t ↦ a • xt t + b • yt t
    let corr : ℝ → ℝ := fun t ↦ ((a * b) * (μ / 2)) * ‖xt t - yt t‖ ^ (2 : ℕ)
    let ψ : ℝ → ℝ := fun t ↦ a * f (xt t) + b * f (yt t) - corr t - f (zt t)
    have hxtQ : Set.MapsTo xt (Set.Icc (0 : ℝ) 1) Q := by
      intro t ht
      exact hQ_conv hx hx₀Q (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    have hytQ : Set.MapsTo yt (Set.Icc (0 : ℝ) 1) Q := by
      intro t ht
      exact hQ_conv hy hx₀Q (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    have hztQ : Set.MapsTo zt (Set.Icc (0 : ℝ) 1) Q := by
      intro t ht
      exact hQ_conv (hxtQ ht) (hytQ ht) ha hb hab
    have hxt_int : ∀ t ∈ Set.Ioc (0 : ℝ) 1, xt t ∈ interior Q := by
      intro t ht
      exact hQ_conv.combo_self_interior_mem_interior hx hx₀ (sub_nonneg.mpr ht.2) ht.1
        (by linarith)
    have hyt_int : ∀ t ∈ Set.Ioc (0 : ℝ) 1, yt t ∈ interior Q := by
      intro t ht
      exact hQ_conv.combo_self_interior_mem_interior hy hx₀ (sub_nonneg.mpr ht.2) ht.1
        (by linarith)
    have hzt_int : ∀ t ∈ Set.Ioc (0 : ℝ) 1, zt t ∈ interior Q := by
      intro t ht
      exact hstrong_int.1 (hxt_int t ht) (hyt_int t ht) ha hb hab
    have hxt_cont : Continuous xt := by
      simpa [xt] using
        ((continuous_const.sub continuous_id).smul continuous_const).add
          (continuous_id.smul continuous_const)
    have hyt_cont : Continuous yt := by
      simpa [yt] using
        ((continuous_const.sub continuous_id).smul continuous_const).add
          (continuous_id.smul continuous_const)
    have hzt_cont : Continuous zt := by
      simpa [zt] using (continuous_const.smul hxt_cont).add (continuous_const.smul hyt_cont)
    have hcorr_cont : Continuous corr := by
      simpa [corr] using (((hxt_cont.sub hyt_cont).norm.pow (2 : ℕ)).const_mul
        ((a * b) * (μ / 2)))
    have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
      have hfx_cont : ContinuousOn (fun t ↦ f (xt t)) (Set.Icc (0 : ℝ) 1) :=
        hf_cont.comp hxt_cont.continuousOn hxtQ
      have hfy_cont : ContinuousOn (fun t ↦ f (yt t)) (Set.Icc (0 : ℝ) 1) :=
        hf_cont.comp hyt_cont.continuousOn hytQ
      have hfz_cont : ContinuousOn (fun t ↦ f (zt t)) (Set.Icc (0 : ℝ) 1) :=
        hf_cont.comp hzt_cont.continuousOn hztQ
      -- The boundary extension is a one-parameter limit of the interior strong-convexity gap.
      simpa [ψ] using
        (((hfx_cont.const_mul a).add (hfy_cont.const_mul b)).sub hcorr_cont.continuousOn).sub
          hfz_cont
    have hψ_nonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ ψ t := by
      intro t ht
      have hstrong_t :
          f (zt t) ≤
            a * f (xt t) + b * f (yt t) -
              a * b * ((μ / 2) * ‖xt t - yt t‖ ^ (2 : ℕ)) :=
        hstrong_int.2 (hxt_int t ht) (hyt_int t ht) ha hb hab
      have hstrong_t' : f (zt t) ≤ a * f (xt t) + b * f (yt t) - corr t := by
        simpa [corr, mul_assoc, mul_left_comm, mul_comm] using hstrong_t
      exact sub_nonneg.mpr hstrong_t'
    have hψ_tendsto :
        Filter.Tendsto ψ (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1)) (nhds (ψ 0)) := by
      have hcont0 : ContinuousWithinAt ψ (Set.Icc (0 : ℝ) 1) 0 :=
        hψ_cont.continuousWithinAt (by simp)
      exact tendsto_nhdsWithin_mono_left (f := ψ) (a := 0)
        (s := Set.Ioc (0 : ℝ) 1) (t := Set.Icc (0 : ℝ) 1)
        (by intro t ht; exact ⟨ht.1.le, ht.2⟩) hcont0.tendsto
    have hneBot : Filter.NeBot (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1)) := by
      have hclosure : (0 : ℝ) ∈ closure (Set.Ioc (0 : ℝ) 1) := by
        rw [closure_Ioc zero_ne_one]
        simp
      exact mem_closure_iff_nhdsWithin_neBot.mp hclosure
    have hψ0_nonneg : 0 ≤ ψ 0 := by
      letI := hneBot
      refine ge_of_tendsto hψ_tendsto ?_
      exact Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => hψ_nonneg t ht)
    -- Evaluate the limiting inequality at `t = 0` to recover the target segment inequality.
    have hψ0_le :
        f (zt 0) ≤ a * f (xt 0) + b * f (yt 0) - corr 0 := by
      exact sub_nonneg.mp hψ0_nonneg
    simpa [xt, yt, zt, corr, mul_assoc, mul_left_comm, mul_comm] using hψ0_le

/-- Definition 2.15: on a convex set with nonempty interior in a complete real inner-product
space, the intrinsic Hessian lower bound `μ • id ≤ ∇² f(x)` on `interior Q` is exactly mathlib's
canonical strong-convexity predicate, under the standard `μ > 0`, continuity, and `C²`
hypotheses. -/
theorem strongConvexOn_iff_hessian_lower_bound
    (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
    (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    StrongConvexOn Q μ f ↔
      ∀ x ∈ interior Q, μ • (1 : E →L[ℝ] E) ≤ hessian f x := by
  -- Reduce the operator-valued statement to the scalar quadratic-form criterion.
  rw [strongConvexOn_iff_hessian_quadratic_form_lower_bound hμ hQ_conv hQ_int hf_cont hf_C2]
  constructor
  · intro hquad x hx
    -- The pointwise Hessian lower bound is exactly the quadratic-form bound at each interior point.
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hμ hf_C2 hx).2 (hquad x hx)
  · intro hbound x hx h
    -- Conversely, the Loewner bound immediately implies the scalar bound on every direction.
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hμ hf_C2 hx).1 (hbound x hx) h

/-- Companion bridge: the same Hessian lower bound can be read through the chapter owner
predicate `StrongConvexOnWith`, specialized to the ambient norm. -/
theorem strongConvexOnWith_normSeminorm_iff_hessian_lower_bound
    (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
    (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    StrongConvexOnWith (normSeminorm ℝ E) μ Q f ↔
      ∀ x ∈ interior Q, μ • (1 : E →L[ℝ] E) ≤ hessian f x := by
  have h :=
    strongConvexOn_iff_hessian_lower_bound hμ hQ_conv hQ_int hf_cont hf_C2
  simpa [strongConvexOnWith_normSeminorm_iff, hμ] using h

end

/-! ### Lemma_2_15 (from Chap02) -/
open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Lemma 2.15 lies in the projection / smooth-convex domain of real inner-product spaces.

Sampled owner-style declarations:
* `Metric.infDist_closure` and `Metric.infDist_empty` in mathlib, showing that
  `Q.halfSquaredDistance` depends only on `closure Q` and becomes the zero function on `∅`;
* `IsProjectionPointOn Q x p` in `Chap07/Definition_7_3`, the project owner predicate for
  nearest-point geometry;
* `euclideanProjection` and `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the
  chosen projection map and its bridge back to the owner predicate;
* `euclideanProjection_nonexpansive` in `Theorem_2_34`, the canonical map-level `1`-Lipschitz
  control on the chosen projection;
* `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` in `Theorem_2_5`, the owner predicate for whole-space `C¹`
  convex objectives with `L`-Lipschitz gradient.

Source/core/bridge triage:
* source-facing: the textbook gradient identity for the half squared distance and the resulting
  `1`-smooth convexity statement; the Euclidean `ℝⁿ` version is the specialization
  `E = EuclideanSpace ℝ (Fin n)`;
* core/canonical: `IsProjectionPointOn Q x p` on the geometric side and
  `Q.halfSquaredDistance ∈ 𝓕[1, normSeminorm ℝ E]¹¹` on the objective side;
* bridge/view: the specialization from an arbitrary projection point to the chosen map
  `euclideanProjection`.

Primitive data:
* the set `Q`, base point `x`, projection point `p`, and convexity / closedness / nonemptiness
  hypotheses exactly when they affect existence of the chosen projection map;
* for the owner-level gradient identity, only the convexity of `Q` and the witness
  `IsProjectionPointOn Q x p`, with completeness entering only through the ambient gradient API;
* for the final smoothness statement, the public mathematical input is `Convex ℝ Q` together with
  the finite-dimensional ambient owner required by `𝓕[1, normSeminorm ℝ E]¹¹`, while closure and
  emptiness reductions come canonically from `Metric.infDist`.

Derived API:
* the gradient formula at an arbitrary owner-level projection point;
* the smooth-objective packaging in `ConvexC1SeminormSmooth`.

Accordingly, the main geometric theorem remains owner-based in the namespace
`IsProjectionPointOn`, and the smoothness result is stated directly in the chapter owner
abstraction. The specialization to the chosen projection map is already a one-line downstream
bridge via `euclideanProjection_isProjectionPointOn`, so no parallel local wrapper is kept here.
-/

namespace IsProjectionPointOn

section

variable [CompleteSpace E]

/-- Helper for Lemma 2.15: at a projection point `p` of `x`, the half squared distance lies above
its affine model with slope `x - p`, and the tangent error is at most `‖z - x‖² / 2`. -/
  lemma halfSquaredDistance_tangent_bounds
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x p z : E} (hp : IsProjectionPointOn Q x p) :
    0 ≤ Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) ∧
      Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) ≤
        (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
  let Qc : Set E := closure Q
  have hp_mem_closure : p ∈ Qc := by
    simpa [Qc] using (subset_closure hp.1)
  have hQc_convex : Convex ℝ Qc := hQ_convex.closure
  have hQc_nonempty : Qc.Nonempty := ⟨p, hp_mem_closure⟩
  let zproj : E := euclideanProjection Qc hQc_nonempty isClosed_closure hQc_convex z
  have hzproj : IsProjectionPointOn Qc z zproj :=
    euclideanProjection_isProjectionPointOn Qc hQc_nonempty isClosed_closure hQc_convex z
  have hp_closure : IsProjectionPointOn Qc x p := by
    refine ⟨hp_mem_closure, ?_⟩
    simpa [Qc, Metric.infDist_closure] using hp.2
  have hz_eq :
      Q.halfSquaredDistance z = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) := by
    calc
      Q.halfSquaredDistance z = Qc.halfSquaredDistance z := by
        simp [Set.halfSquaredDistance, Qc, Metric.infDist_closure]
      _ = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) := hzproj.halfSquaredDistance_eq
  have hupper_half :
      Q.halfSquaredDistance z ≤ (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) := by
    have hdist : Metric.infDist z Q ≤ ‖z - p‖ := by
      simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := z) hp.1
    calc
      Q.halfSquaredDistance z = (1 / 2 : ℝ) * Metric.infDist z Q ^ (2 : ℕ) := rfl
      _ ≤ (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) := by
        nlinarith [Metric.infDist_nonneg (x := z) (s := Q), norm_nonneg (z - p), hdist]
  have hupper :
      Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) ≤
        (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
    have hz_sub : z - p = (z - x) + (x - p) := by
      abel_nf
    calc
      Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x)
          ≤ (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) -
              Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) := by
              linarith
      _ = (1 / 2 : ℝ) * ‖z - p‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖x - p‖ ^ (2 : ℕ) - inner ℝ (x - p) (z - x) := by
            rw [hp.halfSquaredDistance_eq]
      _ = (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        rw [hz_sub, norm_add_sq_real, real_inner_comm (z - x) (x - p)]
        ring
  have hproj_inner :
      0 ≤ inner ℝ (p - x) (zproj - p) :=
    hp_closure.inner_sub_nonneg hQc_convex hzproj.1
  have hlower :
      0 ≤ Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) := by
    let d : E := (z - x) - (zproj - p)
    have hz_sub :
        z - zproj = d + (x - p) := by
      dsimp [d]
      abel_nf
    have hzx :
        z - x = d + (zproj - p) := by
      dsimp [d]
      abel_nf
    calc
      0
          ≤ (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) +
              inner ℝ (p - x) (zproj - p) := by
              positivity
      _ = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) -
            (1 / 2 : ℝ) * ‖x - p‖ ^ (2 : ℕ) -
              inner ℝ (x - p) (z - x) := by
            calc
              (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) + inner ℝ (p - x) (zproj - p)
                  = (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) - inner ℝ (x - p) (zproj - p) := by
                      have hneg :
                          inner ℝ (p - x) (zproj - p) = -inner ℝ (x - p) (zproj - p) := by
                        simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
                      simpa [sub_eq_add_neg] using
                        congrArg (fun t : ℝ ↦ (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) + t) hneg
              _ = (1 / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) + inner ℝ (x - p) d - inner ℝ (x - p) (z - x) := by
                    rw [hzx, inner_add_right]
                    ring
              _ = (1 / 2 : ℝ) * ‖z - zproj‖ ^ (2 : ℕ) -
                    (1 / 2 : ℝ) * ‖x - p‖ ^ (2 : ℕ) -
                      inner ℝ (x - p) (z - x) := by
                    rw [hz_sub, norm_add_sq_real, real_inner_comm d (x - p)]
                    ring
      _ = Q.halfSquaredDistance z - Q.halfSquaredDistance x - inner ℝ (x - p) (z - x) := by
            rw [← hz_eq, hp.halfSquaredDistance_eq]
  exact ⟨hlower, hupper⟩

/-- Helper for Lemma 2.15: the tangent-error sandwich at a projection point makes the affine
remainder little-o of `‖y - x‖`. -/
lemma halfSquaredDistance_sub_affineApproximation_isLittleO
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x p : E} (hp : IsProjectionPointOn Q x p) :
    (fun y ↦
      Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x))) =o[nhds x]
      fun y ↦ ‖y - x‖ := by
  let r : E → ℝ :=
    fun y ↦ Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x))
  -- Convert the quadratic tangent bound into a local `O(‖y - x‖²)` estimate for the remainder.
  have hBigO :
      r =O[nhds x] fun y ↦ ‖y - x‖ ^ (2 : ℕ) := by
    refine Asymptotics.IsBigO.of_bound (1 / 2 : ℝ) ?_
    filter_upwards with y
    have hy := hp.halfSquaredDistance_tangent_bounds hQ_convex (z := y)
    calc
      ‖r y‖ = |Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x))| := by
        simp [r, Real.norm_eq_abs]
      _ = Q.halfSquaredDistance y - (Q.halfSquaredDistance x + inner ℝ (x - p) (y - x)) := by
        rw [abs_of_nonneg]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy.1
      _ ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
        have hy' := hy.2
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy'
      _ ≤ (1 / 2 : ℝ) * ‖‖y - x‖ ^ (2 : ℕ)‖ := by
        simp
  -- A quadratic remainder has zero Fréchet derivative, which is exactly the desired little-o
  -- statement after unpacking the zero linear part.
  have hDeriv0 : HasFDerivAt r (0 : E →L[ℝ] ℝ) x :=
    hBigO.hasFDerivAt (by norm_num : 1 < 2)
  simpa [r] using (hasFDerivAt_iff_isLittleO).mp hDeriv0

/-- The gradient of the half squared distance to a convex set equals the displacement from the base
point to its projection point onto that set. -/
-- Proof sketch: compare the first-order lower support inequality coming from the projection
-- optimality condition with the one-step upper bound obtained by testing the defining minimization
-- at a fixed projection point `p`. The matching lower and upper expansions identify the
-- directional derivative at `x` with the linear functional `d ↦ ⟪x - p, d⟫`, hence the gradient
-- is `x - p`.
theorem gradient_halfSquaredDistance
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x p : E} (hp : IsProjectionPointOn Q x p) :
    ∇ Q.halfSquaredDistance x = x - p := by
  -- Convert the projection-point tangent sandwich into the canonical little-o affine remainder.
  have hLittle := hp.halfSquaredDistance_sub_affineApproximation_isLittleO hQ_convex
  -- The Chapter 1 affine-approximation criterion then identifies the gradient exactly.
  exact ((hasGradientAt_iff_sub_affineApproximation_isLittleO).2 hLittle).gradient

end

end IsProjectionPointOn

section

variable [CompleteSpace E]

/-- Helper for Lemma 2.15: a projection selector on a convex set gives the global quadratic bound
for the affine model of the half squared distance. -/
lemma halfSquaredDistance_affineModel_bound_of_projection_selector
    {Q : Set E} (hQ_convex : Convex ℝ Q) {projQ : E → E}
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x)) :
    ∀ x y,
      |Q.halfSquaredDistance y - affineModelAt Q.halfSquaredDistance (fun z ↦ z - projQ z) x y| ≤
        (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  intro x y
  have hxy := (hproj x).halfSquaredDistance_tangent_bounds hQ_convex (z := y)
  -- The tangent error is already nonnegative, so its absolute value is the same quantity.
  refine abs_le.2 ?_
  constructor
  · have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by positivity
    have hmodel_nonneg :
        0 ≤
          Q.halfSquaredDistance y -
            affineModelAt Q.halfSquaredDistance (fun z ↦ z - projQ z) x y := by
      simpa [affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy.1
    linarith
  · simpa [affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy.2

/-- Helper for Lemma 2.15: every projection selector yields a global affine lower support for the
half squared distance. -/
lemma halfSquaredDistance_lower_support_of_projection_selector
    {Q : Set E} (hQ_convex : Convex ℝ Q) {projQ : E → E}
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x)) :
    ∀ x y,
      Q.halfSquaredDistance y ≥
        Q.halfSquaredDistance x + inner ℝ (x - projQ x) (y - x) := by
  intro x y
  -- The nonnegativity half of the tangent sandwich is exactly the lower-support inequality.
  have hxy := ((hproj x).halfSquaredDistance_tangent_bounds hQ_convex (z := y)).1
  linarith

end

section

variable [FiniteDimensional ℝ E]

/-- Lemma 2.15 on the canonical real Hilbert-space owner layer: the half squared distance to a
convex set is a convex `C¹` objective whose gradient is `1`-Lipschitz in the ambient norm. The
textbook Euclidean statement is the specialization to `ℝⁿ`. -/
-- Proof sketch: first reduce privately to the closed case using `Metric.infDist_closure`, and to
-- the empty-set case using `Metric.infDist_empty`, so the public statement depends only on
-- convexity. For the nonempty closed convex reduction, use the projection optimality inequality to
-- derive the global supporting-plane inequality for `Q.halfSquaredDistance`, giving
-- convexity. The companion gradient formula identifies the gradient with the displacement from
-- `x` to the chosen projection of `x` onto `closure Q`, and the projection map is nonexpansive,
-- so this gradient map is `1`-Lipschitz. The explicit gradient formula then upgrades the
-- differentiability statement to `ContDiff ℝ 1`.
theorem halfSquaredDistance_mem_F11
    (Q : Set E) (hQ_convex : Convex ℝ Q) :
    Q.halfSquaredDistance ∈ 𝓕[1, normSeminorm ℝ E]¹¹ := by
  by_cases hQ_empty : Q = ∅
  · have hzero :
      (fun _ : E ↦ (0 : ℝ)) ∈ 𝓕[1, normSeminorm ℝ E]¹¹ := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · -- The zero function is globally `C¹`.
        simpa [contDiffOn_univ] using (contDiff_const : ContDiff ℝ 1 (fun _ : E ↦ (0 : ℝ)))
      · -- The zero function is convex because every affine combination has the same value.
        simpa using convexOn_const (0 : ℝ) convex_univ
      · -- Its ambient gradient is the zero vector at every point.
        intro x hx
        simpa [gradient_const] using (hasGradientAt_const (x := x) (c := (0 : ℝ)))
      · -- The dual norm of the zero gradient difference vanishes identically.
        intro x hx y hy
        simp [Seminorm.dualNorm_normSeminorm_eq_norm]
    have hempty_fun : (∅ : Set E).halfSquaredDistance = fun _ : E ↦ (0 : ℝ) := by
      funext x
      simp [Set.halfSquaredDistance, Metric.infDist_empty]
    simpa [hQ_empty, hempty_fun] using hzero
  · have hQ_nonempty : Q.Nonempty := Set.nonempty_iff_ne_empty.mpr hQ_empty
    let Qc : Set E := closure Q
    have hQc_convex : Convex ℝ Qc := hQ_convex.closure
    have hQc_nonempty : Qc.Nonempty := hQ_nonempty.closure
    let projQ : E → E := euclideanProjection Qc hQc_nonempty isClosed_closure hQc_convex
    have hproj : ∀ x : E, IsProjectionPointOn Qc x (projQ x) :=
      fun x ↦ euclideanProjection_isProjectionPointOn Qc hQc_nonempty isClosed_closure hQc_convex x
    have hquad :
        ∀ x y,
          |Qc.halfSquaredDistance y -
              affineModelAt Qc.halfSquaredDistance (fun z ↦ z - projQ z) x y| ≤
            (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) :=
      halfSquaredDistance_affineModel_bound_of_projection_selector hQc_convex hproj
    have hContDiffAndLip :
        ContDiff ℝ 1 Qc.halfSquaredDistance ∧ LipschitzWith 1 (∇ Qc.halfSquaredDistance) :=
      mem_contDiffOne_withLipschitzGradient_of_sub_affineApproximation_norm_sq_bound
        (L := 1) (f := Qc.halfSquaredDistance) (g := fun z ↦ z - projQ z) hquad
    have hgrad_eq :
        ∇ Qc.halfSquaredDistance = fun z ↦ z - projQ z :=
      gradient_eq_of_sub_affineApproximation_norm_sq_bound
        (L := 1) (f := Qc.halfSquaredDistance) (g := fun z ↦ z - projQ z) hquad
    have hConvex :
        ConvexOn ℝ Set.univ Qc.halfSquaredDistance := by
      refine
        (convexOn_iff_lower_tangent_plane_of_contDiffOn
          (Q := Set.univ) (f := Qc.halfSquaredDistance) convex_univ
          (contDiffOn_univ.2 hContDiffAndLip.1)).2 ?_
      intro x hx y hy
      -- Rewrite the selector lower-support inequality into the canonical gradient form.
      have hgradx :
          HasGradientAt Qc.halfSquaredDistance (x - projQ x) x :=
        hasGradientAt_of_sub_affineApproximation_norm_sq_bound
          (L := 1) (f := Qc.halfSquaredDistance) (g := fun z ↦ z - projQ z) hquad x
      have hcanon :
          HasGradientAt Qc.halfSquaredDistance
            (gradientWithin Qc.halfSquaredDistance Set.univ x) x := by
        have hdiffWithin :
            DifferentiableWithinAt ℝ
              Qc.halfSquaredDistance Set.univ x :=
          ((hContDiffAndLip.1.contDiffAt).differentiableAt_one).differentiableWithinAt
        exact (hasGradientWithinAt_univ).mp hdiffWithin.hasGradientWithinAt
      have hgradWithin :
          gradientWithin Qc.halfSquaredDistance Set.univ x = x - projQ x :=
        hcanon.unique hgradx
      simpa [hgradWithin] using
        halfSquaredDistance_lower_support_of_projection_selector hQc_convex hproj x y
    have hQc_mem :
        Qc.halfSquaredDistance ∈ 𝓕[1, normSeminorm ℝ E]¹¹ := by
      refine ⟨⟨contDiffOn_univ.2 hContDiffAndLip.1, hConvex⟩, ?_, ?_⟩
      · -- The recovered `C¹` regularity gives the ambient gradient witness at every point.
        intro x hx
        exact ((hContDiffAndLip.1.contDiffAt).differentiableAt_one).hasGradientAt
      · -- The chapter owner wants the dual-norm Lipschitz estimate, which matches the usual norm
        -- in the `normSeminorm` specialization.
        intro x hx y hy
        simpa [Seminorm.dualNorm_normSeminorm_eq_norm] using hContDiffAndLip.2.norm_sub_le x y
    have hclosure_fun : Q.halfSquaredDistance = Qc.halfSquaredDistance := by
      funext x
      simp [Set.halfSquaredDistance, Qc, Metric.infDist_closure]
    simpa [hclosure_fun] using hQc_mem

end

end

/-! ### Proposition_2_15 (from Chap02) -/
open Set
open scoped Pointwise

/-!
Primary domain: convex-geometric subsets of `ℝ²` expressed as owner sets in `Set (ℝ × ℝ)`,
with Proposition 2.15 stated directly as pointwise set identities.

Relevant owner-style declarations sampled before refining this file:
* `reciprocalEpigraphOnPositiveRay`, the imported chapter owner set `Q`
* `nonnegativeFirstCoordinateRay`, the imported chapter owner set `ℝ_+^{1,2}`
* `Set.mem_add`, the canonical bridge for pointwise Minkowski addition of sets
* `Set.mem_sub`, the canonical bridge for pointwise set subtraction

Owner abstraction:
* the owner sets already live in `ReciprocalEpigraphOnPositiveRay.lean`, so this file now keeps
  only the source-facing set identities at the same `Set (ℝ × ℝ)` level.

Primitive data:
* none locally; both owner sets are imported

Derived API:
* the two source-facing set equalities of Proposition 2.15

Source/core/bridge triage:
* source-facing: the two set identities asserted in Proposition 2.15
* core/canonical: the imported owner sets as subsets of `ℝ × ℝ`, together with pointwise `Set`
  addition and subtraction
* bridge/view: the imported membership theorems
-/

/-- Proposition 2.15 (1): subtracting the nonnegative first-coordinate ray from `Q` gives exactly
the open upper half-plane `{x ∈ ℝ² | x₂ > 0}`. -/
-- Proof sketch: if `y = x - r` with `x ∈ Q` and `r` on the horizontal ray, then the second
-- coordinate is unchanged and remains positive because `x.1 > 0` and `x.2 ≥ 1 / x.1`. For the
-- reverse inclusion, given `y.2 > 0`, choose `x.1` large enough so that `1 / x.1 ≤ y.2` and
-- `y.1 ≤ x.1`, then set `x := (x.1, y.2)` and `r := x - y`.
theorem reciprocalEpigraphOnPositiveRay_sub_nonnegativeFirstCoordinateRay :
    reciprocalEpigraphOnPositiveRay - nonnegativeFirstCoordinateRay = {x : ℝ × ℝ | 0 < x.2} := by
  ext y
  constructor
  · rintro ⟨x, hx, r, hr, rfl⟩
    rcases (mem_reciprocalEpigraphOnPositiveRay_iff x).1 hx with ⟨hx1, hx2⟩
    rcases (mem_nonnegativeFirstCoordinateRay_iff r).1 hr with ⟨_, hr2⟩
    simpa [hr2] using lt_of_lt_of_le (one_div_pos.mpr hx1) hx2
  · intro hy
    let t : ℝ := max y.1 (1 / y.2)
    have ht_left : y.1 ≤ t := le_max_left _ _
    have ht_right : 1 / y.2 ≤ t := le_max_right _ _
    have ht_pos : 0 < t := lt_of_lt_of_le (one_div_pos.mpr hy) ht_right
    refine Set.mem_sub.2 ?_
    refine ⟨(t, y.2), ?_, (t - y.1, 0), ?_, by ext <;> simp [t]⟩
    · exact (mem_reciprocalEpigraphOnPositiveRay_iff (t, y.2)).2
        ⟨by simpa [t] using ht_pos, (one_div_le ht_pos hy).2 ht_right⟩
    · exact (mem_nonnegativeFirstCoordinateRay_iff (t - y.1, 0)).2
        ⟨by linarith, by simp⟩

/-- Proposition 2.15 (2): adding the nonnegative first-coordinate ray to `Q` leaves `Q`
unchanged. -/
-- Proof sketch: adding `(r, 0)` only increases the first coordinate, so the reciprocal bound
-- `1 / x₁` decreases while the second coordinate stays fixed; the opposite inclusion follows from
-- the zero vector lying on the ray.
theorem reciprocalEpigraphOnPositiveRay_add_nonnegativeFirstCoordinateRay :
    reciprocalEpigraphOnPositiveRay + nonnegativeFirstCoordinateRay =
      reciprocalEpigraphOnPositiveRay := by
  ext y
  constructor
  · rintro ⟨x, hx, r, hr, rfl⟩
    rcases (mem_reciprocalEpigraphOnPositiveRay_iff x).1 hx with ⟨hx1, hx2⟩
    rcases (mem_nonnegativeFirstCoordinateRay_iff r).1 hr with ⟨hr1, hr2⟩
    refine (mem_reciprocalEpigraphOnPositiveRay_iff (x + r)).2 ?_
    constructor
    · simpa [Prod.fst_add, hr2] using add_pos_of_pos_of_nonneg hx1 hr1
    · have hmono : 1 / (x.1 + r.1) ≤ 1 / x.1 := by
        apply one_div_le_one_div_of_le hx1
        linarith
      simpa [Prod.snd_add, hr2] using le_trans hmono hx2
  · intro hy
    refine Set.mem_add.2 ?_
    refine ⟨y, hy, (0, 0), ?_, by simp⟩
    simpa using (mem_nonnegativeFirstCoordinateRay_iff (0, 0)).2 (by simp)

/-! ### Text_2_15 (from Chap02) -/
open Finset

noncomputable section

variable {n : ℕ}

/- Text 2.15 lies in the finite-dimensional Euclidean hard-instance domain for the chapter's
quadratic lower-bound family.

Source/core/bridge triage:
* source-facing: the norm estimate for the textbook stationary point `\bar x_k`
* core/canonical: the owner point `quadraticHardInstanceStationaryPoint k` from `Text_2_13`
* bridge/view: the coordinate formula `quadraticHardInstanceStationaryPoint_apply`, the Euclidean
  squared-norm owner theorem `EuclideanSpace.real_norm_sq_eq`, and the arithmetic estimate
  `sum_Icc_sq_le_cubic_third` from `Text_2_16`

Sampled owner-style declarations in this domain:
* `quadraticHardInstanceStationaryPoint` in `Text_2_13`
* `quadraticHardInstanceStationaryPoint_apply` in `Text_2_13`
* `EuclideanSpace.real_norm_sq_eq` in mathlib
* `sum_Icc_sq_le_cubic_third` in `Text_2_16`

Best owner abstraction:
* the canonical stationary point `quadraticHardInstanceStationaryPoint k`

Primitive data:
* the canonical stationary point `quadraticHardInstanceStationaryPoint k`

Derived API:
* its exact squared norm, obtained by coordinate expansion through the owner Euclidean norm
* the cubic upper bound from `Text_2_16`

This file keeps the source-facing norm estimate, but derives it directly from the chapter owner
stationary point and the existing Euclidean/arithmetic owner declarations rather than maintaining
any parallel local coordinate wrapper or finite-sum API.
-/

/-- The squared Euclidean norm of the canonical hard-instance stationary point is the normalized
sum of the first `k.1 + 1` squares. -/
theorem quadraticHardInstanceStationaryPoint_sqNorm_eq (k : Fin n) :
    ‖quadraticHardInstanceStationaryPoint k‖ ^ 2 =
      (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun i ↦
    if hi : i < n then (quadraticHardInstanceStationaryPoint k) ⟨i, hi⟩ ^ 2 else 0
  have hnorm : ‖quadraticHardInstanceStationaryPoint k‖ ^ 2 = ∑ i ∈ range n, f i := by
    calc
      ‖quadraticHardInstanceStationaryPoint k‖ ^ 2
          = ∑ i : Fin n, (quadraticHardInstanceStationaryPoint k) i ^ 2 := by
              simpa using (EuclideanSpace.real_norm_sq_eq (quadraticHardInstanceStationaryPoint k))
      _ = ∑ i : Fin n, f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [f]
      _ = ∑ i ∈ range n, f i := Fin.sum_univ_eq_sum_range f n
  rw [hnorm]
  have hk1 : k.1 + 1 ≤ n := Nat.succ_le_of_lt k.2
  rw [← Finset.sum_range_add_sum_Ico f hk1]
  have htail : (∑ i ∈ Ico (k.1 + 1) n, f i) = 0 := by
    refine sum_eq_zero ?_
    intro i hi
    have hk_le_i : k.1 + 1 ≤ i := (mem_Ico.mp hi).1
    have hi_lt_n : i < n := (mem_Ico.mp hi).2
    have hk_lt_i : k.1 < i := lt_of_lt_of_le (Nat.lt_succ_self _) hk_le_i
    have hnot : ¬ (⟨i, hi_lt_n⟩ : Fin n) ≤ k := by
      exact fun h ↦ not_le_of_gt hk_lt_i (Fin.le_iff_val_le_val.mp h)
    simp [f, hi_lt_n, quadraticHardInstanceStationaryPoint_apply, hnot]
  rw [htail, add_zero]
  calc
    ∑ i ∈ range (k.1 + 1), f i
        = ∑ i ∈ range (k.1 + 1),
            ((((k.1 + 1 - i : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          have hi_lt_n : i < n := lt_of_lt_of_le (mem_range.mp hi) hk1
          have hi_le_k : i ≤ k.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
          have hik : (⟨i, hi_lt_n⟩ : Fin n) ≤ k :=
            Fin.le_iff_val_le_val.mpr hi_le_k
          simp [f, hi_lt_n, quadraticHardInstanceStationaryPoint_apply, hik]
          field_simp
          have hreal :
              (((k.1 : ℕ) : ℝ) + 2 - ((i : ℝ) + 1)) = (((k.1 + 1 - i : ℕ) : ℝ)) := by
            have hi2 : i + 1 ≤ k.1 + 2 := by omega
            have hcast : (((k.1 + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) =
                (((k.1 + 1 - i : ℕ) : ℝ)) := by
              rw [← Nat.cast_sub hi2]
              norm_num
              omega
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hcast
          rw [hreal]
    _ = ∑ i ∈ range (k.1 + 1),
          ((((i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
          have hrewrite :
              ∑ i ∈ range (k.1 + 1), ((((k.1 + 1 - i : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) =
                ∑ i ∈ range (k.1 + 1), ((((k.1 - i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
                  refine sum_congr rfl ?_
                  intro i hi
                  have hi_le_k : i ≤ k.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
                  have hnat : k.1 + 1 - i = k.1 - i + 1 := by omega
                  simp [hnat]
          have hreflect :
              ∑ i ∈ range (k.1 + 1), ((((k.1 - i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) =
                ∑ i ∈ range (k.1 + 1), ((((i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                    (Finset.sum_range_reflect
                      (fun i ↦ ((((i + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ)) ^ 2))
                      (k.1 + 1))
          exact hrewrite.trans hreflect
    _ = ∑ i ∈ range (k.1 + 1), (((i + 1 : ℕ) : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          rw [div_pow]
    _ = (∑ i ∈ range (k.1 + 1), (((i + 1 : ℕ) : ℝ) ^ 2)) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
          rw [Finset.sum_div]
    _ = (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
          congr 1
          rw [show Icc 1 (k.1 + 1) = Ico 1 (k.1 + 2) by
            simpa using (Finset.Ico_succ_right_eq_Icc 1 (k.1 + 1))]
          rw [Finset.sum_Ico_eq_sum_range]
          refine sum_congr rfl ?_
          intro i hi
          ring_nf

/-- Helper for Text 2.15: the textbook square-sum bound follows from the degree-two Faulhaber
formula over `ℚ`. -/
private lemma sum_Icc_sq_le_cubic_third_rat_local (m : ℕ) :
    (∑ i ∈ Icc 1 m, (i : ℚ) ^ 2) ≤ ((m + 1 : ℚ) ^ 3) / 3 := by
  -- Route correction: prove the arithmetic estimate locally from `sum_Ico_pow` so this file no
  -- longer depends on the later statement file `Text_2_16`.
  rw [← Ico_add_one_right_eq_Icc 1 m]
  -- Expand the degree-two Faulhaber identity on the canonical half-open interval.
  rw [sum_Ico_pow]
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
  norm_num [bernoulli'_zero, bernoulli'_one, bernoulli'_two]
  have hm : (0 : ℚ) ≤ m := by
    positivity
  nlinarith

/-- Helper for Text 2.15: cast the local rational square-sum bound into `ℝ` for the norm
estimate. -/
private lemma sum_Icc_sq_le_cubic_third_real_local (m : ℕ) :
    (∑ i ∈ Icc 1 m, (i : ℝ) ^ 2) ≤ ((m + 1 : ℝ) ^ 3) / 3 := by
  -- Move the rational Faulhaber estimate into `ℝ`, keeping exactly the same interval sum.
  have hq := sum_Icc_sq_le_cubic_third_rat_local m
  have hq' :
      ((∑ i ∈ Icc 1 m, (i : ℚ) ^ 2 : ℚ) : ℝ) ≤
        ((((m + 1 : ℚ) ^ 3) / 3 : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa using hq'

/-- Text 2.15: the hard-instance stationary point `\bar x_k`, encoded by
`quadraticHardInstanceStationaryPoint k`, satisfies `‖\bar x_k‖^2 ≤ (1 / 3) * (k + 1)`. In the
file's zero-based `Fin` indexing, `k : Fin n` encodes the textbook index `k + 1`, so the right
side becomes `(1 / 3) * (k.1 + 2)`. -/
-- Proof sketch: apply the exact squared-norm identity
-- `quadraticHardInstanceStationaryPoint_sqNorm_eq`, then use the owner arithmetic estimate
-- `sum_Icc_sq_le_cubic_third` with `k + 1`, and simplify the resulting cubic-over-quadratic
-- expression.
theorem quadraticHardInstanceStationaryPoint_sqNorm_le (k : Fin n) :
    ‖quadraticHardInstanceStationaryPoint k‖ ^ 2 ≤ (1 / 3 : ℝ) * (k.1 + 2) := by
  -- Rewrite the geometric norm exactly as the arithmetic sum from the source proof.
  rw [quadraticHardInstanceStationaryPoint_sqNorm_eq]
  have hsq :
      (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) ≤ (((k.1 + 2 : ℕ) : ℝ) ^ 3) / 3 := by
    -- Apply the local cubic upper bound at `m = k.1 + 1`.
    convert sum_Icc_sq_le_cubic_third_real_local (k.1 + 1) using 1
    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  have hdiv :
      (∑ i ∈ Icc 1 (k.1 + 1), (i : ℝ) ^ 2) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) ≤
        ((((k.1 + 2 : ℕ) : ℝ) ^ 3) / 3) / (((k.1 + 2 : ℕ) : ℝ) ^ 2) := by
    -- Divide by the positive denominator to match the normalized norm identity.
    exact div_le_div_of_nonneg_right hsq (by positivity)
  -- Simplify the resulting cubic-over-quadratic expression to the claimed linear bound.
  refine hdiv.trans_eq ?_
  have hk2 : (((k.1 + 2 : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
  field_simp [hk2]
  norm_num

/-! ### Theorem_2_15 (from Chap02) -/
open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: smooth convex gradient descent on real Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)` in `Chap01/Definition_1_5_2`, the chapter's canonical
  `C^{1,1}_L` owner on real Hilbert spaces;
* `gradientMethod_value_antitone_of_constant_stepsize` in `Proposition_2_8`, the canonical
  constant-step monotonicity theorem on that intrinsic ambient layer;
* `gradientMethod_sqdist_le_geometric_rate` in `Theorem_2_17`, which already states a Chapter 2
  gradient-method rate theorem on the same intrinsic Hilbert-space owner layer;
* `ConvexC1SeminormSmooth.gradient_lipschitz` in `Theorem_2_5`, the finite-dimensional bridge
  from the Chapter 2 notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` to the canonical Lipschitz-gradient
  owner hypothesis.

Source/core/bridge triage:
* source-facing: the explicit gradient-descent objective-gap rate of Theorem 2.15;
* core/canonical: `ConvexOn ℝ Set.univ f`, `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`,
  `IsMinOn f Set.univ xStar`, and the constant-step trajectory
  `gradientMethod (fun _ ↦ h) f x0`;
* bridge/view: the finite-dimensional Chapter 2 wrapper `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`, whose
  only role here is to recover the intrinsic owner hypotheses.

Primitive data:
* whole-space convexity of `f`;
* `C¹` regularity of `f`;
* the global Lipschitz bound for `∇ f`;
* a global minimizer `xStar` with `IsMinOn f Set.univ xStar`;
* the constant-step bounds `0 ≤ h ≤ 2 / L`;
* the initial point `x0`.

Derived API:
* the Chapter 1 sufficient-decrease and monotonicity estimates for the constant-step trajectory;
* the convex first-order lower bound against the minimizer;
* the specialization from the Chapter 2 smooth-convex notation
  `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`.

Accordingly, the main theorem is stated on the intrinsic real-Hilbert-space owner layer, and the
finite-dimensional Chapter 2 notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` is kept only as a thin
specialization bridge rather than as primitive public data. -/

namespace ConvexC1SeminormSmooth

variable {L : NNReal} {f : E → ℝ}

section

variable [CompleteSpace E]

/-- Helper for Theorem 2.15: convexity and an `L`-Lipschitz gradient imply the quadratic lower
tangent estimate that underlies the cocoercivity argument. -/
private theorem gradient_quadratic_lower_bound_of_convex_contDiffOne_lipschitz
    (hconv : ConvexOn ℝ Set.univ f)
    (hf_C1 : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hL : 0 < L)
    (x y : E) :
    f y + inner ℝ (∇ f y) (x - y) +
        (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) ≤
      f x := by
  let d := ∇ f x - ∇ f y
  let z := x - (1 / (L : ℝ)) • d
  have hgradAt : ∀ u : E, HasGradientAt f (∇ f u) u :=
    fun u ↦ (hf_C1.differentiable_one u).hasGradientAt
  -- The smooth upper model at `x` controls the shifted point `z`.
  have hupper :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    have h :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient hf_C1 hgrad_lipschitz x z
    have hz : z - x = -((1 / (L : ℝ)) • d) := by
      simp [z]
    calc
      f z ≤ f x + inner ℝ (∇ f x) (z - x) + ((L : ℝ) / 2) * ‖z - x‖ ^ (2 : ℕ) := by
        simpa [firstOrderTaylorModelAt_apply] using h
      _ = f x + inner ℝ (∇ f x) (-((1 / (L : ℝ)) • d)) +
            ((L : ℝ) / 2) * ‖-((1 / (L : ℝ)) • d)‖ ^ (2 : ℕ) := by
            rw [hz]
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            ((L : ℝ) / 2) * ((1 / (L : ℝ)) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ)) := by
            simp [inner_smul_right, norm_smul, sq]
            ring
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            have hL0 : (L : ℝ) ≠ 0 := by
              exact_mod_cast (ne_of_gt hL)
            field_simp [hL0]
  -- Convexity gives the matching lower tangent bound at `y`.
  have hlower :
      f z ≥
        f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
    have h :=
      hconv.lower_tangent_plane_of_hasGradientWithinAt
        y (by simp) (∇ f y) ((hasGradientWithinAt_univ).2 (hgradAt y)) z (by simp)
    have hz : z - y = (x - y) - (1 / (L : ℝ)) • d := by
      simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      f z ≥ f y + inner ℝ (∇ f y) (z - y) := h
      _ = f y + inner ℝ (∇ f y) ((x - y) - (1 / (L : ℝ)) • d) := by
        rw [hz]
      _ = f y + inner ℝ (∇ f y) (x - y) -
            (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
            rw [inner_sub_right, inner_smul_right]
            ring
  have hinner :
      inner ℝ (∇ f x) d = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (∇ f x) d = inner ℝ (d + ∇ f y) d := by
        congr 1
        dsimp [d]
        abel_nf
      _ = inner ℝ d d + inner ℝ (∇ f y) d := by
        rw [inner_add_left]
      _ = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
        simp [inner_self_eq_norm_sq_to_K, add_comm]
  have hupper' :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    calc
      f z ≤
          f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := hupper
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            rw [hinner]
            ring
  -- Comparing the lower and upper controls isolates the quadratic remainder.
  have hmid :
      f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) :=
    le_trans hlower hupper'
  have hmid' :
      f y + inner ℝ (∇ f y) (x - y) ≤
        f x - (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    linarith
  have hfinal :
      f y + inner ℝ (∇ f y) (x - y) +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) ≤
        f x := by
    linarith
  simpa [d] using hfinal

/-- Helper for Theorem 2.15: specializing the quadratic lower tangent estimate at a minimizer
gives the pairing bound needed for the radius monotonicity argument. -/
private theorem gradient_pairing_with_minimizer_gap_ge_norm_sq_div_local
    (hconv : ConvexOn ℝ Set.univ f)
    (hf_C1 : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x) (x - xStar) := by
  have hgrad0 : ∇ f xStar = 0 := by
    exact
      (isMinOn_hasGradientAt_zero_of_differentiableAt
        (hf_C1.differentiable_one xStar) hxStar).gradient
  by_cases hL : 0 < L
  · have hxy :=
      gradient_quadratic_lower_bound_of_convex_contDiffOne_lipschitz
        hconv hf_C1 hgrad_lipschitz hL x xStar
    have hyx :=
      gradient_quadratic_lower_bound_of_convex_contDiffOne_lipschitz
        hconv hf_C1 hgrad_lipschitz hL xStar x
    have hxy' :
        f xStar + (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤ f x := by
      simpa [hgrad0, sub_zero] using hxy
    have hyx' :
        f x - inner ℝ (∇ f x) (x - xStar) +
            (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤
          f xStar := by
      have hsub : xStar - x = -(x - xStar) := by
        abel_nf
      have hyx'' := hyx
      rw [hgrad0, norm_sub_rev, hsub, inner_neg_right, sub_zero] at hyx''
      exact hyx''
    have hsum := add_le_add hxy' hyx'
    ring_nf at hsum ⊢
    linarith
  · have hL0 : L = 0 := le_antisymm (le_of_not_gt hL) bot_le
    have hgrad_eq : ∇ f x = ∇ f xStar := by
      have hdist := hgrad_lipschitz.dist_le_mul x xStar
      have hdist0 : dist (∇ f x) (∇ f xStar) = 0 := by
        apply le_antisymm
        · simpa [hL0] using hdist
        · exact dist_nonneg
      exact eq_of_dist_eq_zero hdist0
    simp [hL0, hgrad_eq, hgrad0]

/-- Theorem 2.15 on the intrinsic real-Hilbert-space owner layer: if `f` is convex on the whole
space, `C¹`, has `L`-Lipschitz gradient, `xStar` is a global minimizer of `f`, and `0 ≤ h ≤ 2 / L`,
then the gradient method with step size `h` satisfies the explicit sublinear objective-gap bound at
every iterate. The textbook `ℝⁿ` formulation is recovered by the finite-dimensional Chapter 2
specialization theorem below. The source strict range `0 < h < 2 / L` is a special case, and at
the endpoints the correction factor `h * (2 - L * h)` vanishes. -/
-- Proof sketch: combine the Chapter 1 constant-step sufficient-decrease / monotonicity API with
-- the convex first-order inequality against the minimizer `xStar`, using `hxStar` to replace
-- `f xStar` by the minimum value. This yields a reciprocal-gap estimate for
-- `Δ_k = f x_k - f xStar` in terms of `‖x0 - xStar‖²`; telescope that estimate over the
-- constant-step trajectory. The Chapter 2 owner notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`
-- reappears only in the specialization bridge below.
theorem gradientMethod_objective_gap_le_explicit_rate
    (hconv : ConvexOn ℝ Set.univ f)
    (hf_C1 : ContDiff ℝ 1 f)
    (hgrad : LipschitzWith L (∇ f))
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ) (hh_nonneg : 0 ≤ h) (hh_le : h ≤ 2 / (L : ℝ))
    (x0 : E) (k : ℕ) :
    f (gradientMethod (fun _ ↦ h) f x0 k) - f xStar ≤
      (2 * (f x0 - f xStar) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
          h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar)) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ h) f x0
  let Δ : ℕ → ℝ := fun i ↦ f (traj i) - f xStar
  let R2 : ℝ := ‖x0 - xStar‖ ^ (2 : ℕ)
  let ω : ℝ := h * (2 - (L : ℝ) * h) / 2
  have hgradAt : ∀ x : E, HasGradientAt f (∇ f x) x :=
    fun x ↦ (hf_C1.differentiable_one x).hasGradientAt
  have hxStar_min : ∀ y : E, f xStar ≤ f y := by
    intro y
    exact (isMinOn_iff.mp hxStar) y (by simp)
  have hΔ_nonneg : ∀ i : ℕ, 0 ≤ Δ i := by
    intro i
    dsimp [Δ, traj]
    exact sub_nonneg.mpr (hxStar_min (traj i))
  have hω_nonneg : 0 ≤ ω := by
    -- The textbook correction factor is nonnegative on the full monotonicity interval.
    by_cases hL0 : (L : ℝ) = 0
    · have hh_nonpos : h ≤ 0 := by
        simpa [hL0] using hh_le
      have hh_zero : h = 0 := by
        linarith
      simp [ω, hh_zero, hL0]
    · have hL_pos : 0 < (L : ℝ) :=
        lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
      have hmul : (L : ℝ) * h ≤ 2 := by
        simpa [mul_comm] using (le_div_iff₀ hL_pos).mp hh_le
      dsimp [ω]
      nlinarith
  have hmono_f :
      Antitone (fun i ↦ f (traj i)) := by
    refine antitone_nat_of_succ_le ?_
    intro i
    have hstep :=
      gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
        (hf := hf_C1) (hgrad := hgrad) (traj i) h
    have hcoeff_nonneg : 0 ≤ h * (1 - ((L : ℝ) * h) / 2) := by
      dsimp [ω] at hω_nonneg
      nlinarith
    have hdrop_nonneg :
        0 ≤ h * (1 - ((L : ℝ) * h) / 2) * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
      positivity
    simpa [traj, gradientMethod_succ] using le_trans hstep (by linarith)
  have hmono : Antitone Δ := by
    intro i j hij
    dsimp [Δ]
    exact sub_le_sub_right (hmono_f hij) _
  have hsqdist_step :
      ∀ x : E, ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤ ‖x - xStar‖ ^ (2 : ℕ) := by
    intro x
    -- Expand one step and use the local minimizer-pairing inequality.
    have hpair :=
      gradient_pairing_with_minimizer_gap_ge_norm_sq_div_local
        hconv hf_C1 hgrad hxStar x
    have hcoeff_nonpos : h ^ (2 : ℕ) - 2 * h / (L : ℝ) ≤ 0 := by
      by_cases hL0 : (L : ℝ) = 0
      · have hh_nonpos : h ≤ 0 := by
          simpa [hL0] using hh_le
        have hh_zero : h = 0 := by
          linarith
        simp [hh_zero, hL0]
      · have hL_pos : 0 < (L : ℝ) :=
          lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
        have hsq_le : h ^ (2 : ℕ) ≤ 2 * h / (L : ℝ) := by
          have hh' : h * h ≤ h * (2 / (L : ℝ)) :=
            mul_le_mul_of_nonneg_left hh_le hh_nonneg
          calc
            h ^ (2 : ℕ) = h * h := by ring
            _ ≤ h * (2 / (L : ℝ)) := hh'
            _ = 2 * h / (L : ℝ) := by ring
        linarith
    have hpair' :
        (-2 * h) * inner ℝ (∇ f x) (x - xStar) ≤
          (-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonpos_left hpair (by nlinarith)
    have hexpand :
        ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
          ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
      calc
        ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
            ‖(x - xStar) - h • ∇ f x‖ ^ (2 : ℕ) := by
              abel_nf
        _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * inner ℝ (x - xStar) (h • ∇ f x) +
              ‖h • ∇ f x‖ ^ (2 : ℕ) := by
              simpa using norm_sub_sq_real (x - xStar) (h • ∇ f x)
        _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
              h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
              rw [real_inner_smul_right, real_inner_comm]
              simp [norm_smul, Real.norm_of_nonneg hh_nonneg, sq]
              ring
    have hrest_nonpos :
        (-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) ≤
          0 := by
      have hnorm_nonneg : 0 ≤ ‖∇ f x‖ ^ (2 : ℕ) := by
        positivity
      have hrewrite :
          (-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) +
              h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) =
            (h ^ (2 : ℕ) - 2 * h / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
        ring
      rw [hrewrite]
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hnorm_nonneg
    calc
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
          ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := hexpand
      _ ≤ ‖x - xStar‖ ^ (2 : ℕ) +
            ((-2 * h) * ((1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ)) +
              h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ)) := by
            linarith
      _ ≤ ‖x - xStar‖ ^ (2 : ℕ) := by
            linarith
  have hsqdist_le_initial : ∀ i : ℕ, ‖traj i - xStar‖ ^ (2 : ℕ) ≤ R2 := by
    intro i
    induction i with
    | zero =>
        simp [traj, R2]
    | succ i hi =>
        -- The source invariant `r_(i+1) ≤ r_i ≤ r_0` follows by iterating the one-step estimate.
        have hstep := hsqdist_step (traj i)
        simpa [traj, R2, gradientMethod_succ] using le_trans hstep hi
  have hgap_sq_le : ∀ i : ℕ, (Δ i) ^ (2 : ℕ) ≤ R2 * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
    intro i
    -- Combine the convex lower-tangent inequality with Cauchy-Schwarz and the radius invariant.
    have htangent :=
      hconv.lower_tangent_plane_of_hasGradientWithinAt
        (traj i) (by simp) (∇ f (traj i))
        ((hasGradientWithinAt_univ).2 (hgradAt (traj i)))
        xStar (by simp)
    have hfirst :
        Δ i ≤ inner ℝ (∇ f (traj i)) (traj i - xStar) := by
      have hsub :
          inner ℝ (∇ f (traj i)) (xStar - traj i) =
            -inner ℝ (∇ f (traj i)) (traj i - xStar) := by
        have : xStar - traj i = -(traj i - xStar) := by
          abel_nf
        rw [this, inner_neg_right]
      dsimp [Δ, traj] at *
      rw [hsub] at htangent
      linarith
    have hcs :
        Δ i ≤ ‖∇ f (traj i)‖ * ‖traj i - xStar‖ := by
      exact le_trans (le_trans hfirst (le_abs_self _)) (abs_real_inner_le_norm _ _)
    have hrad :
        ‖traj i - xStar‖ ≤ ‖x0 - xStar‖ := by
      exact
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 <|
          by simpa [R2, pow_two] using hsqdist_le_initial i
    have hcs' :
        Δ i ≤ ‖∇ f (traj i)‖ * ‖x0 - xStar‖ := by
      exact le_trans hcs (mul_le_mul_of_nonneg_left hrad (norm_nonneg _))
    have hsq :=
      (sq_le_sq₀ (hΔ_nonneg i)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs'
    simpa [R2, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  by_cases hΔ0_zero : Δ 0 = 0
  · -- If the initial gap vanishes, monotonicity and nonnegativity force every later gap to vanish.
    have hgap0 : f x0 - f xStar = 0 := by
      simpa [Δ, traj, gradientMethod_zero] using hΔ0_zero
    have hΔk_zero : Δ k = 0 := by
      have hk_le_zero : Δ k ≤ 0 := by
        simpa [hΔ0_zero] using hmono (Nat.zero_le k)
      exact le_antisymm hk_le_zero (hΔ_nonneg k)
    simpa [Δ, traj, R2, gradientMethod_zero, hgap0, hΔk_zero]
  · have hΔ0_pos : 0 < Δ 0 :=
        lt_of_le_of_ne (hΔ_nonneg 0) (Ne.symm hΔ0_zero)
    have hR2_nonneg : 0 ≤ R2 := by
      dsimp [R2]
      positivity
    have hR2_pos : 0 < R2 := by
      have hR2_ne : R2 ≠ 0 := by
        intro hR2_zero
        have hnorm_zero : ‖x0 - xStar‖ = 0 := by
          have hsq_zero : ‖x0 - xStar‖ ^ (2 : ℕ) = 0 := by
            simpa [R2] using hR2_zero
          nlinarith [norm_nonneg (x0 - xStar)]
        have hx0_eq : x0 = xStar := by
          exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
        have : Δ 0 = 0 := by
          simpa [Δ, traj, gradientMethod_zero, hx0_eq]
        exact hΔ0_zero this
      exact lt_of_le_of_ne hR2_nonneg hR2_ne.symm
    have hstep_rec :
        ∀ i : ℕ, Δ (i + 1) ≤ Δ i - (ω / R2) * (Δ i) ^ (2 : ℕ) := by
      intro i
      -- Route correction: eliminate the gradient norm using the source quadratic gap estimate.
      have hdrop :=
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          (hf := hf_C1) (hgrad := hgrad) (traj i) h
      have hdrop_step :
          f (traj (i + 1)) ≤
            f (traj i) - h * (1 - ((L : ℝ) * h) / 2) * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
        simpa [traj, gradientMethod_succ] using hdrop
      have hdrop' :
          Δ (i + 1) ≤ Δ i - ω * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
        have hω_eq : h * (1 - ((L : ℝ) * h) / 2) = ω := by
          dsimp [ω]
          ring
        have hdrop_gap :
            f (traj (i + 1)) - f xStar ≤
              (f (traj i) - f xStar) -
                h * (1 - ((L : ℝ) * h) / 2) * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
          linarith
        simpa [Δ, hω_eq] using hdrop_gap
      have hgrad_elim :
          (ω / R2) * (Δ i) ^ (2 : ℕ) ≤ ω * ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
        have hdiv :
            (Δ i) ^ (2 : ℕ) / R2 ≤ ‖∇ f (traj i)‖ ^ (2 : ℕ) := by
          exact (div_le_iff₀ hR2_pos).2 <|
            by simpa [mul_assoc, mul_left_comm, mul_comm] using hgap_sq_le i
        have hmul := mul_le_mul_of_nonneg_left hdiv hω_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
      linarith
    by_cases hΔk_zero : Δ k = 0
    · have hcoeff_nonneg : 0 ≤ h * (2 - (L : ℝ) * h) := by
        dsimp [ω] at hω_nonneg
        nlinarith
      have hrhs_nonneg :
          0 ≤
            (2 * (f x0 - f xStar) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              (2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
                h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar)) := by
        have hgap0_nonneg : 0 ≤ f x0 - f xStar := by
          simpa [Δ, traj, gradientMethod_zero] using hΔ_nonneg 0
        have hden_nonneg :
            0 ≤ 2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
              h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar) := by
          positivity
        exact div_nonneg (by positivity) hden_nonneg
      simpa [Δ, traj, gradientMethod_zero, hΔk_zero] using hrhs_nonneg
    · have hΔk_pos : 0 < Δ k :=
          lt_of_le_of_ne (hΔ_nonneg k) (Ne.symm hΔk_zero)
      have hΔ_pos_prefix : ∀ {i : ℕ}, i ≤ k → 0 < Δ i := by
        intro i hik
        exact lt_of_lt_of_le hΔk_pos (hmono hik)
      have hrecip_step :
          ∀ i : ℕ, i < k → ω / R2 ≤ 1 / Δ (i + 1) - 1 / Δ i := by
        intro i hik
        have hi1_le : i + 1 ≤ k := Nat.succ_le_of_lt hik
        have hi_le : i ≤ k := Nat.le_trans (Nat.le_succ i) hi1_le
        have hΔi_pos : 0 < Δ i := hΔ_pos_prefix hi_le
        have hΔi1_pos : 0 < Δ (i + 1) := hΔ_pos_prefix hi1_le
        have hmono_step : Δ (i + 1) ≤ Δ i := hmono (Nat.le_succ i)
        have hdiff :
            (ω / R2) * (Δ i) ^ (2 : ℕ) ≤ Δ i - Δ (i + 1) := by
          linarith [hstep_rec i]
        have hmul_sq :
            ω * (Δ i) ^ (2 : ℕ) ≤ R2 * (Δ i - Δ (i + 1)) := by
          have hmul := mul_le_mul_of_nonneg_left hdiff hR2_nonneg
          simpa [div_eq_mul_inv, hR2_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
        have hmul_prod :
            ω * (Δ i * Δ (i + 1)) ≤ R2 * (Δ i - Δ (i + 1)) := by
          have hleft :
              ω * (Δ i * Δ (i + 1)) ≤ ω * ((Δ i) * Δ i) := by
            gcongr
          calc
            ω * (Δ i * Δ (i + 1)) ≤ ω * (Δ i * Δ i) := hleft
            _ = ω * (Δ i) ^ (2 : ℕ) := by ring
            _ ≤ R2 * (Δ i - Δ (i + 1)) := hmul_sq
        have htmp :
            ω ≤ R2 * ((Δ i - Δ (i + 1)) / (Δ i * Δ (i + 1))) := by
          have hprod_pos : 0 < Δ i * Δ (i + 1) := mul_pos hΔi_pos hΔi1_pos
          have htmp' :
              ω ≤ (R2 * (Δ i - Δ (i + 1))) / (Δ i * Δ (i + 1)) := by
            exact (le_div_iff₀ hprod_pos).2 <|
              by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_prod
          simpa [mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using htmp'
        have hfrac :
            ω / R2 ≤ (Δ i - Δ (i + 1)) / (Δ i * Δ (i + 1)) := by
          exact (div_le_iff₀ hR2_pos).2 <|
            by simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
        have hrewrite :
            (Δ i - Δ (i + 1)) / (Δ i * Δ (i + 1)) =
              1 / Δ (i + 1) - 1 / Δ i := by
          field_simp [hΔi_pos.ne', hΔi1_pos.ne']
        simpa [hrewrite] using hfrac
      have hrecip_lower :
          ∀ n : ℕ, n ≤ k → 1 / Δ n ≥ 1 / Δ 0 + (n : ℝ) * (ω / R2) := by
        intro n
        induction n with
        | zero =>
            intro _
            simpa
        | succ n ihn =>
            intro hnk
            have hn_le : n ≤ k := Nat.le_trans (Nat.le_succ n) hnk
            have hn_lt : n < k := lt_of_lt_of_le (Nat.lt_succ_self n) hnk
            have hprev := ihn hn_le
            have hstep := hrecip_step n hn_lt
            have hsucc_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
              norm_num
            rw [hsucc_cast]
            linarith
      have hk_lower :
          1 / Δ 0 + (k : ℝ) * (ω / R2) ≤ 1 / Δ k := by
        linarith [hrecip_lower k le_rfl]
      have hsum_pos :
          0 < 1 / Δ 0 + (k : ℝ) * (ω / R2) := by
        have hbase_pos : 0 < 1 / Δ 0 := one_div_pos.mpr hΔ0_pos
        have htail_nonneg : 0 ≤ (k : ℝ) * (ω / R2) := by
          positivity
        linarith
      have hk_inv :
          Δ k ≤ 1 / (1 / Δ 0 + (k : ℝ) * (ω / R2)) := by
        simpa [one_div, hΔk_pos.ne', hsum_pos.ne'] using
          (one_div_le_one_div_of_le hsum_pos hk_lower)
      have hden_pos :
          0 < 2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * (Δ 0) := by
        have hcoeff_nonneg : 0 ≤ h * (2 - (L : ℝ) * h) := by
          dsimp [ω] at hω_nonneg
          nlinarith
        positivity
      have hmid_rewrite :
          1 / (1 / Δ 0 + (k : ℝ) * (ω / R2)) =
            (Δ 0 * R2) / (R2 + ω * (k : ℝ) * Δ 0) := by
        have hmid_den_pos : 0 < R2 + ω * (k : ℝ) * Δ 0 := by
          positivity
        field_simp [hΔ0_pos.ne', hR2_pos.ne', hsum_pos.ne', hmid_den_pos.ne']
      have hfinal_rewrite :
          (Δ 0 * R2) / (R2 + ω * (k : ℝ) * Δ 0) =
            (2 * Δ 0 * R2) /
              (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) := by
        have hden_eq :
            R2 + ω * (k : ℝ) * Δ 0 =
              (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) / 2 := by
          dsimp [ω]
          ring
        rw [hden_eq]
        field_simp [hden_pos.ne']
      have hk_final :
          Δ k ≤
            (2 * Δ 0 * R2) /
              (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) := by
        calc
          Δ k ≤ 1 / (1 / Δ 0 + (k : ℝ) * (ω / R2)) := hk_inv
          _ = (Δ 0 * R2) / (R2 + ω * (k : ℝ) * Δ 0) := hmid_rewrite
          _ = (2 * Δ 0 * R2) /
                (2 * R2 + h * (2 - (L : ℝ) * h) * (k : ℝ) * Δ 0) := hfinal_rewrite
      simpa [Δ, traj, R2, gradientMethod_zero, mul_assoc, mul_left_comm, mul_comm] using hk_final

end

section

variable [FiniteDimensional ℝ E]

local instance finiteDimensionalComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "p" => normSeminorm ℝ E

/-- Finite-dimensional Chapter 2 specialization of Theorem 2.15: the source-facing notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` supplies the intrinsic Hilbert-space hypotheses used by
`gradientMethod_objective_gap_le_explicit_rate`. -/
theorem gradientMethod_objective_gap_le_explicit_rate_of_mem_F11
    (hf : f ∈ 𝓕[L, p]¹¹)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ) (hh_nonneg : 0 ≤ h) (hh_le : h ≤ 2 / (L : ℝ))
    (x0 : E) (k : ℕ) :
    f (gradientMethod (fun _ ↦ h) f x0 k) - f xStar ≤
      (2 * (f x0 - f xStar) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (2 * ‖x0 - xStar‖ ^ (2 : ℕ) +
          h * (2 - (L : ℝ) * h) * (k : ℝ) * (f x0 - f xStar)) :=
  gradientMethod_objective_gap_le_explicit_rate
    hf.convexOn hf.contDiff hf.gradient_lipschitz
    xStar hxStar h hh_nonneg hh_le x0 k

end

end ConvexC1SeminormSmooth
