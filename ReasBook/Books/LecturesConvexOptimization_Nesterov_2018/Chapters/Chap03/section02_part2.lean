import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_2_2 (from Chap03) -/
noncomputable section

open scoped PointwiseGrowthFunction SubgradientLocalizationMeasure

universe u

/- Theorem 3.2.2 lies in the chapter's subgradient-localization / best-sampled-gap domain.

Primary mathematical domain:
- real-valued convex analysis on a real inner-product space, organized around the owner
  localization measure `v[g; xStar]`, the owner growth profile `ω[f; xStar]`, and the owner
  finite prefix infimum `bestFunctionValueUpTo`.

Sampled owner-style declarations:
- `subgradientLocalizationMeasure` and
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`;
- `bestFunctionValueGapUpTo_le_modulusAtBestRadius` in `Lemma_3_2_2`, the chapter owner theorem
  for passing pointwise bounds to a bound at the best sampled radius;
- `pointwiseGrowthFunction_monotone` in `Proposition_3_34`;
- `bestRadiusUpTo` / `bestFunctionValueUpTo` in `Definition_3_55`.

Best owner abstraction:
- source-facing: the sampled objective-gap estimate of Theorem 3.2.2;
- core/canonical: `pointwiseGrowthFunction` plus
  `bestFunctionValueGapUpTo_le_modulusAtBestRadius`;
- bridge/view: the source-facing sampled minimum `bestFunctionValueUpTo` and sampled localization
  radius `bestRadiusUpTo`.

Primitive data:
- a real-valued function `f`;
- a chosen subgradient selection `g`;
- a sample sequence `xSeq`;
- a minimizer `xStar`, outer radius `R`, Lipschitz constant `M`, and stage `k`.

Derived API:
- the best sampled gap bound.

This item does not use coordinates or finite-dimensional structure, so the ambient space is the
intrinsic real inner-product-space owner rather than the concrete model `EuclideanSpace ℝ (Fin n)`.
The positivity hypothesis on the stepsizes is also redundant here: the theorem only consumes the
already-packaged radius bound `hvk`, so the public API keeps that canonical hypothesis and drops
the unused extra guard.
-/

section

variable {X : Type u} [MetricSpace X]

/-- If `f` is `M`-Lipschitz on the closed ball `Metric.closedBall xStar R`, then the pointwise
growth function at every radius `r ∈ [0, R]` is bounded by `(M : ℝ) * r`. -/
theorem pointwiseGrowthFunction_le_lipschitz_mul_of_le_radius
    {f : X → ℝ} {xStar : X} {r R : ℝ} {M : NNReal}
    (hLip : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hr_nonneg : 0 ≤ r) (hrR : r ≤ R) :
    ω[f; xStar] r ≤ (((M : ℝ) * r : ℝ) : WithTop ℝ) := by
  rw [pointwiseGrowthFunction, if_pos hr_nonneg]
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    simpa using Set.mem_image_of_mem
      (fun y : X ↦ ((f y - f xStar : ℝ) : WithTop ℝ))
      (Metric.mem_closedBall_self hr_nonneg)
  · rintro _ ⟨y, hy, rfl⟩
    have hyR : y ∈ Metric.closedBall xStar R :=
      Metric.closedBall_subset_closedBall hrR hy
    have hxStarR : xStar ∈ Metric.closedBall xStar R :=
      Metric.mem_closedBall_self (le_trans hr_nonneg hrR)
    have hy_dist : dist y xStar ≤ r := by
      simpa [Metric.mem_closedBall] using hy
    have hy_gap : f y - f xStar ≤ (M : ℝ) * r := by
      have hy_lip : f y ≤ f xStar + (M : ℝ) * dist y xStar :=
        hLip.le_add_mul hyR hxStarR
      have hy_mul : (M : ℝ) * dist y xStar ≤ (M : ℝ) * r :=
        mul_le_mul_of_nonneg_left hy_dist M.2
      linarith
    change ((f y - f xStar : ℝ) : WithTop ℝ) ≤
        (((M : ℝ) * r : ℝ) : WithTop ℝ)
    exact_mod_cast hy_gap

end

section

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Theorem 3.2.2: if `xStar` is a global minimizer of `f`, `f` is `M`-Lipschitz on the closed
Euclidean ball `B₂(xStar, R)`, `‖x₀ - xStar‖ ≤ R`, and the minimum localization measure
`v_k^* = bestRadiusUpTo (fun i ↦ v_f(xStar; xᵢ)) k` satisfies the standard
projected-subgradient estimate
`v_k^* ≤ (R^2 + ∑_{i=0}^k h_i^2) / (2 ∑_{i=0}^k h_i)`, then the best objective gap up to step `k`
satisfies `f_k^* - f^* ≤ M * (R^2 + ∑_{i=0}^k h_i^2) / (2 ∑_{i=0}^k h_i)`, where
`f_k^* = bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k`. -/
-- Proof sketch: apply Lemma 3.2.1 pointwise to the chosen subgradient selection and then take the
-- best-so-far value over `i = 0, ..., k`, obtaining `f_k^* - f^* ≤ ω_f(xStar; v_k^*)`. Since
-- `v_k^* ≤ v_0 ≤ ‖x₀ - xStar‖ ≤ R`, the growth function on that radius is bounded by the
-- Lipschitz estimate `(M : ℝ) * v_k^*`. Substitute the assumed upper bound on `v_k^*`.
theorem bestFunctionValueGapUpTo_le_lipschitz_mul_stepsize_ratio
    {f : V → ℝ} {g : V → V}
    (hg : ∀ x : V, IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (xSeq : ℕ → V) {xStar : V} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℕ → ℝ) (k : ℕ) {R : ℝ} {M : NNReal}
    (hLip : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hR : ‖xSeq 0 - xStar‖ ≤ R)
    (hvk :
      bestRadiusUpTo
          (fun i ↦ v[g; xStar] (xSeq i)) k ≤
        (R ^ (2 : ℕ) + ∑ i : Fin (k + 1), (h i) ^ (2 : ℕ)) /
          (2 * ∑ i : Fin (k + 1), h i)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
      (M : ℝ) *
        ((R ^ (2 : ℕ) + ∑ i : Fin (k + 1), (h i) ^ (2 : ℕ)) /
          (2 * ∑ i : Fin (k + 1), h i)) := by
  let v : ℕ → ℝ := fun i ↦ v[g; xStar] (xSeq i)
  let rStar : ℝ := bestRadiusUpTo v k
  let ratio : ℝ :=
    (R ^ (2 : ℕ) + ∑ i : Fin (k + 1), (h i) ^ (2 : ℕ)) /
      (2 * ∑ i : Fin (k + 1), h i)
  have hxStar_le : ∀ x : V, f xStar ≤ f x := isMinOn_univ_iff.mp hxStar
  have hbest :
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) ≤
        ω[f; xStar] rStar := by
    simpa [v, rStar] using
      bestFunctionValueGapUpTo_le_modulusAtBestRadius
        f
        (ω[f; xStar])
        (pointwiseGrowthFunction_monotone f xStar)
        xSeq
        xStar
        v
        k
        (fun i ↦
          sub_le_pointwiseGrowthFunction_of_localizationMeasure
            xStar
            (xSeq i)
            (hg (xSeq i)))
  have hv_nonneg (i : Fin (k + 1)) : 0 ≤ v i := by
    dsimp [v]
    exact
      subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
        (hg (xSeq i))
        (hxStar_le (xSeq i))
  have hrStar_nonneg : 0 ≤ rStar := by
    dsimp [rStar, bestRadiusUpTo]
    exact le_ciInf hv_nonneg
  have hv0_le : v 0 ≤ ‖xSeq 0 - xStar‖ := by
    dsimp [v]
    by_cases hzero : g (xSeq 0) = 0
    · simp [subgradientLocalizationMeasure, hzero]
    · rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero hzero]
      have hinner_le :
          inner ℝ (g (xSeq 0)) (xSeq 0 - xStar) ≤
            ‖g (xSeq 0)‖ * ‖xSeq 0 - xStar‖ := by
        exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
      have hnorm_pos : 0 < ‖g (xSeq 0)‖ := norm_pos_iff.mpr hzero
      exact
        (div_le_iff₀ hnorm_pos).2 <|
          by simpa [mul_comm] using hinner_le
  have hrStar_le_v0 : rStar ≤ v 0 := by
    have : bestFunctionValueUpTo v k ≤ v 0 := bestFunctionValueUpTo_le 0
    simpa [rStar] using this
  have hrStar_le_R : rStar ≤ R :=
    hrStar_le_v0.trans (hv0_le.trans hR)
  have hω_le :
      ω[f; xStar] rStar ≤ (((M : ℝ) * rStar : ℝ) : WithTop ℝ) := by
    exact pointwiseGrowthFunction_le_lipschitz_mul_of_le_radius hLip hrStar_nonneg hrStar_le_R
  have hrStar_le_ratio : rStar ≤ ratio := by
    simpa [v, rStar, ratio] using hvk
  have hmain :
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) ≤
        (((M : ℝ) * ratio : ℝ) : WithTop ℝ) := by
    calc
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) ≤
          ω[f; xStar] rStar := hbest
      _ ≤ (((M : ℝ) * rStar : ℝ) : WithTop ℝ) := hω_le
      _ ≤ (((M : ℝ) * ratio : ℝ) : WithTop ℝ) := by
        exact_mod_cast mul_le_mul_of_nonneg_left hrStar_le_ratio M.2
  have hmain_real :
      bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
        (M : ℝ) * ratio := by
    exact_mod_cast hmain
  simpa [ratio] using hmain_real

end

/-! ### Corollary_3_2_3 (from Chap03) -/
noncomputable section

universe u

/-
Corollary 3.2.3 lies in the constrained strong-convexity domain for real normed spaces.

Sampled owner-style declarations:
- project `StrongConvexOn.quadratic_growth_of_isMinOn` in `Theorem_2_30`
- mathlib `StrongConvexOn`
- mathlib `StrongConvexOn.strictConvexOn`
- project `StrongConvexOn.eq_of_isMinOn` in `Theorem_3_45`

Best owner abstraction:
- `StrongConvexOn Q μ f`

Primitive data:
- a feasible set `Q`, an objective `f`, a strong-convexity modulus `μ`, and feasible minimizers
  of `f` on `Q`

Derived API:
- the constrained quadratic-growth bound at a feasible minimizer
- uniqueness of the feasible minimizer when `μ > 0`

Source/core/bridge triage:
- source-facing: Corollary 3.2.3, the constrained quadratic-growth estimate and uniqueness
  consequence
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: `StrongConvexOn.strictConvexOn` together with
  `StrictConvexOn.eq_of_isMinOn`
-/

namespace StrongConvexOn

variable {E : Type u} [NormedAddCommGroup E]
variable [NormedSpace ℝ E]

/- Corollary 3.2.3 (quadratic-growth part): this is the direct constrained owner theorem already
exposed in Chapter 2. -/
recall StrongConvexOn.quadratic_growth_of_isMinOn_of_mem

/- Corollary 3.2.3 (uniqueness part): this is the direct chapter owner theorem already exposed in
`Theorem_3_45`. -/
recall StrongConvexOn.eq_of_isMinOn

end StrongConvexOn

end

/-! ### Lemma_3_2_3 (from Chap03) -/
noncomputable section

universe u

open Set AffineMap
open scoped Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 3.2.3 lies in the real normed-space strong-convexity / one-sided directional-derivative
domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `strongConvexOn_iff_convex`
- mathlib `ConvexOn.rightDeriv_le_slope_of_mem_interior`
- chapter `StrongConvexOnWith.lower_tangent_quadratic` in `Chap02/Definition_2_14`

Best owner abstraction:
- `StrongConvexOn Q μ f`

Primitive data:
- the ambient real normed space `E`
- the feasible set `Q`, modulus `μ`, objective `f`, and points `x`, `y`

Derived API:
- the affine line slice `t ↦ f (x + t • (y - x))`
- the induced one-dimensional strong-convexity owner on `((lineMap x y) ⁻¹' Q)`
- the quadratic-corrected convex slice on `((lineMap x y) ⁻¹' Q)`, derived through
  `strongConvexOn_iff_convex`
- the lower-support estimate at the right derivative `derivWithin ... (Set.Ici 0) 0`

Source/core/bridge triage:
- source-facing: Lemma 3.2.3, the interior-point quadratic lower-support estimate
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: the affine line map `lineMap x y : ℝ →ᵃ[ℝ] E`

The source statement is kept, but its owner is the intrinsic theorem of `StrongConvexOn` on an
arbitrary real normed space; the line slice is only the bridge used to apply the canonical
one-variable convex-derivative theorem.
-/

namespace StrongConvexOn

/-- Lemma 3.2.3: if `f` is `μ`-strongly convex on `Q`, then every interior point `x` of `Q`
supports the quadratic lower bound
`f y ≥ f x + f'(x; y - x) + (μ / 2) * ‖x - y‖^2`
at every `y ∈ Q`, where `f'(x; y - x)` is the one-sided directional derivative of the line
restriction `t ↦ f (x + t • (y - x))` at `t = 0`. -/
-- Proof sketch: restrict `f` to the affine line from `x` to `y`, subtract the quadratic term
-- `((μ / 2) * ‖y - x‖²) t²`, identify the sliced function as one-dimensional strongly convex, and
-- recover convexity of the corrected slice from `strongConvexOn_iff_convex`. The one-variable
-- theorem
-- `ConvexOn.rightDeriv_le_slope_of_mem_interior` applied at `0` then bounds the right derivative
-- by the secant slope at `1`, and the quadratic correction contributes exactly
-- `(μ / 2) * ‖x - y‖²`.
theorem lower_tangent_derivWithin_of_mem_interior
    {Q : Set E} {μ : ℝ} {f : E → ℝ} (hf : StrongConvexOn Q μ f)
    {x y : E} (hx : x ∈ interior Q) (hy : y ∈ Q) :
    f y ≥
      f x +
        derivWithin (fun t : ℝ ↦ f (x + t • (y - x))) (Set.Ici (0 : ℝ)) 0 +
        (μ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  let γ : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap x y
  let S : Set ℝ := γ ⁻¹' Q
  let m : ℝ := μ * ‖y - x‖ ^ (2 : ℕ)
  let g : ℝ → ℝ := fun t ↦ f (x + t • (y - x))
  let h : ℝ → ℝ := fun t ↦ g t - (m / 2) * t ^ (2 : ℕ)
  have hγ_apply (t : ℝ) : γ t = x + t • (y - x) := by
    change (AffineMap.lineMap x y) t = x + t • (y - x)
    rw [lineMap_apply_module']
    simp [add_comm]
  have hnorm {u v : ℝ} :
      ‖γ u - γ v‖ ^ (2 : ℕ) = ‖u - v‖ ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ) := by
    change ‖(AffineMap.lineMap x y) u - (AffineMap.lineMap x y) v‖ ^ (2 : ℕ) =
      ‖u - v‖ ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ)
    rw [← dist_eq_norm, dist_lineMap_lineMap, Real.dist_eq, dist_eq_norm, mul_pow, sq_abs]
    rw [show (u - v) ^ (2 : ℕ) = ‖u - v‖ ^ (2 : ℕ) by
      rw [Real.norm_eq_abs, sq_abs]]
    rw [show ‖x - y‖ ^ (2 : ℕ) = ‖y - x‖ ^ (2 : ℕ) by
      simpa using congrArg (fun r : ℝ ↦ r ^ (2 : ℕ)) (norm_sub_rev x y)]
  have hg_strong : StrongConvexOn S m g := by
    refine ⟨hf.1.affine_preimage γ.toAffineMap, ?_⟩
    intro u hu v hv a b ha hb hab
    have hstrong := hf.2 hu hv ha hb hab
    change
      f (a • γ.toAffineMap u + b • γ.toAffineMap v) ≤
        a • f (γ.toAffineMap u) + b • f (γ.toAffineMap v) -
          a * b * ((μ / 2) * ‖γ.toAffineMap u - γ.toAffineMap v‖ ^ (2 : ℕ)) at hstrong
    rw [← Convex.combo_affine_apply hab] at hstrong
    change
      f (γ (a • u + b • v)) ≤
        a • f (γ u) + b • f (γ v) - a * b * ((μ / 2) * ‖γ u - γ v‖ ^ (2 : ℕ)) at hstrong
    have hstrong' :
        f (γ (a • u + b • v)) ≤
          a • f (γ u) + b • f (γ v) - a * b * ((m / 2) * ‖u - v‖ ^ (2 : ℕ)) := by
      rw [hnorm] at hstrong
      dsimp [m] at hstrong ⊢
      ring_nf at hstrong ⊢
      simpa [smul_eq_mul] using hstrong
    simpa [g, hγ_apply] using hstrong'
  have hconv : ConvexOn ℝ S h := by
    simpa [h, g, m, Real.norm_eq_abs, sq_abs, mul_assoc, mul_left_comm, mul_comm] using
      (strongConvexOn_iff_convex.mp hg_strong)
  have h0 : (0 : ℝ) ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have hxQ : Q ∈ 𝓝 (γ (0 : ℝ)) := by
      simpa [hγ_apply] using (mem_interior_iff_mem_nhds.mp hx)
    simpa [S] using γ.continuous.continuousAt.preimage_mem_nhds hxQ
  have h1 : (1 : ℝ) ∈ S := by
    simpa [S, hγ_apply] using hy
  have hderiv_h_le : derivWithin h (Set.Ioi (0 : ℝ)) 0 ≤ slope h 0 1 :=
    hconv.rightDeriv_le_slope_of_mem_interior h0 h1 zero_lt_one
  have hq' : HasDerivWithinAt (fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) (0 : ℝ) (Set.Ioi (0 : ℝ)) 0 := by
    have hq : HasDerivAt (fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) 0 0 := by
      simpa [pow_two] using ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (m / 2)
    exact hq.hasDerivWithinAt
  have hh : DifferentiableWithinAt ℝ h (Set.Ioi (0 : ℝ)) 0 :=
    hconv.differentiableWithinAt_Ioi_of_mem_interior h0
  have hq : DifferentiableWithinAt ℝ (fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) (Set.Ioi (0 : ℝ)) 0 :=
    hq'.differentiableWithinAt
  have hderiv_g_eq_h : derivWithin g (Set.Ioi (0 : ℝ)) 0 = derivWithin h (Set.Ioi (0 : ℝ)) 0 := by
    have hadd := derivWithin_add hq hh
    rw [hq'.derivWithin (uniqueDiffWithinAt_Ioi (0 : ℝ))] at hadd
    have hsumfun : ((fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) + h) = g := by
      funext t
      simp [h, g]
    rw [hsumfun] at hadd
    simpa using hadd
  have hslope : slope h 0 1 = f y - f x - m / 2 := by
    simp [h, g, slope_def_field]
    ring
  have hmain :
      derivWithin (fun t : ℝ ↦ f (x + t • (y - x))) (Set.Ici (0 : ℝ)) 0 ≤
        f y - f x - m / 2 := by
    calc
      derivWithin g (Set.Ici (0 : ℝ)) 0 = derivWithin g (Set.Ioi (0 : ℝ)) 0 := by
        symm
        simpa using derivWithin_Ioi_eq_Ici g (0 : ℝ)
      _ = derivWithin h (Set.Ioi (0 : ℝ)) 0 := hderiv_g_eq_h
      _ ≤ slope h 0 1 := hderiv_h_le
      _ = f y - f x - m / 2 := hslope
  have hm : m / 2 = (μ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    dsimp [m]
    rw [show ‖y - x‖ ^ (2 : ℕ) = ‖x - y‖ ^ (2 : ℕ) by
      simpa using congrArg (fun r : ℝ ↦ r ^ (2 : ℕ)) (norm_sub_rev y x)]
    ring
  linarith [hmain, hm]

end StrongConvexOn

/-! ### Theorem_3_2_3 (from Chap03) -/
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/- Theorem 3.2.3 lies in the chapter's whole-space multi-constraint first-order method domain.

Sampled owner declarations:
* `MultipleConstraintFirstOrderProblem` in `Algorithm_3_4`, the chapter owner for a convex
  objective, a finite constraint family, and chosen first-order oracles;
* `FirstOrderOracle.correctionStepsize` in `Definition_3_40`, the canonical owner-derived scalar
  `f_j(x) / ‖g_j(x)‖²` for a violated-constraint correction;
* `MultipleConstraintFirstOrderProblem.iterates` in `Algorithm_3_4`, the canonical owner-level
  recursion for the whole-space method `(3.2.24)`;
* `FunctionalConstraintSubgradientMethod.iterates` in `Algorithm_3_3` and
  `ProjectedMultipleConstraintFirstOrderProblem.switchingIterates` in `Algorithm_3_4`, the nearby
  chapter pattern that keeps the recursive iterate family public instead of packaging it behind a
  second owner;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the Chapter 1
  owner for intrinsic minimum values over a sampled feasible set.

Best owner abstraction:
* source-facing: the recursive iterate family
  `problem.iterates ε x₀ selectedConstraintAt : ℕ → E` for method `(3.2.24)`;
* core/canonical: `MultipleConstraintFirstOrderProblem`,
  `FirstOrderOracle.correctionStepsize`, `NormedSpace.normalize`, and
  `SetConstrainedMinimizationProblem.optimalValue`;
* bridge/view: the branch-validity predicate for the chosen indices, the admissible index family
  `𝒜(N)`, the sampled iterate set `𝓕_A(N)`, and the sampled optimal value.

Primitive data:
* the multi-constraint first-order owner `problem`;
* the initial point `x₀`;
* the tolerance `ε`;
* the stepwise branch choices `selectedConstraintAt : ℕ → Option (Fin m)`.

Derived API:
* the recursive iterate family `x₀, x₁, ...`;
* the admissibility predicate `∀ j, f_j(x) ≤ ε`;
* the validity condition saying `none` occurs exactly on admissible iterates and `some j`
  records a violated constraint;
* the textbook admissible family `𝒜(N)`, sampled iterate set `𝓕_A(N)`, and sampled minimum.

This refinement removes the public packaged-method owner entirely. The owner-derived whole-space
step and iterate recursion now live in `Algorithm_3_4`, and the theorem surface here works
directly with that canonical run data to derive the branch equations, `𝒜(N)`, `𝓕_A(N)`, and the
sampled minimum. -/

namespace MultipleConstraintFirstOrderProblem

/-- The admissibility predicate at a point: all constraint inequalities satisfy `f_j(x) ≤ ε`. -/
def IsAdmissible
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x : E) : Prop :=
  ∀ j : Fin m, problem.constraints j x ≤ ε

/-- The chosen branch sequence is valid for method `(3.2.24)` exactly when `none` occurs on
admissible iterates and `some j` records a violated constraint. -/
def IsValidSelection
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) : Prop :=
  ∀ k,
    match selectedConstraintAt k with
    | none => problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)
    | some j => ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k)

section Iterates

variable {problem : MultipleConstraintFirstOrderProblem E m}
variable {ε : ℝ} {x0 : E} {selectedConstraintAt : ℕ → Option (Fin m)}

/-- The chosen branch sequence is valid along the recursively generated run. -/
theorem selectedConstraintAt_spec
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (k : ℕ) :
    match selectedConstraintAt k with
    | none => problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)
    | some j => ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) :=
  hvalid k

/-- The branch choice is `none` exactly on admissible iterates. -/
theorem selectedConstraintAt_eq_none_iff
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (k : ℕ) :
    selectedConstraintAt k = none ↔
      problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k) := by
  constructor
  · intro hk
    simpa [hk] using problem.selectedConstraintAt_spec hvalid k
  · intro hk
    cases hsel : selectedConstraintAt k with
    | none =>
        rfl
    | some j =>
        have hviol : ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) := by
          simpa [hsel] using problem.selectedConstraintAt_spec hvalid k
        exact (not_lt_of_ge (hk j) hviol).elim

/-- The zeroth iterate is the prescribed initial point `x₀`. -/
@[simp] theorem iterates_zero :
    problem.iterates ε x0 selectedConstraintAt 0 = x0 := by
  rfl

/-- Each successor iterate is obtained from the previous one by the branch rule of
method `(3.2.24)`. -/
@[simp] theorem iterates_succ (k : ℕ) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.step ε (problem.iterates ε x0 selectedConstraintAt k)
        (selectedConstraintAt k) := by
  rfl

/-- At admissible iterates, the successor iterate is the objective step. -/
theorem iterates_succ_eq_objective
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) {k : ℕ}
    (hk : problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.objectiveStep ε (problem.iterates ε x0 selectedConstraintAt k) := by
  have hsel : selectedConstraintAt k = none :=
    (problem.selectedConstraintAt_eq_none_iff hvalid k).2 hk
  rw [iterates_succ, hsel]
  rfl

/-- If the run selects the violated constraint `j` at time `k`, the successor iterate is the
corresponding correction step. -/
theorem iterates_succ_eq_constraint
    {k : ℕ} {j : Fin m} (hsel : selectedConstraintAt k = some j) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.constraintStep j (problem.iterates ε x0 selectedConstraintAt k) := by
  rw [iterates_succ, hsel]
  rfl

/-- The textbook index set `𝒜(N)` of admissible iterates among `x₀, ..., x_N`. -/
def admissibleIndices
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun k ↦
    problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)

namespace MultipleConstraintFirstOrderProblemNotation

scoped notation:max "𝒜[" problem:arg ", " ε:arg ", " x0:arg ", " selected:arg "](" N:arg ")" =>
  admissibleIndices problem ε x0 selected N

end MultipleConstraintFirstOrderProblemNotation

open scoped MultipleConstraintFirstOrderProblemNotation

/-- Membership in `𝒜(N)` is equivalent to satisfying all constraint inequalities
`f_j(x_k) ≤ ε`. -/
@[simp] theorem mem_admissibleIndices_iff
    (N : ℕ) {k : Fin (N + 1)} :
    k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ↔
      ∀ j, problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) ≤ ε := by
  simp [admissibleIndices, IsAdmissible]

/-- The textbook set `𝓕_A(N)` of iterates whose indices belong to `𝒜(N)`. -/
def admissibleIterateSet
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) :
    Set E :=
  Set.range fun k : {i : Fin (N + 1) // i ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N)} ↦
    problem.iterates ε x0 selectedConstraintAt k.1

namespace MultipleConstraintFirstOrderProblemNotation

scoped notation:max "𝓕_A[" problem:arg ", " ε:arg ", " x0:arg ", " selected:arg "](" N:arg ")" =>
  admissibleIterateSet problem ε x0 selected N

end MultipleConstraintFirstOrderProblemNotation

/-- The sampled minimum on `𝓕_A(N)`, expressed through the Chapter 1 constrained optimal-value
owner. -/
def sampledOptimalValue
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) : EReal :=
  (SetConstrainedMinimizationProblem.mk
      (𝓕_A[problem, ε, x0, selectedConstraintAt](N))
      problem.objective).optimalValue

/-- Membership in `𝓕_A(N)` means that the point is one of the iterates `x_k` with
`k ∈ 𝒜(N)`. -/
theorem mem_admissibleIterateSet_iff
    (N : ℕ) {x : E} :
    x ∈ 𝓕_A[problem, ε, x0, selectedConstraintAt](N) ↔
      ∃ k : Fin (N + 1),
        k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ∧
          problem.iterates ε x0 selectedConstraintAt k = x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/-- The admissible iterate set is nonempty exactly when the admissible index family `𝒜(N)` is
nonempty. -/
theorem admissibleIterateSet_nonempty_iff
    (N : ℕ) :
    𝓕_A[problem, ε, x0, selectedConstraintAt](N) ≠ ∅ ↔
      (𝒜[problem, ε, x0, selectedConstraintAt](N)).Nonempty := by
  constructor
  · intro hSet
    rcases Set.range_nonempty_iff_nonempty.mp
        (Set.nonempty_iff_ne_empty.mpr hSet) with ⟨k⟩
    exact ⟨k.1, k.2⟩
  · rintro ⟨k, hk⟩ hEmpty
    have hx : problem.iterates ε x0 selectedConstraintAt k ∈
        𝓕_A[problem, ε, x0, selectedConstraintAt](N) := by
      exact Set.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
    rw [hEmpty] at hx
    exact hx

-- Proof sketch: argue by contradiction. If every iterate up to time `N` either violates a
-- constraint by more than `ε` or has objective gap larger than `ε`, then each step of method
-- `(3.2.24)` decreases `‖x_k - x*‖²` by at least `ε² / M²`. Summing the drop over
-- `k = 0, ..., N` contradicts the bound `N ≥ (M² / ε²) ‖x₀ - x*‖²`, so some admissible iterate
-- must satisfy the desired objective estimate, which then bounds the sampled minimum.
/-- Theorem 3.2.3: let `x_k = problem.iterates ε x₀ selectedConstraintAt k` be the recursively
generated run of method `(3.2.24)`. If the branch choices are valid, if the objective `f` and
the constraint functions `f_j`, `j = 1, ..., m`, are `M`-Lipschitz on the ball
`B₂(x*, ‖x₀ - x*‖)`, if `x*` is optimal for the constrained feasible set
`{x | ∀ j, f_j(x) ≤ 0}`, and if the number of steps satisfies
`N ≥ (M² / ε²) ‖x₀ - x*‖²`, then the admissible index family `𝒜(N)` is nonempty, hence
`𝓕_A(N)` is nonempty, and the sampled minimum on `𝓕_A(N)` satisfies
`f_N^* ≤ f(x*) + ε`. -/
theorem admissibleIterateSet_nonempty_and_sampledMinimum_le_optimal_add_eps
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hxStar_optimal :
      IsMinOn problem.objective {x | ∀ j, problem.constraints j x ≤ 0} xStar)
    (N : ℕ)
    (hN :
      (((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
        (N : ℝ)) :
    (𝒜[problem, ε, x0, selectedConstraintAt](N)).Nonempty ∧
      𝓕_A[problem, ε, x0, selectedConstraintAt](N) ≠ ∅ ∧
        problem.sampledOptimalValue ε x0 selectedConstraintAt N ≤
          problem.objective xStar + ε := sorry

end Iterates

end MultipleConstraintFirstOrderProblem

end

/-! ### Corollary_3_2_4 (from Chap03) -/
/-
Corollary 3.2.4 lives in the localization-radius / ellipsoid-volume domain.

Sampled owner declarations:
- `localization_radius` and `localization_radius_le_outer_radius_mul_volume_ratio_rpow`
  from `Theorem_3_2_9`
- `inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex` from `Theorem_3_51`
- `selected_radius_bound_of_positive_index` and `selected_index_pos_of_volume_drop`
  from `Theorem_3_52`

Owner abstraction:
- the chapter localization-radius API, with `Theorem_3_52` as the selected-index bridge.

Primitive data:
- `Q`, the raw query sequence `querySeq`, the localization map `g`, the comparison sequence
  `Ell`, and the owner selected-index data `Nat.count` / `Nat.nth`.

Derived API:
- the corollary's two source-facing conclusions are already exactly the bridge theorems from
  `Theorem_3_52`, so adding local copies here would only duplicate API.

Triage:
- source-facing: the selected-stage radius bound and positivity of
  `Nat.count (fun j ↦ querySeq j ∈ Q) k`
- core/canonical: the localization-radius bound from `Theorem_3_2_9`
- bridge/view: the selected-index specialization from `Theorem_3_52`

This file therefore keeps Corollary 3.2.4 as direct canonical recalls and adds no parallel
wrapper theorems.
-/

recall selected_radius_bound_of_positive_index

recall selected_index_pos_of_volume_drop

/-! ### Lemma_3_2_4 (from Chap03) -/
noncomputable section

open FeasibilityResistingOracleState
open Lean Elab Tactic Meta

variable {n : ℕ}

/-
Lemma 3.2.4 lies in the midpoint-bisection box / Euclidean inradius domain.

Primary mathematical domain:
- recursively generated axis-aligned boxes in `ℝⁿ` and the Euclidean closed balls centered at
  their midpoints.

Sampled owner-style declarations:
- `FeasibilityResistingOracleState.currentBox` and
  `FeasibilityResistingOracleState.currentCenter` in `Algorithm_3_5`, the chapter owner
  declarations for the realized box and its midpoint at a given stage;
- `IsMidpointCoordinateBisectionStep` and
  `generated_box_side_lengths_eq_half_after_n_steps` in `Proposition_3_43`, the canonical
  midpoint-bisection geometry controlling the side lengths of those boxes;
- mathlib `Metric.closedBall`, the ambient Euclidean closed-ball owner;
- mathlib `Nat.cast_div_le` and `Real.rpow_le_rpow_of_exponent_ge'`, the canonical comparison
  between the cyclewise integer-division exponent and the textbook real exponent.

Best owner abstraction:
- source-facing: the current realized box `state.currentBox R hn` and its midpoint
  `state.currentCenter R hn`;
- core/canonical: the box recursion owned by `FeasibilityResistingOracleState` together with the
  side-length control supplied by `Proposition_3_43`;
- bridge/view: the passage from the stronger cyclewise exponent `state.depth / n : ℕ` to the
  textbook real exponent `((state.depth : ℝ) / n)`.

Primitive data:
- the outer scale `R`
- the positive dimension witness `hn : 0 < n`
- the resisting-oracle transcript `state : FeasibilityResistingOracleState n`

Derived API:
- the source-facing inclusion of the textbook Euclidean ball in the current realized box.

Source/core/bridge triage:
- source-facing: the textbook inclusion
  `B₂(state.currentCenter R hn, (R / 2) * (1 / 2)^(state.depth / n)) ⊆ state.currentBox R hn`;
- core/canonical: the midpoint-bisection owner API in `Algorithm_3_5`;
- bridge/view: the radius comparison from the stronger cyclewise radius
  `(R / 2) * (1 / 2)^(state.depth / n : ℕ)` to the textbook radius with real exponent.

The previous version erased the actual box owner and proved only a generic consequence from an
assumed stronger inclusion. This refinement restores the source-facing statement directly on the
chapter's box owner instead of keeping an arbitrary-family wrapper as the main public theorem.
-/

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the cyclic split index is the remainder of the
current depth modulo `n`. -/
lemma nextCoord_eq_depth_mod
    (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.nextCoord hn = ⟨state.depth % n, Nat.mod_lt _ hn⟩ := by
  induction state with
  | initial =>
      -- The initial transcript starts with the first coordinate.
      apply Fin.ext
      simp [FeasibilityResistingOracleState.nextCoord, FeasibilityResistingOracleState.depth]
  | keepLowerHalf state ih =>
      -- One more split advances the cyclic coordinate by one.
      apply Fin.ext
      simp [FeasibilityResistingOracleState.nextCoord, FeasibilityResistingOracleState.depth,
        FeasibilityResistingOracleState.nextCoordinateIndex, ih, Fin.val_add, Nat.add_mod]
  | keepUpperHalf state ih =>
      -- The upper-half branch advances the cyclic coordinate in the same way.
      apply Fin.ext
      simp [FeasibilityResistingOracleState.nextCoord, FeasibilityResistingOracleState.depth,
        FeasibilityResistingOracleState.nextCoordinateIndex, ih, Fin.val_add, Nat.add_mod]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder does not wrap around,
adding one step does not change the quotient `depth / n`. -/
lemma succ_div_eq_div_of_remainder_succ_lt
    {d n : ℕ} (hn : 0 < n) (hrem : d % n + 1 < n) :
    (d + 1) / n = d / n := by
  -- The non-wrap case means the new remainder is still nonzero.
  have hmod_ne : (d + 1) % n ≠ 0 := by
    have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod, hone, Nat.mod_eq_of_lt hrem]
    omega
  simpa using Nat.succ_div_of_mod_ne_zero hmod_ne

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder wraps around, adding one
step increases the quotient `depth / n` by one. -/
lemma succ_div_eq_div_add_one_of_remainder_succ_ge
    {d n : ℕ} (hn : 0 < n) (hrem : ¬ d % n + 1 < n) :
    (d + 1) / n = d / n + 1 := by
  -- Wrapping means the new remainder is exactly `0`.
  have hmod_zero : (d + 1) % n = 0 := by
    have hlt : d % n < n := Nat.mod_lt _ hn
    have hEq : d % n + 1 = n := by
      omega
    rw [Nat.add_mod]
    by_cases h1 : n = 1
    · subst h1
      omega
    · have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hone, hEq]
      simp
  simpa using Nat.succ_div_of_mod_eq_zero hmod_zero

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder does not wrap around,
the next remainder is exactly one larger. -/
lemma succ_mod_eq_remainder_succ_of_remainder_succ_lt
    {d n : ℕ} (hn : 0 < n) (hrem : d % n + 1 < n) :
    (d + 1) % n = d % n + 1 := by
  -- This is the remainder update in the non-wrap case.
  have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.add_mod, hone, Nat.mod_eq_of_lt hrem]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: if the current remainder wraps around, the next
remainder is `0`. -/
lemma succ_mod_eq_zero_of_remainder_succ_ge
    {d n : ℕ} (hn : 0 < n) (hrem : ¬ d % n + 1 < n) :
    (d + 1) % n = 0 := by
  -- Wrapping closes one full cycle of `n` coordinate splits.
  have hlt : d % n < n := Nat.mod_lt _ hn
  have hEq : d % n + 1 = n := by
    omega
  rw [Nat.add_mod]
  by_cases h1 : n = 1
  · subst h1
    omega
  · have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hone, hEq]
    simp

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: in one lower-half step, only the selected
coordinate width is halved. -/
lemma keepLowerHalf_width_eq_update
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepLowerHalf state).currentUpper R hn -
      (FeasibilityResistingOracleState.keepLowerHalf state).currentLower R hn =
        Function.update
          (state.currentUpper R hn - state.currentLower R hn)
          (state.nextCoord hn)
          ((state.currentUpper R hn (state.nextCoord hn) -
            state.currentLower R hn (state.nextCoord hn)) / 2) := by
  -- This is exactly the midpoint-bisection side-length update theorem.
  simpa using midpointCoordinateBisectionStep_sideLengths_eq_update
    (state.keepLowerHalf_isMidpointCoordinateBisectionStep (R := R) (hn := hn))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: coordinatewise form of the lower-half width
update. -/
lemma keepLowerHalf_width_eq_if
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    (FeasibilityResistingOracleState.keepLowerHalf state).currentUpper R hn i -
      (FeasibilityResistingOracleState.keepLowerHalf state).currentLower R hn i =
        if i = state.nextCoord hn then
          (state.currentUpper R hn i - state.currentLower R hn i) / 2
        else
          state.currentUpper R hn i - state.currentLower R hn i := by
  -- Evaluate the update at coordinate `i`.
  have hfun := congrFun (keepLowerHalf_width_eq_update R hn state) i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    simpa using hfun
  · simpa [hi] using hfun

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: in one upper-half step, only the selected
coordinate width is halved. -/
lemma keepUpperHalf_width_eq_update
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepUpperHalf state).currentUpper R hn -
      (FeasibilityResistingOracleState.keepUpperHalf state).currentLower R hn =
        Function.update
          (state.currentUpper R hn - state.currentLower R hn)
          (state.nextCoord hn)
          ((state.currentUpper R hn (state.nextCoord hn) -
            state.currentLower R hn (state.nextCoord hn)) / 2) := by
  -- The upper-half branch has the same side-length update.
  simpa using midpointCoordinateBisectionStep_sideLengths_eq_update
    (state.keepUpperHalf_isMidpointCoordinateBisectionStep (R := R) (hn := hn))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: coordinatewise form of the upper-half width
update. -/
lemma keepUpperHalf_width_eq_if
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    (FeasibilityResistingOracleState.keepUpperHalf state).currentUpper R hn i -
      (FeasibilityResistingOracleState.keepUpperHalf state).currentLower R hn i =
        if i = state.nextCoord hn then
          (state.currentUpper R hn i - state.currentLower R hn i) / 2
        else
          state.currentUpper R hn i - state.currentLower R hn i := by
  -- Evaluate the update at coordinate `i`.
  have hfun := congrFun (keepUpperHalf_width_eq_update R hn state) i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    simpa using hfun
  · simpa [hi] using hfun

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: after `depth / n` full coordinate cycles, each
side length is either the cycle radius `R * 2^{-⌊depth / n⌋}` or twice that value, depending on
whether this coordinate has already been visited in the current partial cycle. -/
lemma current_side_length_profile
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    state.currentUpper R hn i - state.currentLower R hn i =
      if i.1 < state.depth % n then
        R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ))
      else
        2 * R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) := by
  induction state generalizing i with
  | initial =>
      -- Initially every side length is exactly `2R`.
      have hbase :
          (FeasibilityResistingOracleState.initial : FeasibilityResistingOracleState n).currentUpper
              R hn i -
            (FeasibilityResistingOracleState.initial : FeasibilityResistingOracleState n).currentLower
              R hn i =
            2 * R := by
        change R - (-R) = 2 * R
        ring
      simpa [FeasibilityResistingOracleState.depth] using hbase
  | keepLowerHalf state ih =>
      -- A lower-half step either preserves a width or halves the currently selected width.
      rw [keepLowerHalf_width_eq_if]
      have hnext : (state.nextCoord hn).1 = state.depth % n := by
        simpa using congrArg Fin.val (nextCoord_eq_depth_mod hn state)
      by_cases hrem : state.depth % n + 1 < n
      · have hdiv : (state.depth + 1) / n = state.depth / n :=
            succ_div_eq_div_of_remainder_succ_lt hn hrem
        have hmod : (state.depth + 1) % n = state.depth % n + 1 :=
            succ_mod_eq_remainder_succ_of_remainder_succ_lt hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hine : i.1 ≠ state.depth % n := by
            intro hieq
            apply hi
            apply Fin.ext
            simpa [hnext] using hieq
          by_cases hir : i.1 < state.depth % n
          · have hir' : i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
          · have hir' : ¬ i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
      · have hdiv : (state.depth + 1) / n = state.depth / n + 1 :=
            succ_div_eq_div_add_one_of_remainder_succ_ge hn hrem
        have hmod : (state.depth + 1) % n = 0 :=
            succ_mod_eq_zero_of_remainder_succ_ge hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hir : i.1 < state.depth % n := by
            have hlt : i.1 < n := i.2
            have hstate : state.depth % n + 1 = n := by
              have hlt' : state.depth % n < n := Nat.mod_lt _ hn
              omega
            have hine : i.1 ≠ state.depth % n := by
              intro hieq
              apply hi
              apply Fin.ext
              simpa [hnext] using hieq
            omega
          simp [FeasibilityResistingOracleState.depth, hir, hdiv, hmod]
          ring_nf
  | keepUpperHalf state ih =>
      -- The upper-half branch obeys the same cyclic side-length profile.
      rw [keepUpperHalf_width_eq_if]
      have hnext : (state.nextCoord hn).1 = state.depth % n := by
        simpa using congrArg Fin.val (nextCoord_eq_depth_mod hn state)
      by_cases hrem : state.depth % n + 1 < n
      · have hdiv : (state.depth + 1) / n = state.depth / n :=
            succ_div_eq_div_of_remainder_succ_lt hn hrem
        have hmod : (state.depth + 1) % n = state.depth % n + 1 :=
            succ_mod_eq_remainder_succ_of_remainder_succ_lt hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hine : i.1 ≠ state.depth % n := by
            intro hieq
            apply hi
            apply Fin.ext
            simpa [hnext] using hieq
          by_cases hir : i.1 < state.depth % n
          · have hir' : i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
          · have hir' : ¬ i.1 < (state.depth + 1) % n := by
              rw [hmod]
              omega
            simp [FeasibilityResistingOracleState.depth, hir, hir', hdiv]
      · have hdiv : (state.depth + 1) / n = state.depth / n + 1 :=
            succ_div_eq_div_add_one_of_remainder_succ_ge hn hrem
        have hmod : (state.depth + 1) % n = 0 :=
            succ_mod_eq_zero_of_remainder_succ_ge hn hrem
        by_cases hi : i = state.nextCoord hn
        · subst hi
          rw [if_pos rfl, ih]
          simp [FeasibilityResistingOracleState.depth, hnext, hdiv, hmod]
          ring_nf
        · rw [if_neg hi, ih]
          have hir : i.1 < state.depth % n := by
            have hlt : i.1 < n := i.2
            have hstate : state.depth % n + 1 = n := by
              have hlt' : state.depth % n < n := Nat.mod_lt _ hn
              omega
            have hine : i.1 ≠ state.depth % n := by
              intro hieq
              apply hi
              apply Fin.ext
              simpa [hnext] using hieq
            omega
          simp [FeasibilityResistingOracleState.depth, hir, hdiv, hmod]
          ring_nf

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: every current side length is at least the
cyclewise scale `R * 2^{-⌊depth / n⌋}` when `R` is nonnegative. -/
lemma current_side_length_ge_cycle_scale
    (R : ℝ) (hR : 0 ≤ R) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) ≤
      state.currentUpper R hn i - state.currentLower R hn i := by
  -- The profile theorem shows the width is either one or two copies of the cyclewise scale.
  have hprofile := current_side_length_profile (R := R) (hn := hn) (state := state) (i := i)
  rw [hprofile]
  by_cases hir : i.1 < state.depth % n
  · simp [hir]
  · simp [hir]
    nlinarith

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: every coordinate of a Euclidean vector is bounded
in absolute value by the ambient Euclidean norm. -/
lemma abs_coordinate_le_norm (v : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    |v j| ≤ ‖v‖ := by
  -- Re-express the chosen coordinate as an inner product against the standard basis vector.
  have hinner : inner ℝ v (EuclideanSpace.single j (1 : ℝ)) = v j := by
    simpa using EuclideanSpace.inner_single_right j (1 : ℝ) v
  calc
    |v j| = |inner ℝ v (EuclideanSpace.single j (1 : ℝ))| := by
      rw [hinner]
    _ ≤ ‖v‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by
      simp [EuclideanSpace.single]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: a coordinate box whose every side length is at
least `2ρ` contains the Euclidean closed ball of radius `ρ` centered at its midpoint. -/
lemma closedBall_subset_box_of_halfwidth_le
    {a b : Fin n → ℝ} {ρ : ℝ}
    (hwidth : ∀ i, 2 * ρ ≤ b i - a i) :
    Metric.closedBall ((EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) ρ ⊆
      {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, a i ≤ x i ∧ x i ≤ b i} := by
  intro x hx i
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  -- Control the `i`-th coordinate displacement by the ambient Euclidean norm.
  have hcoord :
      |x i - ((EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) i| ≤ ρ := by
    have hcoord_norm :=
      abs_coordinate_le_norm
        (v := x - (EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) i
    simpa using le_trans hcoord_norm hx
  have hmid :
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (midpoint ℝ a b)) i = (a i + b i) / 2 := by
    simp [midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul]
    ring
  have hhalf : ρ ≤ (b i - a i) / 2 := by
    linarith [hwidth i]
  have habs : |x i - (a i + b i) / 2| ≤ (b i - a i) / 2 := by
    rw [hmid] at hcoord
    exact le_trans hcoord hhalf
  have habs' := abs_le.mp habs
  constructor <;> nlinarith

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the textbook real-exponent radius is no larger
than the stronger cyclewise radius with exponent `depth / n : ℕ`. -/
lemma textbook_radius_le_cycle_radius
    (R : ℝ) (hR : 0 ≤ R) (state : FeasibilityResistingOracleState n) :
    (R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) ≤
      (R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) := by
  -- The base `1 / 2` lies in `(0, 1)`, so larger exponents give smaller radii.
  have hdiv : (state.depth / n : ℕ) ≤ (state.depth : ℝ) / n := by
    simpa using (Nat.cast_div_le (m := state.depth) (n := n) :
      ((state.depth / n : ℕ) : ℝ) ≤ (state.depth : ℝ) / n)
  have hrpow :
      Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) ≤
        Real.rpow (1 / 2 : ℝ) (state.depth / n : ℕ) := by
    refine Real.rpow_le_rpow_of_exponent_ge' ?_ ?_ ?_ hdiv
    · norm_num
    · norm_num
    · positivity
  have hR2 : 0 ≤ R / 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hrpow hR2
  simpa [Real.rpow_natCast] using hmul

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: unfold the private lower-bound owners from
Algorithm 3.5 so the last stored lower corner reduces definitionally. -/
elab "unfold_oracle_lower_bound_owners" : tactic => do
  let privateRoot := Name.str Name.anonymous "_private"
  let privateRoot := Name.str privateRoot "LecturesConvexOptimization_Nesterov_2018"
  let privateRoot := Name.str privateRoot "Chap03"
  let privateRoot := Name.str privateRoot "Algorithm_3_5"
  let privateRoot := Name.num privateRoot 0
  let stateNs := Name.str privateRoot "FeasibilityResistingOracleState"
  let names : Array Name := #[
    ``FeasibilityResistingOracleState.lower,
    ``FeasibilityResistingOracleState.currentLower,
    Name.str stateNs "realizedBounds",
    Name.str stateNs "currentBounds",
    Name.str (Name.str stateNs "BoxBounds") "lower"
  ]
  let stxNames : Array (TSyntax `ident) := names.map mkIdent
  evalTactic (← `(tactic| unfold $[$stxNames]*))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: unfold the private upper-bound owners from
Algorithm 3.5 so the last stored upper corner reduces definitionally. -/
elab "unfold_oracle_upper_bound_owners" : tactic => do
  let privateRoot := Name.str Name.anonymous "_private"
  let privateRoot := Name.str privateRoot "LecturesConvexOptimization_Nesterov_2018"
  let privateRoot := Name.str privateRoot "Chap03"
  let privateRoot := Name.str privateRoot "Algorithm_3_5"
  let privateRoot := Name.num privateRoot 0
  let stateNs := Name.str privateRoot "FeasibilityResistingOracleState"
  let names : Array Name := #[
    ``FeasibilityResistingOracleState.upper,
    ``FeasibilityResistingOracleState.currentUpper,
    Name.str stateNs "realizedBounds",
    Name.str stateNs "currentBounds",
    Name.str (Name.str stateNs "BoxBounds") "upper"
  ]
  let stxNames : Array (TSyntax `ident) := names.map mkIdent
  evalTactic (← `(tactic| unfold $[$stxNames]*))

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the last stored realized lower corner is exactly
the owner-level current lower corner. -/
lemma lower_last_eq_currentLower
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.lower R hn (Fin.last state.depth) = state.currentLower R hn := by
  -- Unfold the private recursive owners so the last stored lower corner becomes explicit.
  ext i
  unfold_oracle_lower_bound_owners
  -- Each constructor records the current lower corner in the newest transcript slot.
  cases state <;> simp [Fin.lastCases_last, FeasibilityResistingOracleState.depth]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the last stored realized upper corner is exactly
the owner-level current upper corner. -/
lemma upper_last_eq_currentUpper
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.upper R hn (Fin.last state.depth) = state.currentUpper R hn := by
  -- Unfold the private recursive owners so the last stored upper corner becomes explicit.
  ext i
  unfold_oracle_upper_bound_owners
  -- Each constructor records the current upper corner in the newest transcript slot.
  cases state <;> simp [Fin.lastCases_last, FeasibilityResistingOracleState.depth]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the owner `currentCenter` agrees with the
midpoint of the current lower and upper coordinate bounds. -/
lemma currentCenter_eq_midpoint_currentBounds
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.currentCenter R hn =
      (EuclideanSpace.equiv (Fin n) ℝ).symm
        (midpoint ℝ (state.currentLower R hn) (state.currentUpper R hn)) := by
  -- Rewrite the last stored realized box into the owner-level current coordinate bounds.
  rw [FeasibilityResistingOracleState.currentCenter.eq_1, FeasibilityResistingOracleState.center]
  rw [lower_last_eq_currentLower, upper_last_eq_currentUpper]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the owner `currentBox` agrees with the coordinate
box cut out by `currentLower` and `currentUpper`. -/
lemma currentBox_eq_currentBounds_set
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.currentBox R hn =
      {x : EuclideanSpace ℝ (Fin n) |
        ∀ i : Fin n, state.currentLower R hn i ≤ x i ∧ x i ≤ state.currentUpper R hn i} := by
  -- Rewrite the last stored realized box inequalities into the owner-level current bounds.
  ext x
  simp [FeasibilityResistingOracleState.currentBox.eq_1, FeasibilityResistingOracleState.box,
    lower_last_eq_currentLower, upper_last_eq_currentUpper]

/-- Helper for Lemma 3.2.4 [Chapter3_4.json:81]: the stronger cyclewise-radius closed ball is
already contained in the current box. -/
lemma cycle_radius_ball_subset_currentBox
    (R : ℝ) (hR : 0 ≤ R) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    Metric.closedBall (state.currentCenter R hn)
        ((R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ))) ⊆
      state.currentBox R hn := by
  let ρ := (R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ))
  have hwidth :
      ∀ i : Fin n, 2 * ρ ≤ state.currentUpper R hn i - state.currentLower R hn i := by
    intro i
    have hside := current_side_length_ge_cycle_scale (R := R) (hR := hR) (hn := hn)
      (state := state) (i := i)
    calc
      2 * ρ = R * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) := by
        dsimp [ρ]
        ring
      _ ≤ state.currentUpper R hn i - state.currentLower R hn i := hside
  -- Convert the generic midpoint-ball inclusion to the chapter's owner API.
  rw [currentCenter_eq_midpoint_currentBounds, currentBox_eq_currentBounds_set]
  exact closedBall_subset_box_of_halfwidth_le hwidth

/-- Lemma 3.2.4 [Chapter3_4.json:81]: every realized midpoint-bisection box in the chapter's
resisting-oracle construction contains the Euclidean closed ball centered at its midpoint with
textbook radius `r_k = (R / 2) * (1 / 2)^(k / n)`, where `k = state.depth`; this is the geometric
containment lemma that immediately yields the subsequent complexity result. -/
-- Proof sketch: write `state.depth = n * l + p` with `p < n`. The midpoint-bisection owner in
-- `Algorithm_3_5`, together with `generated_box_side_lengths_eq_half_after_n_steps`, shows that
-- each side length of `state.currentBox R hn` is at least `R * (1 / 2)^l`, so the stronger
-- cyclewise-radius ball of radius `(R / 2) * (1 / 2)^l` around `state.currentCenter R hn` lies in
-- the box. Since `l = state.depth / n : ℕ` and `l ≤ state.depth / n` in `ℝ`, the base
-- `1 / 2 ∈ (0, 1)` makes the textbook radius no larger than that cyclewise radius, yielding the
-- displayed inclusion by closed-ball monotonicity.
theorem FeasibilityResistingOracleState.closedBall_subset_currentBox
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    Metric.closedBall (state.currentCenter R hn)
        ((R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n)) ⊆
      state.currentBox R hn := by
  -- Route correction: the proof follows the source's cyclewise side-length invariant first, and
  -- only then converts that stronger radius to the textbook `Real.rpow` radius.
  by_cases hR : 0 ≤ R
  · have hrad :
        (R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) ≤
          (R / 2) * ((1 / 2 : ℝ) ^ (state.depth / n : ℕ)) :=
        textbook_radius_le_cycle_radius (R := R) hR state
    exact Set.Subset.trans
      (Metric.closedBall_subset_closedBall hrad)
      (cycle_radius_ball_subset_currentBox (R := R) hR hn state)
  · have hR2neg : R / 2 < 0 := by
      nlinarith
    have hrpow_pos : 0 < Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hrad_neg :
        (R / 2) * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) < 0 :=
      mul_neg_of_neg_of_pos hR2neg hrpow_pos
    rw [Metric.closedBall_eq_empty.2 hrad_neg]
    simp

end

/-! ### Theorem_3_2_4 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

namespace MultipleConstraintFirstOrderProblem

private def subgradientNormFamily
    (problem : MultipleConstraintFirstOrderProblem E m) : Fin (m + 1) → E → ℝ :=
  Fin.cases
    (fun y ↦ ‖problem.oracle.subgradient y‖)
    (fun j y ↦ ‖(problem.constraintOracle j).subgradient y‖)

/-- The canonical finite-family maximum of the objective-subgradient norm together with all
constraint-subgradient norms at `x`. -/
def subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) : ℝ :=
  maxTypeObjective (subgradientNormFamily problem) x

/-- Each sampled objective-subgradient norm is bounded by the problem-level maximum
`subgradientNormMaximum`. -/
theorem objectiveSubgradientNorm_le_subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) :
    ‖problem.oracle.subgradient x‖ ≤ problem.subgradientNormMaximum x := by
  rw [subgradientNormMaximum, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun i : Fin (m + 1) ↦ subgradientNormFamily problem i x)
      (Finset.mem_univ 0))

/-- Each sampled constraint-subgradient norm is bounded by the problem-level maximum
`subgradientNormMaximum`. -/
theorem constraintSubgradientNorm_le_subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) (j : Fin m) :
    ‖(problem.constraintOracle j).subgradient x‖ ≤ problem.subgradientNormMaximum x := by
  rw [subgradientNormMaximum, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun i : Fin (m + 1) ↦ subgradientNormFamily problem i x)
      (Finset.mem_univ (Fin.succ j)))

end MultipleConstraintFirstOrderProblem

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/- Theorem 3.2.4 lies in the chapter's approximate-Lagrange-multiplier switching-method domain.

Sampled owner-style declarations:
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintIndices`
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintCount`
- `ApproximateLagrangeMultiplierSwitchingMethod.primalDualGapQuantity`
- `MultipleConstraintFirstOrderProblem.subgradientNormMaximum`
- `maxTypeObjective` in `Chap02/Lemma_2_18`
- mathlib `Finset.sup'` on finite sampled scalar families

Best owner abstraction:
- a run `method : ApproximateLagrangeMultiplierSwitchingMethod problem`
- the project finite-family maximum owner `maxTypeObjective`

Primitive data:
- the switching-method run `method`
- the radius `R`, the stage `t`, the bounded-feasible-set hypothesis, and the
  large-iteration hypothesis

Derived API:
- the residual maximum `maxTypeObjective problem.constraints (method k)`, given directly by the
  Chapter 2 finite-family maximum owner
- the problem-owned norm envelope
  `problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum`
- the sampled norm bound `M[method](t)`, owned by `sampleMaxSubgradientNorm` and derived as the
  finite operational maximum of that owner quantity along the sampled iterates `k = 0, ..., t`
- the source gap estimate written directly for the owner
  `primalDualGapQuantity`

Source/core/bridge triage:
- source-facing: the textbook residual bound, the positivity of `N(t)`, and the
  gap estimate for `δ_t` in the source regime `S_t > 0`
- core/canonical: `inactiveConstraintCount`, `normalizingFactor`,
  `approximateDualMultiplier`, `primalDualGapQuantity`, the finite-family maximum owner
  `maxTypeObjective`, and the finite-fold owner `Finset.sup'`
- bridge/view: the direct `Fin m` specialization `maxTypeObjective problem.constraints (method k)`

The old file duplicated the run data and left `δ_t` as arbitrary primitive data.
This refinement keeps the source-facing quantities, but derives them from the chapter owner run,
the chapter's canonical finite-family maximum surface for the constraint residual, the canonical
finite-fold sampled maximum for the textbook bound `M[method](t)`, and the existing gap owner
`primalDualGapQuantity`. -/

/-- Theorem 3.2.4: if `0 < h`, the feasible set is contained in the ball `‖x - x₀‖ ≤ R`, and
`t > R² / h²`, then the number `N(t)` of objective-step indices among `{0, ..., t}` is
positive. -/
theorem positive_inactiveConstraintCount_of_large_iteration_count
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    0 < N[method](t) := sorry

section ConstraintMaxima

/-- The sampled norm bound
`M = max_{0 ≤ k ≤ t} max {‖g(x_k)‖, ‖g₁(x_k)‖, ..., ‖g_m(x_k)‖}`. -/
def sampleMaxSubgradientNorm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k : Fin (t + 1) ↦
    problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k)

/- Source-facing Lean notation for the textbook sampled norm bound `M`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "M[" method:arg "](" t:arg ")" =>
  sampleMaxSubgradientNorm method t

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

private theorem stageMax_le_sampleMaxSubgradientNorm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {t : ℕ} (k : Fin (t + 1)) :
    problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k) ≤
      M[method](t) := by
  unfold sampleMaxSubgradientNorm
  exact
    Finset.le_sup'
      (fun i : Fin (t + 1) ↦
        problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method i))
      (Finset.mem_univ k)

/-- Companion bridge for the textbook residual estimate: every objective-step iterate up to time
`t` satisfies the componentwise bound `f_j(x_k) ≤ M h` for each constraint index `j`, where
`0 < h` and `M = M[method](t)`. -/
-- Proof sketch: on indices in `A₀(t)`, the switching active set is empty, so each constraint
-- value is bounded by the corresponding threshold `h ‖g_j(x_k)‖`. The sampled norm bound
-- `M[method](t)` dominates the owner quantity
-- `problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k)` at every
-- sampled stage up to time `t`, hence every sampled constraint-subgradient norm, so the desired
-- inequality follows for each fixed `j`.
theorem constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hh : 0 < method.h)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) (j : Fin m) :
    problem.constraints j (method k) ≤ M[method](t) * method.h := by
  have hactive : method.activeSet k = ∅ :=
    (mem_inactiveConstraintIndices_iff method t).1 hk
  have hconstraint :
      problem.constraints j (method k) ≤
        method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := by
    exact le_of_not_gt fun hj ↦ by
      have hj_mem : j ∈ method.activeSet k := by
        simp [ApproximateLagrangeMultiplierSwitchingMethod.activeSet,
          ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet, hj]
      simp [hactive] at hj_mem
  have hnorm :
      ‖(problem.constraintOracle j).subgradient (method k)‖ ≤
        M[method](t) :=
    le_trans
      (MultipleConstraintFirstOrderProblem.constraintSubgradientNorm_le_subgradientNormMaximum
        problem.toMultipleConstraintFirstOrderProblem (method k) j)
      (stageMax_le_sampleMaxSubgradientNorm method k)
  calc
    problem.constraints j (method k)
      ≤ method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := hconstraint
    _ ≤ method.h * M[method](t) :=
      mul_le_mul_of_nonneg_left hnorm hh.le
    _ = M[method](t) * method.h := by rw [mul_comm]

/-- Every objective-step iterate up to time `t` satisfies the textbook residual-maximum bound
`max_{1 ≤ j ≤ m} f_j(x_k) ≤ M h`, written through the chapter owner
`maxTypeObjective problem.constraints (method k)`, where `0 < h` and `M = M[method](t)`. -/
theorem maxConstraintValueAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
    [NeZero m]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hh : 0 < method.h)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) :
    maxTypeObjective problem.constraints (method k) ≤
      M[method](t) * method.h := by
  exact
    (maxTypeObjective_le_iff problem.constraints (method k)
      (M[method](t) * method.h)).2
      (fun j ↦
        constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
          method t hh hk j)

/-- In the large-iteration regime, the textbook denominator regime needed by Definition 3.45 is
available: the objective and selected-constraint ratios are genuine, `h > 0`, and `N(t) > 0`. -/
theorem hasApproximateDualMultiplierDenominators_of_large_iteration_count
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hobjective : method.HasObjectiveDenominators t)
    (hselected : method.HasSelectedConstraintDenominators t)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    method.HasApproximateDualMultiplierDenominators t := by
  refine ⟨hobjective, hselected, hh, ?_⟩
  exact method.positive_inactiveConstraintCount_of_large_iteration_count R t hh hQ_bounded ht

/-- In the large-iteration regime of Theorem 3.2.4, the textbook gap quantity `δ_t` is bounded
above by `M h`, where `0 < h` and `M = M[method](t)`. The source denominator
regime needed for `δ_t` is assembled from the objective and selected-constraint nonvanishing
hypotheses together with the earlier positivity theorem for `N(t)`. -/
-- Proof sketch: combine the telescoping estimate `(3.2.36)` with the source positivity gate
-- `0 < S[method](t; hobjective)`, obtained from the earlier positivity theorem for `N(t)`,
-- hence `0 < σ[method](t; hobjective)`. After inserting `t > R² / h²`, divide by `σ_t`
-- to obtain `δ_t ≤ M h`.
theorem delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hobjective : method.HasObjectiveDenominators t)
    (hselected : method.HasSelectedConstraintDenominators t)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    δ[method](t;
        (method.hasApproximateDualMultiplierDenominators_of_large_iteration_count
          R t hh hobjective hselected hQ_bounded ht)) ≤ (M[method](t) * method.h : EReal) := sorry

end ConstraintMaxima

end ApproximateLagrangeMultiplierSwitchingMethod

end

/-! ### Lemma_3_2_5 (from Chap03) -/
/- Lemma 3.2.5 lies in the chapter's ellipsoid-method localization-containment domain.

Primary domain:
- ellipsoid-method cutting-plane recursions and the containment of the retained localization sets
  inside the ambient ellipsoid sequence.

Sampled owner-style declarations:
- `localizationSets` in `Definition_3_52`, the source-facing recursive retained-region family;
- `GeneralCuttingPlaneScheme.localizationSets_subset_localizer` in `Algorithm_3_6`, the core
  containment theorem for any cutting-plane localizer;
- `EllipsoidMethod.toGeneralCuttingPlaneScheme` in `Algorithm_3_8`, the bridge from the ellipsoid
  recursion to the cutting-plane owner abstraction;
- `EllipsoidMethod.localizationSets_subset_associatedEllipsoid` in `Algorithm_3_8`, the exact
  ellipsoid-method containment theorem.

Best owner abstraction:
- source-facing: the ellipsoid-method localization sets and associated ellipsoid sequence;
- core/canonical: `GeneralCuttingPlaneScheme.localizationSets_subset_localizer`;
- bridge/view: `EllipsoidMethod.localizationSets_subset_associatedEllipsoid`.

Primitive data:
- the ambient convex minimization problem with separation oracle;
- the initial center and radius;
- the definedness, initial-cover, and positive-definiteness hypotheses for the ellipsoid
  recursion.

Derived API:
- the canonical query/cut localization sets of the ellipsoid recursion;
- the associated ellipsoid sequence;
- the source-facing containment theorem recalled below.

The previous file kept an arbitrary induction shell on unrelated sequences `S`, `Ell`, and `i`.
That shell was not the chapter owner abstraction, and the exact source-facing ellipsoid-method
statement already exists upstream. This item is therefore recall-only and keeps the canonical
bridge theorem as its public center.
-/

recall EllipsoidMethod.localizationSets_subset_associatedEllipsoid
