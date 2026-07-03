import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_69 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- `lean_leansearch` was unavailable in this run, so the local Chapter 5 and Chapter 10 files
were used directly for API recall.

Definition 10.69 is a `source-facing` bridge in the non-Euclidean proximal-gradient section. The
source item does not introduce a new owner abstraction; it restates the shared quadratic
upper-model inequality at one iterate under the admissible constant-or-B5 stepsize regime. The
relevant domain owners already present in the project are:
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 for the constant branch;
- `uses_non_euclidean_proximal_gradient_backtracking_B5_rule` from Algorithm 10.69 for the B5
  branch;
- `non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule` from Theorem 10.72
  as the source-facing Chapter 10 owner of that exact disjunction;
- `is_l_smooth_on_descent_lemma` from Lemma 5.7 for the smoothness-based derivation of the
  constant branch on the segment joining consecutive iterates.

Primitive data are the smoothness/domain hypotheses, the Bregman potential hypothesis, the
non-Euclidean trajectory, and the canonical Chapter 10 stepsize owner. The displayed quadratic
upper-model inequality is derived API, so this file should first bridge to the canonical owner
`non_euclidean_proximal_gradient_backtracking_B5_accepts` from Algorithm 10.69 instead of
keeping the expanded inequality as the primary owner-facing output. -/

omit [FiniteDimensional ℝ E] [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] in
/-- Helper for Definition 10.69: every iterate of a non-Euclidean proximal-gradient trajectory
lies in `interior (effective_domain f)` once `effective_domain g` is contained there. -/
lemma non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (k : ℕ) :
    x k ∈ interior (effective_domain f) := by
  -- The trajectory stays in `effective_domain g`, and the standing inclusion moves it into the
  -- interior of `effective_domain f`.
  exact
    hg_effective_domain_subset_interior_f_effective_domain
      (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj k).1

/-- Bridge/view layer: along a non-Euclidean proximal-gradient trajectory, the next iterate is
the canonical non-Euclidean proximal-gradient operator value `V[L_k, f, g, ω] (x^k)`. -/
theorem is_non_euclidean_proximal_gradient_trajectory_succ_eq_operator
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (k : ℕ) :
    x (k + 1) = V[L k, f, g, ω] (x k) := by
  -- The trajectory successor and the operator output solve the same unique step problem.
  have hfxk :
      is_differentiable_at f (x k) :=
    is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
  refine
    (existsUnique_non_euclidean_proximal_gradient_step_mem_domains
      f g ω (x k) (L k) hfxk).unique ?_ ?_
  · -- The realized successor is a valid step and stays in the required domains.
    exact
      ⟨is_non_euclidean_proximal_gradient_trajectory_mem_step htraj k,
        is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (k + 1)⟩
  · -- The canonical operator value satisfies the same step and domain conditions.
    exact
      ⟨non_euclidean_proximal_gradient_operator_mem_step f g ω (x k) (L k) hfxk,
        non_euclidean_proximal_gradient_operator_mem_domains f g ω (x k) (L k) hfxk⟩

/-- Helper for Definition 10.69: a real-valued descent estimate upgrades to the `EReal`
upper-model inequality once the current iterate lies in the finite domain and the next iterate
stays in `interior (effective_domain f)`. -/
lemma non_euclidean_upper_model_of_toReal_le
    {xk xNext : E} {Lk : PosReal}
    (hfxk : is_differentiable_at f xk)
    (hxNext : xNext ∈ interior (effective_domain f))
    (hdescent :
      (f xNext).toReal ≤
        (f xk).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ)) :
    f xNext ≤
      f xk +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- The differentiability owner records that `xk` lies in the finite domain of `f`.
  have hxk_finite : xk ∈ finite_domain f := interior_subset hfxk.1
  have hxk_eff : xk ∈ effective_domain f := (mem_finite_domain.mp hxk_finite).1
  have hxk_ne_bot : f xk ≠ ⊥ := (mem_finite_domain.mp hxk_finite).2
  by_cases hxNext_bot : f xNext = ⊥
  · -- If `f xNext = ⊥`, the `EReal` upper model is immediate.
    simp [hxNext_bot]
  · -- Otherwise both endpoints can be rewritten as real coercions and the real estimate lifts.
    have hxNext_eff : xNext ∈ effective_domain f := interior_subset hxNext
    have hxk_val : f xk = (((f xk).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxk_eff).ne hxk_ne_bot).symm
    have hxNext_val : f xNext = (((f xNext).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff).ne hxNext_bot).symm
    have hdescentE :
        (((f xNext).toReal : ℝ) : EReal) ≤
          (((f xk).toReal +
              inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
              ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      exact_mod_cast hdescent
    rw [hxNext_val, hxk_val]
    simpa [EReal.coe_add, add_assoc] using hdescentE

/-- Bridge/view layer: under the standing smoothness and domain hypotheses, the canonical
constant-or-B5 stepsize owner implies that the chosen curvature estimate `L_k` satisfies the
canonical B5 acceptance predicate at iteration `k`. -/
theorem non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_accepts
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule :
      non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
        f g ω Lf hω x L)
    (k : ℕ) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω (L k) (x k) := by
  rcases hrule with hLf_rule | ⟨s, η, hB5⟩
  · -- In the constant-stepsize branch, use the descent lemma on the segment joining
    -- consecutive iterates.
    have hfxk :
        is_differentiable_at f (x k) :=
      is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
    have hxk_int :
        x k ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj k
    have hxk1_int :
        x (k + 1) ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj (k + 1)
    have hnext :
        x (k + 1) = V[L k, f, g, ω] (x k) :=
      is_non_euclidean_proximal_gradient_trajectory_succ_eq_operator hω htraj k
    have hdescent :
        (f (x (k + 1))).toReal ≤
          (f (x k)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
      -- Lemma 5.7 applies on the convex interior of `effective_domain f`.
      simpa [hLf_rule k, norm_sub_rev] using
        (is_l_smooth_on_descent_lemma
          (L := Lf)
          (D := interior (effective_domain f))
          (f := fun y ↦ (f y).toReal)
          hf_effective_domain_convex.interior
          hf_toReal_smooth_on_interior_effective_domain
          hxk_int
          hxk1_int)
    refine ⟨hfxk, ?_⟩
    -- Rewrite the realized successor as the canonical operator output and lift the real descent
    -- estimate to the `EReal` acceptance inequality.
    simpa [hnext] using
      non_euclidean_upper_model_of_toReal_le
        (f := f)
        (xk := x k)
        (xNext := x (k + 1))
        (Lk := L k)
        hfxk
        hxk1_int
        hdescent
  · exact uses_non_euclidean_proximal_gradient_backtracking_B5_rule_accepts f g ω hB5 k

/-- Definition 10.69: [Remark 10.79] if `effective_domain f` is convex,
`effective_domain g ⊆ interior (effective_domain f)`, `(fun y ↦ (f y).toReal)` is `L_f`-smooth
on `interior (effective_domain f)`, and the
non-Euclidean proximal-gradient trajectory satisfies the canonical constant-or-B5 stepsize owner,
then at every iteration `k` the quadratic upper-model inequality
`f(x^(k+1)) ≤ f(x^k) + ⟪∇ f(x^k), x^(k+1) - x^k⟫ + (L_k / 2) ‖x^(k+1) - x^k‖²` holds. -/
theorem non_euclidean_proximal_gradient_upper_model_of_constant_or_backtracking_B5_rule
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule :
      non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
        f g ω Lf hω x L)
    (k : ℕ) :
    f (x (k + 1)) ≤
      f (x k) +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  have haccepts :=
    non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_accepts
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      hω htraj hrule k
  have hnext :
      x (k + 1) = V[L k, f, g, ω] (x k) :=
    is_non_euclidean_proximal_gradient_trajectory_succ_eq_operator hω htraj k
  simpa [non_euclidean_proximal_gradient_backtracking_B5_accepts, hnext] using haccepts.2

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {Lf : NNReal}
variable {XStar : Set E} {FOpt : ℝ}

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Bridge/view layer: Assumption 10.77 specializes the primitive Definition 10.69 upper-model
theorem to the source-facing constant-or-B5 stepsize rule from Theorem 10.72. -/
theorem upper_model_of_constantOrBacktrackingB5Rule
    [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L)
    (k : ℕ) :
    f (x (k + 1)) ≤
      f (x k) +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [ConstantOrBacktrackingB5StepsizeRule] using
    non_euclidean_proximal_gradient_upper_model_of_constant_or_backtracking_B5_rule
      hproblem.f_effective_domain_convex
      hproblem.g_effective_domain_subset_interior_f_effective_domain
      hproblem.f_toReal_smooth_on_interior_effective_domain
      hω htraj hrule k

end IsConvexCompositeSmoothMinimizationProblem

end

/-! ### Lemma_10_69 (from Chap10) -/
noncomputable section

universe u

section

open Metric
open scoped DualNorm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]

section

variable {counterpart : ℕ → E → E} {L : ℕ → PosReal} {x0 : E} {M : ℝ} {Rα : PosReal}
variable {α : ℝ}

local notation "xSeq" => non_euclidean_gradient_method f counterpart L x0
local notation "xDaggerSeq" =>
  non_euclidean_gradient_method_counterpart_sequence f counterpart L x0

/- Lemma 10.69 is a `source-facing` bridge from the chapter owners for the generated
non-Euclidean gradient trajectory and admissible stepsize rules to the textbook quadratic
objective-gap decrease estimate.

Domain sampling in the surrounding Chapter 10 API shows:
- `IsFastProximalGradientProblem` is the canonical owner for the convexity, smoothness, optimizer,
  and optimal-value data of the real-valued objective with zero regularizer;
- `non_euclidean_gradient_method` and
  `non_euclidean_gradient_method_is_admissible` from Algorithm 10.61 are the trajectory owners;
- `uses_non_euclidean_gradient_stepsize_rule` and
  `non_euclidean_gradient_sufficient_decrease_by_stepsize_rule` from Lemma 10.66 are the canonical
  stepsize and sufficient-decrease owners.

The radius bound at the initial level set is supplied explicitly as `hRα`, so the stronger owner
`IsSublevelDistanceBoundedSmoothConvexMinimizationProblem` would be redundant here. -/

-- Proof sketch: apply `non_euclidean_gradient_objective_values_antitone` to obtain
-- `f(x^k) ≤ f(x^0)`, then use `hRα` to bound `infDist (x^k) XStar` by `Rα`. For each optimizer
-- `xStar ∈ XStar`, the convex gradient inequality and Cauchy-Schwarz give
-- `f(x^k) - fOpt ≤ dist (x^k) xStar * ‖f'(x^k)‖_*`; taking the infimum over `xStar ∈ XStar`
-- yields `f(x^k) - fOpt ≤ Rα ‖f'(x^k)‖_*`, while
-- `non_euclidean_gradient_sufficient_decrease_by_stepsize_rule` gives
-- `f(x^k) - f(x^(k+1)) ≥ M ‖f'(x^k)‖_*²`. Combining the two bounds yields the claimed
-- quadratic objective-gap estimate, equivalently the textbook form with `C = R_α^2 / M`.
/-- Helper for Lemma 10.69: every optimizer in `XStar` attains the optimal value `fOpt`. -/
lemma optimal_value_eq_of_mem_optimal_set
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    {xStar : E} (hxStar : xStar ∈ XStar) :
    f xStar = fOpt := by
  have hoptset :
      XStar = unconstrained_problem_solutions f :=
    IsFastProximalGradientProblem.optimal_set_eq_unconstrained_problem_solutions
      (h := hfast)
  have hglb :
      IsGLB (Set.range f) fOpt :=
    IsFastProximalGradientProblem.optimal_value_isGLB_range
      (h := hfast)
  -- Rewrite the chapter optimal set as the canonical unconstrained argmin set of `f`.
  have hxStar_opt : xStar ∈ unconstrained_problem_solutions f := by
    simpa [hoptset] using hxStar
  -- The optimizer value lies below every objective value and above the global lower bound `fOpt`.
  apply le_antisymm
  · exact hglb.2 <| by
      rintro _ ⟨y, rfl⟩
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar_opt) y
  · exact hglb.1 ⟨xStar, rfl⟩

/-- Helper for Lemma 10.69: a convex differentiable real-valued function on the whole space
satisfies the first-order support inequality in `fderiv` form. -/
lemma convex_support_at_iterate_fderiv
    {xBase yBase : E}
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_diff : DifferentiableAt ℝ f xBase) :
    f yBase ≥ f xBase + fderiv ℝ f xBase (yBase - xBase) := by
  let line : ℝ → E := AffineMap.lineMap xBase yBase
  let ψ : ℝ → ℝ := fun t ↦ f (line t)
  have hψ_convex : ConvexOn ℝ Set.univ ψ := by
    -- Restrict the ambient convex objective to the affine line through `x` and `y`.
    simpa [ψ, line] using
      hf_convex.comp_affineMap (AffineMap.lineMap (k := ℝ) xBase yBase)
  have hψ_deriv : HasDerivAt ψ (fderiv ℝ f xBase (yBase - xBase)) 0 := by
    -- Differentiate the line restriction at the base point `x`.
    have hbase : HasFDerivAt f (fderiv ℝ f xBase) (line 0) := by
      simpa [line] using hf_diff.hasFDerivAt
    have hline : HasDerivAt line (yBase - xBase) 0 := by
      simpa [line] using
        (AffineMap.hasDerivAt_lineMap (a := xBase) (b := yBase) (x := (0 : ℝ)))
    simpa [ψ, line] using
      HasFDerivAt.comp_hasDerivAt (x := 0) hbase hline
  have hsecant :
      fderiv ℝ f xBase (yBase - xBase) ≤ slope ψ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hψ_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hψ_deriv
  have hsecant' :
      fderiv ℝ f xBase (yBase - xBase) ≤ f yBase - f xBase := by
    simpa [ψ, line, slope] using hsecant
  linarith

/-- Helper for Lemma 10.69: fixing an optimizer `xStar`, the objective gap at iterate `k` is
bounded by the derivative norm times the distance from `x^k` to `xStar`. -/
lemma objective_gap_le_dist_mul_dual_norm_of_mem_optimal_set
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    f (xSeq k) - fOpt ≤ dist (xSeq k) xStar * ‖fderiv ℝ f (xSeq k)‖_* := by
  have hdiff :
      DifferentiableAt ℝ f (xSeq k) :=
    non_euclidean_gradient_method_differentiableAt
      (f := f) (counterpart := counterpart) (L := L) (x0 := x0) hadm k
  have hsupport :
      f xStar ≥ f (xSeq k) - fderiv ℝ f (xSeq k) (xSeq k - xStar) := by
    -- Route correction: rewrite the convex support term along `xStar - x^k` into the source
    -- direction `x^k - xStar` before comparing it with the operator norm.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, map_neg] using
      (convex_support_at_iterate_fderiv
        (f := f) (xBase := xSeq k) (yBase := xStar) hfast.f_convex hdiff)
  have hgap_le_apply :
      f (xSeq k) - fOpt ≤ fderiv ℝ f (xSeq k) (xSeq k - xStar) := by
    -- Replace the optimizer value by `fOpt` and move the support term to the right-hand side.
    have hxstar_eq : f xStar = fOpt :=
      optimal_value_eq_of_mem_optimal_set (hfast := hfast) hxStar
    rw [← hxstar_eq]
    linarith
  -- Finish with the operator-norm bound and rewrite the ambient norm as a metric distance.
  calc
    f (xSeq k) - fOpt ≤ fderiv ℝ f (xSeq k) (xSeq k - xStar) := hgap_le_apply
    _ ≤ ‖fderiv ℝ f (xSeq k) (xSeq k - xStar)‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ f (xSeq k)‖_* * ‖xSeq k - xStar‖ := by
      simpa [Real.norm_eq_abs] using (fderiv ℝ f (xSeq k)).le_opNorm (xSeq k - xStar)
    _ = dist (xSeq k) xStar * ‖fderiv ℝ f (xSeq k)‖_* := by
      rw [dist_eq_norm]
      ring

/-- Helper for Lemma 10.69: the iterate objective gap is bounded by the distance to the optimal
set times the derivative norm. -/
lemma objective_gap_le_infDist_mul_dual_norm
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (k : ℕ) :
    f (xSeq k) - fOpt ≤ infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* := by
  by_cases hzero : ‖fderiv ℝ f (xSeq k)‖_* = 0
  · rcases hfast.optimal_set_nonempty with ⟨xStar, hxStar⟩
    -- If the derivative norm is zero, the fixed-optimizer estimate collapses the gap to zero.
    have hgap_le_zero :
        f (xSeq k) - fOpt ≤ 0 := by
      have hgap :=
        objective_gap_le_dist_mul_dual_norm_of_mem_optimal_set
          (counterpart := counterpart) (L := L) (x0 := x0) hadm hxStar k
      simpa [hzero] using hgap
    simpa [hzero] using hgap_le_zero
  · have hnorm_pos : 0 < ‖fderiv ℝ f (xSeq k)‖_* := by
      have hne : 0 ≠ ‖fderiv ℝ f (xSeq k)‖_* := by
        intro h
        exact hzero (by simpa using h.symm)
      exact lt_of_le_of_ne (norm_nonneg _) hne
    have hscaled_le_dist :
        ∀ {xStar : E}, xStar ∈ XStar →
          (f (xSeq k) - fOpt) / ‖fderiv ℝ f (xSeq k)‖_* ≤ dist (xSeq k) xStar := by
      intro xStar hxStar
      -- Divide the pointwise optimizer estimate by the positive derivative norm.
      have hgap :=
        objective_gap_le_dist_mul_dual_norm_of_mem_optimal_set
          (counterpart := counterpart) (L := L) (x0 := x0) hadm hxStar k
      exact (div_le_iff₀ hnorm_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hgap
    have hscaled_le_infDist :
        (f (xSeq k) - fOpt) / ‖fderiv ℝ f (xSeq k)‖_* ≤ infDist (xSeq k) XStar := by
      -- The divided estimate holds against every optimizer, so it holds against the infimum
      -- distance to the optimal set.
      exact (Metric.le_infDist hfast.optimal_set_nonempty).2 <| by
        intro xStar hxStar
        exact hscaled_le_dist hxStar
    have hmul :
        ((f (xSeq k) - fOpt) / ‖fderiv ℝ f (xSeq k)‖_*) * ‖fderiv ℝ f (xSeq k)‖_* ≤
          infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* := by
      exact mul_le_mul_of_nonneg_right hscaled_le_infDist (norm_nonneg _)
    simpa [div_eq_mul_inv, hzero, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Lemma 10.69: the objective values along the generated non-Euclidean gradient
trajectory are nonincreasing under the admissible stepsize rule. -/
lemma objective_values_antitone_of_admissible_stepsize
    [hfast : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf]
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize :
      uses_non_euclidean_gradient_stepsize_rule f Lf xSeq L xDaggerSeq M) :
    Antitone (fun n ↦ f (xSeq n)) := by
  have hM_pos : 0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  refine antitone_nat_of_succ_le ?_
  intro n
  have hdrop :
      f (xSeq n) - f (xSeq (n + 1)) ≥
        M * ‖fderiv ℝ f (xSeq n)‖_* ^ (2 : ℕ) :=
    non_euclidean_gradient_step_decrease_ge_dual_norm_sq
      (f := f) (Lf := Lf) (counterpart := counterpart) (L := L) (x0 := x0) (M := M)
      hfast.f_smooth hadm hstepsize n
  have hnonneg : 0 ≤ M * ‖fderiv ℝ f (xSeq n)‖_* ^ (2 : ℕ) := by
    exact mul_nonneg (le_of_lt hM_pos) (sq_nonneg ‖fderiv ℝ f (xSeq n)‖_*)
  exact sub_nonneg.mp (le_trans hnonneg hdrop)

/-- Bridge/view layer: any radius bound on a sublevel set `{y | f y ≤ α}` containing the initial
point `x0` yields the same quadratic one-step objective-gap decrease estimate for the generated
non-Euclidean gradient trajectory. The textbook `α = f(x^0)` statement is the specialization
below. -/
theorem non_euclidean_gradient_step_decrease_ge_sq_objective_gap_of_sublevel_distance_bound
    (hx0 : f x0 ≤ α)
    (hRα : ∀ ⦃y : E⦄, f y ≤ α → infDist y XStar ≤ Rα)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize :
      uses_non_euclidean_gradient_stepsize_rule f Lf xSeq L xDaggerSeq M)
    (k : ℕ) :
    f (xSeq k) - f (xSeq (k + 1)) ≥
      (M / ((Rα : ℝ) ^ (2 : ℕ))) * (f (xSeq k) - fOpt) ^ (2 : ℕ) := by
  have hM_pos : 0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  have hantitone :
      Antitone (fun n ↦ f (xSeq n)) :=
    objective_values_antitone_of_admissible_stepsize
      (counterpart := counterpart) (L := L) (x0 := x0) (M := M) hadm hstepsize
  have hxk_le_x0 : f (xSeq k) ≤ f x0 := by
    simpa using hantitone (Nat.zero_le k)
  have hxk_le_α : f (xSeq k) ≤ α := by
    exact le_trans hxk_le_x0 hx0
  have hinfDist_le :
      infDist (xSeq k) XStar ≤ Rα :=
    hRα hxk_le_α
  have hgap_inf :
      f (xSeq k) - fOpt ≤ infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* :=
    objective_gap_le_infDist_mul_dual_norm
      (counterpart := counterpart) (L := L) (x0 := x0) hadm k
  have hgap_radius :
      f (xSeq k) - fOpt ≤ (Rα : ℝ) * ‖fderiv ℝ f (xSeq k)‖_* := by
    -- Monotonicity keeps `x^k` in the initial sublevel set, so `hRα` upgrades the `infDist`
    -- bound to the source radius `Rα`.
    calc
      f (xSeq k) - fOpt ≤ infDist (xSeq k) XStar * ‖fderiv ℝ f (xSeq k)‖_* := hgap_inf
      _ ≤ (Rα : ℝ) * ‖fderiv ℝ f (xSeq k)‖_* := by
        exact mul_le_mul_of_nonneg_right hinfDist_le (norm_nonneg _)
  have hdrop :
      f (xSeq k) - f (xSeq (k + 1)) ≥
        M * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) :=
    non_euclidean_gradient_step_decrease_ge_dual_norm_sq
      (f := f) (Lf := Lf) (counterpart := counterpart) (L := L) (x0 := x0) (M := M)
      hproblem.f_smooth hadm hstepsize k
  have hgap_nonneg : 0 ≤ f (xSeq k) - fOpt := by
    have hglb :
        IsGLB (Set.range f) fOpt :=
      IsFastProximalGradientProblem.optimal_value_isGLB_range
        (h := hproblem)
    exact sub_nonneg.mpr (hglb.1 ⟨xSeq k, rfl⟩)
  have hgrad_nonneg : 0 ≤ ‖fderiv ℝ f (xSeq k)‖_* := norm_nonneg _
  have hR_sq_pos : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    simpa [pow_two] using sq_pos_of_pos (PosReal.coe_pos Rα)
  have hgap_sq :
      (f (xSeq k) - fOpt) ^ (2 : ℕ) ≤
        ((Rα : ℝ) ^ (2 : ℕ)) * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) := by
    -- Squaring the radius estimate is valid because both factors are nonnegative.
    nlinarith [hgap_radius, hgap_nonneg, hgrad_nonneg, PosReal.coe_pos Rα]
  have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
  have hmul :
      M * (f (xSeq k) - fOpt) ^ (2 : ℕ) ≤
        M * (((Rα : ℝ) ^ (2 : ℕ)) * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hgap_sq hM_nonneg
  have hdiv :
      (M * (f (xSeq k) - fOpt) ^ (2 : ℕ)) / ((Rα : ℝ) ^ (2 : ℕ)) ≤
        M * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) := by
    exact (div_le_iff₀ hR_sq_pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    f (xSeq k) - f (xSeq (k + 1)) ≥
        M * ‖fderiv ℝ f (xSeq k)‖_* ^ (2 : ℕ) := hdrop
    _ ≥ (M * (f (xSeq k) - fOpt) ^ (2 : ℕ)) / ((Rα : ℝ) ^ (2 : ℕ)) := hdiv
    _ = (M / ((Rα : ℝ) ^ (2 : ℕ))) * (f (xSeq k) - fOpt) ^ (2 : ℕ) := by
      field_simp [hR_sq_pos.ne']

/-- Lemma 10.69: if the non-Euclidean gradient iterates satisfy the sublevel-distance bound at
level `α = f(x^0)`, then every step obeys the quadratic decrease estimate
`f(x^k) - f(x^(k+1)) ≥ (M / R_α^2) (f(x^k) - f_opt)^2`, where `M` is the sufficient-decrease
constant supplied by the Chapter 10 owner
`uses_non_euclidean_gradient_stepsize_rule`; equivalently, with `C = R_α^2 / M`, one has
`f(x^k) - f(x^(k+1)) ≥ (1 / C) (f(x^k) - f_opt)^2`. -/
theorem non_euclidean_gradient_step_decrease_ge_sq_objective_gap
    (hRα : ∀ ⦃y : E⦄, f y ≤ f x0 → infDist y XStar ≤ Rα)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize :
      uses_non_euclidean_gradient_stepsize_rule f Lf xSeq L xDaggerSeq M)
    (k : ℕ) :
    f (xSeq k) - f (xSeq (k + 1)) ≥
      (M / ((Rα : ℝ) ^ (2 : ℕ))) * (f (xSeq k) - fOpt) ^ (2 : ℕ) := by
  exact
    non_euclidean_gradient_step_decrease_ge_sq_objective_gap_of_sublevel_distance_bound
      (show f x0 ≤ f x0 from le_rfl) hRα hadm hstepsize k

end

end
