import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_8_17_1 (from Chap08) -/
universe u

section

variable {E : Type u} [PseudoMetricSpace E]

/-- Helper for Theorem 8.17.1: the numerator in the rate bound is nonnegative whenever `L_f` is
nonnegative. -/
lemma rate_bound_numerator_nonneg
    (x0 : E) (XStar : Set E) (Lf : ℝ) (hLf : 0 ≤ Lf) :
    0 ≤ Lf * Metric.infDist x0 XStar := by
  -- The rate numerator is a product of two nonnegative factors.
  exact mul_nonneg hLf (Metric.infDist_nonneg)

/-- Helper for Theorem 8.17.1: a rate bound `M / √(k + 1) ≤ ε` with `ε > 0` yields the equivalent
iteration lower bound after multiplying by the positive square root and squaring. -/
lemma iteration_count_lb_of_rate_bound
    (M ε : ℝ) (k : ℕ) (hM : 0 ≤ M) (hε : 0 < ε)
    (h_bound : M / Real.sqrt ((k : ℝ) + 1) ≤ ε) :
    M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
  -- The square root denominator is positive because `k + 1 > 0`.
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    apply Real.sqrt_pos.2
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 1) := le_of_lt hsqrt_pos
  -- Multiplying by the positive square root isolates the numerator `M`.
  have h_mul : M ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    rw [div_le_iff₀ hsqrt_pos] at h_bound
    simpa [mul_comm] using h_bound
  have h_right_nonneg : 0 ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    exact mul_nonneg (le_of_lt hε) hsqrt_nonneg
  -- Squaring preserves the inequality because both sides are nonnegative.
  have h_sq : M ^ (2 : ℕ) ≤ (ε * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by
    nlinarith [h_mul, hM, h_right_nonneg]
  have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity))
  have h_num : M ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * ε ^ (2 : ℕ) := by
    nlinarith [h_sq, hsqrt_sq]
  have h_div : M ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ (k : ℝ) + 1 := by
    rw [div_le_iff₀ (by positivity : 0 < ε ^ (2 : ℕ))]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_num
  nlinarith

/-- Helper for Theorem 8.17.1: the iteration lower bound implies the corresponding rate bound
after rewriting it as a squared inequality and taking square roots. -/
lemma rate_bound_of_iteration_count_lb
    (M ε : ℝ) (k : ℕ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hk : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ)) :
    M / Real.sqrt ((k : ℝ) + 1) ≤ ε := by
  -- Rearranging the iteration threshold gives a bound on `M²`.
  have h_div : M ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ (k : ℝ) + 1 := by
    nlinarith
  have h_num : M ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * ε ^ (2 : ℕ) := by
    rw [div_le_iff₀ (by positivity : 0 < ε ^ (2 : ℕ))] at h_div
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_div
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    apply Real.sqrt_pos.2
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 1) := le_of_lt hsqrt_pos
  have h_right_nonneg : 0 ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    exact mul_nonneg (le_of_lt hε) hsqrt_nonneg
  have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity))
  -- Matching square bounds and nonnegativity recover the unsquared rate estimate.
  have h_sq : M ^ (2 : ℕ) ≤ (ε * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by
    nlinarith [h_num, hsqrt_sq]
  have h_mul : M ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    nlinarith [h_sq, hM, h_right_nonneg]
  rw [div_le_iff₀ hsqrt_pos]
  simpa [mul_comm] using h_mul

/-- The numerical rate bound `L_f d_{X^*}(x^0) / √(k + 1) ≤ ε` is equivalent to the corresponding
lower bound on the iteration index `k`, after squaring both sides. -/
-- Proof sketch: use that `Metric.infDist` is nonnegative and that `ε > 0`, so multiplying by
-- `ε` and `Real.sqrt (k + 1)` preserves the inequality. Then square both sides and rearrange the
-- resulting real inequality.
theorem rate_bound_le_epsilon_iff_iteration_count_lb
    (x0 : E) (XStar : Set E) (Lf ε : ℝ) (k : ℕ)
    (hLf : 0 ≤ Lf) (hε : 0 < ε) :
    Lf * Metric.infDist x0 XStar / Real.sqrt (k + 1) ≤ ε ↔
      Lf ^ (2 : ℕ) * Metric.infDist x0 XStar ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
  let M : ℝ := Lf * Metric.infDist x0 XStar
  have hM : 0 ≤ M := by
    -- Package the numerator into a single nonnegative scalar.
    simpa [M] using rate_bound_numerator_nonneg x0 XStar Lf hLf
  have h_expand : M ^ (2 : ℕ) = Lf ^ (2 : ℕ) * Metric.infDist x0 XStar ^ (2 : ℕ) := by
    -- Expanding `M` matches the textbook numerator `L_f² d_{X^*}(x^0)²`.
    dsimp [M]
    ring
  constructor
  · intro h_bound
    -- Convert the displayed rate bound into the scalar form and square it.
    have h_iter_M :
        M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
      exact iteration_count_lb_of_rate_bound M ε k hM hε (by simpa [M] using h_bound)
    rw [h_expand] at h_iter_M
    exact h_iter_M
  · intro h_iter
    -- Rewrite the iteration threshold in terms of the scalar numerator `M`.
    have h_iter_M : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
      simpa [h_expand] using h_iter
    -- Recover the displayed rate bound from the scalar iteration threshold.
    simpa [M] using rate_bound_of_iteration_count_lb M ε k hM hε h_iter_M

/-- Theorem 8.17.1: if the previously established projected-subgradient bound
`f_best - f_opt ≤ L_f d_{X^*}(x^0) / √(k + 1)` holds, then the sufficient condition
`L_f d_{X^*}(x^0) / √(k + 1) ≤ ε` implies `f_best - f_opt ≤ ε`. In particular, this yields the
usual `O(ε⁻²)` iteration estimate through the companion iteration-count inequality. -/
-- Proof sketch: combine the assumed bound on the best attained objective gap with the displayed
-- upper bound `L_f d_{X^*}(x^0) / √(k + 1) ≤ ε` by transitivity.
theorem best_function_value_gap_le_epsilon_of_rate_bound
    (x0 : E) (XStar : Set E) (fBest fOpt Lf ε : ℝ) (k : ℕ)
    (h_rate : fBest - fOpt ≤ Lf * Metric.infDist x0 XStar / Real.sqrt (k + 1))
    (h_bound : Lf * Metric.infDist x0 XStar / Real.sqrt (k + 1) ≤ ε) :
    fBest - fOpt ≤ ε := by
  -- The assumed rate estimate already bounds the objective gap by the displayed quantity.
  exact h_rate.trans h_bound

end

/-! ### Definition_8_17 (from Chap08) -/
universe u v

section

variable {E : Type u} {m : ℕ}

/- Definition 8.17 is `source-facing`: it fixes the primal inequality-constrained optimization
problem with ambient set constraint `x ∈ X` and coordinatewise inequality constraint `g(x) ≤ 0`.
The canonical owner abstraction for optimality itself is mathlib's `IsMinOn`; the genuinely new
data here is the feasible set obtained by combining `X` with the coordinatewise inequalities. -/

/-- Definition 8.17: the feasible set of the problem `min f(x)` subject to `g(x) ≤ 0` and
`x ∈ X` consists of the points of `X` satisfying every coordinatewise inequality constraint
`g x i ≤ 0`. -/
def inequality_constrained_primal_feasible_set
    (X : Set E) (g : E → Fin m → ℝ) : Set E :=
  {x | x ∈ X ∧ ∀ i : Fin m, g x i ≤ 0}

-- Proof sketch: unfold `inequality_constrained_primal_feasible_set`; membership is exactly the
-- conjunction of `x ∈ X` and the coordinatewise inequalities `g x i ≤ 0`.
/-- Helper for Definition 8.17: membership in
`inequality_constrained_primal_feasible_set X g` means belonging to `X` and satisfying all
inequalities `g x i ≤ 0`. -/
@[simp] theorem mem_inequality_constrained_primal_feasible_set
    {X : Set E} {g : E → Fin m → ℝ} {x : E} :
    x ∈ inequality_constrained_primal_feasible_set X g ↔
      x ∈ X ∧ ∀ i : Fin m, g x i ≤ 0 := by
  -- Unfolding the set-builder exposes exactly the ambient-set and inequality constraints.
  rfl

section

variable {α : Type v} [Preorder α]

-- Proof sketch: `IsMinOn` only records the comparison inequalities on feasible points, so the
-- minimizer's own feasibility must be bundled separately to match the textbook constrained
-- problem statement.
/-- Helper for Definition 8.17: a feasible point `x` minimizes `f` on
`inequality_constrained_primal_feasible_set X g` exactly when `x` satisfies the inequality
constraints and beats every other feasible comparison point. -/
theorem isMinOn_inequality_constrained_primal_feasible_set_iff
    {f : E → α} {X : Set E} {g : E → Fin m → ℝ} {x : E} :
    x ∈ inequality_constrained_primal_feasible_set X g ∧
      IsMinOn f (inequality_constrained_primal_feasible_set X g) x ↔
      x ∈ X ∧
        (∀ i : Fin m, g x i ≤ 0) ∧
        ∀ y, y ∈ X → (∀ i : Fin m, g y i ≤ 0) → f x ≤ f y := by
  -- Route correction: mathlib's `IsMinOn` does not assert `x ∈ s`, so we keep feasibility
  -- explicit on the left-hand side before rewriting into the textbook constrained form.
  constructor
  · rintro ⟨hx, hmin⟩
    rcases (mem_inequality_constrained_primal_feasible_set.mp hx) with ⟨hxX, hxg⟩
    rw [isMinOn_iff] at hmin
    refine ⟨hxX, hxg, ?_⟩
    -- Every feasible comparison point is in the feasible set, so `IsMinOn` gives the inequality.
    intro y hyX hyg
    exact hmin y <| mem_inequality_constrained_primal_feasible_set.mpr ⟨hyX, hyg⟩
  · rintro ⟨hxX, hxg, hmin⟩
    refine ⟨mem_inequality_constrained_primal_feasible_set.mpr ⟨hxX, hxg⟩, ?_⟩
    rw [isMinOn_iff]
    -- Rewriting feasible-set membership for the comparison point reduces the goal to `hmin`.
    intro y hy
    rcases (mem_inequality_constrained_primal_feasible_set.mp hy) with ⟨hyX, hyg⟩
    exact hmin y hyX hyg

end

end

/-! ### Theorem_8_17 (from Chap08) -/
universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.17 is `source-facing`: it is the convergence theorem for the concrete projected
subgradient iterates generated under Polyak's stepsize rule. The canonical owners already present
in the chapter are the recursive iterate sequence `projected_subgradient_method`, the standing
problem package `IsConstrainedConvexProblem`, the subgradient bound package
`SubgradientNormBoundOn`, and the Fejér-convergence criterion
`tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo`. To keep the textbook meaning faithful,
the Euclidean finite-dimensional hypothesis from Definition 8.1 is made explicit here: it is the
hidden input that supplies a sequential cluster point of the bounded Fejér-monotone trajectory. -/

-- Proof sketch: rewrite `h_subgrad` through `mem_strongDualSubdifferential` and apply
-- Theorem 8.13(a) to get Fejér monotonicity of `x` with respect to `XStar`, and Theorem 8.13(b)
-- to get convergence of `(f (x[k] : E)).toReal` to `fOpt`. Finite dimensionality and Fejér
-- monotonicity provide a cluster point of the iterate sequence. Any cluster point lies in `C`
-- because `C` is closed, hence in `interior (effective_domain f)` by Assumption 8.7, so the
-- continuity theorem for convex functions on interior points upgrades the limit
-- `(f (x[k] : E)).toReal → fOpt` to optimality of the cluster point. Therefore every cluster point
-- belongs to `XStar`, and Theorem 8.16 yields convergence of the whole sequence to a point of
-- `XStar`.
/-- Helper for Theorem 8.17: Polyak's stepsize rule makes the distance from the projected
subgradient iterates to each optimal point nonincreasing. -/
lemma projected_subgradient_method_dist_mono_of_polyak_stepsize
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n])))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    dist (x[k + 1] : E) xStar ≤ dist (x[k] : E) xStar := by
  -- Rewrite the strong-dual selections into the owner interface used by Theorem 8.13.
  have h_subgrad' :
      ∀ n,
        (toDualMap ℝ E (g n (x[n])) : Module.Dual ℝ E) ∈ subdifferential f (x[n] : E) := by
    intro n
    simpa [mem_strongDualSubdifferential] using h_subgrad n
  have hsq :=
    projected_subgradient_method_sqdist_mono_of_polyak_stepsize
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) h_bound h_subgrad' h_polyak hxStar k
  -- The squared-distance inequality is exactly the Fejer step after removing the squares.
  have hnorm : ‖(x[k + 1] : E) - xStar‖ ≤ ‖(x[k] : E) - xStar‖ := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hsq
    exact hsq
  simpa [dist_eq_norm] using hnorm

/-- Helper for Theorem 8.17: finite-dimensional compactness provides a sequential cluster point for
the Polyak trajectory. -/
lemma projected_subgradient_method_has_mapClusterPt_of_polyak_stepsize
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n]))) :
    ∃ y : E, MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E)) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  let r : ℝ := dist (x[0] : E) xStar
  have hball : ∀ n : ℕ, (x[n] : E) ∈ Metric.closedBall xStar r := by
    intro n
    have hdist : dist (x[n] : E) xStar ≤ dist (x[0] : E) xStar := by
      induction n with
      | zero =>
          exact le_rfl
      | succ n ih =>
          exact le_trans
            (projected_subgradient_method_dist_mono_of_polyak_stepsize
              (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
              (h_subgrad := h_subgrad) (h_polyak := h_polyak) hxStar n)
            ih
    simpa [r, Metric.mem_closedBall] using hdist
  have hfreq :
      ∃ᶠ n in Filter.atTop, (x[n] : E) ∈ Metric.closedBall xStar r :=
    (Filter.Eventually.of_forall hball).frequently
  rcases (isCompact_closedBall xStar r).exists_mapClusterPt_of_frequently hfreq with
    ⟨y, -, hy⟩
  exact ⟨y, hy⟩

/-- Helper for Theorem 8.17: interior feasibility makes `x ↦ (f x).toReal` continuous at that
point. -/
lemma toReal_continuousAt_of_mem_interior_effective_domain
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt) {y : E}
    (hy : y ∈ interior (effective_domain f)) :
    ContinuousAt (fun z : E ↦ (f z).toReal) y := by
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function h_problem.convex
      (fun z hz ↦ h_problem.ne_bot z)
  have hcontOn :
      ContinuousOn (fun z : E ↦ (f z).toReal) (interior (effective_domain f)) :=
    hconv.continuousOn_interior
  -- The interior of a convex domain is open, so continuity within the interior is ordinary
  -- continuity at the chosen point.
  exact (hcontOn y hy).continuousAt (isOpen_interior.mem_nhds hy)

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 8.17: a feasible point whose objective value equals `fOpt` belongs to the
optimal set `XStar`. -/
lemma mem_optimal_set_of_mem_C_of_toReal_eq_fOpt
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt) {y : E}
    (hyC : y ∈ C) (hyOpt : (f y).toReal = fOpt) :
    y ∈ XStar := by
  have hyDom : y ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hyC)
  have hyTop : f y ≠ ⊤ := ne_of_lt hyDom
  have hyBot : f y ≠ ⊥ := h_problem.ne_bot y
  have hyEq : f y = (fOpt : EReal) := by
    calc
      f y = (((f y).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal hyTop hyBot
      _ = (fOpt : EReal) := by
        simp [hyOpt]
  rw [h_problem.optimal_set_eq]
  refine ⟨hyC, ?_⟩
  rw [isMinOn_iff]
  intro z hzC
  have hzImage : f z ∈ f '' C := ⟨z, hzC, rfl⟩
  have hglb : (fOpt : EReal) ≤ f z := h_problem.optimal_value_isGLB.left hzImage
  simpa [hyEq] using hglb

/-- Helper for Theorem 8.17: every sequential cluster point of the Polyak trajectory is an optimal
solution. -/
lemma cluster_point_mem_optimal_set_of_polyak_stepsize {y : E}
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n])))
    (hyCluster : MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E))) :
    y ∈ XStar := by
  have h_subgrad' :
      ∀ n,
        (toDualMap ℝ E (g n (x[n])) : Module.Dual ℝ E) ∈ subdifferential f (x[n] : E) := by
    intro n
    simpa [mem_strongDualSubdifferential] using h_subgrad n
  have hyC : y ∈ C := by
    -- Closedness of the feasible set transfers feasibility from the whole trajectory to the
    -- cluster point.
    refine h_problem.feasible_closed.mem_of_mapClusterPt hyCluster ?_
    exact Filter.Eventually.of_forall fun n => (x[n]).property
  have hyInterior : y ∈ interior (effective_domain f) :=
    h_problem.feasible_subset_interior_effective_domain hyC
  have hcont :
      ContinuousAt (fun z : E ↦ (f z).toReal) y :=
    toReal_continuousAt_of_mem_interior_effective_domain
      (h_problem := h_problem) hyInterior
  have hobj :
      Filter.Tendsto (fun n ↦ (f (x[n] : E)).toReal) Filter.atTop (nhds fOpt) :=
    projected_subgradient_method_objective_tendsto_of_polyak_stepsize
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) h_bound h_subgrad' h_polyak
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hyCluster
  have hsubseq_obj :
      Filter.Tendsto (fun n ↦ (f (x[ψ n] : E)).toReal) Filter.atTop (nhds fOpt) :=
    hobj.comp hψmono.tendsto_atTop
  have hsubseq_cont :
      Filter.Tendsto (fun n ↦ (f (x[ψ n] : E)).toReal) Filter.atTop (nhds ((f y).toReal)) := by
    -- The subsequence converges to `y`, so continuity identifies the objective limit there.
    simpa [Function.comp] using hcont.tendsto.comp hψtendsto
  have hyOpt : (f y).toReal = fOpt :=
    tendsto_nhds_unique hsubseq_cont hsubseq_obj
  exact mem_optimal_set_of_mem_C_of_toReal_eq_fOpt
    (h_problem := h_problem) hyC hyOpt

include h_bound
/-- Theorem 8.17: under Assumptions 8.7 and 8.12, the projected subgradient sequence generated
with Polyak's stepsize rule converges to a point of the optimal set `XStar = X^*`. -/
theorem projected_subgradient_method_tendsto_point_in_optimal_set_of_polyak_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n]))) :
    ∃ xStar : E,
      xStar ∈ XStar ∧
        Filter.Tendsto (fun n ↦ (x[n] : E)) Filter.atTop (nhds xStar) := by
  have hFejer : ∀ y ∈ XStar, ∀ k : ℕ, dist (x[k + 1] : E) y ≤ dist (x[k] : E) y := by
    intro y hy k
    -- Theorem 8.13(a) is the source-faithful Fejer monotonicity input for Theorem 8.16.
    exact projected_subgradient_method_dist_mono_of_polyak_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      (h_subgrad := h_subgrad) (h_polyak := h_polyak) hy k
  have hlimitPoints_subset :
      {y : E | MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E))} ⊆ XStar := by
    intro y hy
    -- Every cluster point is feasible, continuity transfers the objective limit, and the
    -- resulting feasible minimizer lies in `XStar`.
    exact cluster_point_mem_optimal_set_of_polyak_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      (h_subgrad := h_subgrad) (h_polyak := h_polyak) hy
  have hlimitPoint : ∃ y : E, MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E)) :=
    projected_subgradient_method_has_mapClusterPt_of_polyak_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      (h_subgrad := h_subgrad) (h_polyak := h_polyak)
  obtain ⟨xStar, hxStarCluster, hxStarTendsto⟩ :=
    tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo hFejer hlimitPoints_subset hlimitPoint
  exact ⟨xStar, hlimitPoints_subset hxStarCluster, hxStarTendsto⟩

end
