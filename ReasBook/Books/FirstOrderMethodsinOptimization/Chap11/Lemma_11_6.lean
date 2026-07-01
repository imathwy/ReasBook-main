import Mathlib
import FirstOrderMethodsinOptimization.Chap10.Definition_10_67
import FirstOrderMethodsinOptimization.Chap11.Algorithm_11_4
import FirstOrderMethodsinOptimization.Chap11.Lemma_11_4
import FirstOrderMethodsinOptimization.Chap11.Theorem_11_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

section

open Metric

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [Nonempty (Fin p)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

section

/- Lemma 11.6 is `bridge/view`: the Chapter 11 owner abstractions already live upstream.
- `CyclicBlockProximalGradientConvexAssumptions` is the source-facing convex CBPG owner.
- `cbpg_sufficient_decrease_outer_step` from Lemma 11.4 is the canonical outer-step decrease
  estimate.
- `CyclicBlockProximalGradientConvexAssumptions.bounded_initial_sublevel_distance_to_optimal_set`
  from Theorem 11.6 is the owner-level bridge from the source pairwise radius bound to the
  `infDist` formulation used downstream.

This file therefore keeps only the chapter coefficient and the resulting one-step quadratic
objective-gap estimate, instead of repackaging the same problem data in a parallel local owner. -/

/-- The coefficient `L_min / (2 p (L_f + L_max)^2 R^2)` appearing in the quadratic
objective-gap decrease estimate for the convex CBPG method at the initial sublevel radius `R`. -/
def cbpg_quadratic_gap_constant
    (Lf : NNReal) (Li : (i : Fin p) → PosReal) (R : PosReal) : ℝ :=
  (cbpg_min_block_stepsize Li : ℝ) /
    (2 * (p : ℝ) * (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) *
      ((R : ℝ) ^ (2 : ℕ)))

-- Proof sketch: unfold `cbpg_quadratic_gap_constant`; the definition is exactly the displayed
-- scalar coefficient built from the owner declarations `cbpg_min_block_stepsize` and
-- `cbpg_max_block_stepsize`.
/-- Expanding `cbpg_quadratic_gap_constant` gives the textbook coefficient
`L_min / (2 p (L_f + L_max)^2 R^2)`. -/
@[simp] theorem cbpg_quadratic_gap_constant_def (R : PosReal) :
    cbpg_quadratic_gap_constant Lf Li R =
      (cbpg_min_block_stepsize Li : ℝ) /
        (2 * (p : ℝ) * (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) *
          ((R : ℝ) ^ (2 : ℕ))) :=
  rfl

section

variable [∀ i, ProperSpace (Ei i)]
variable
  (hconvex : CyclicBlockProximalGradientConvexAssumptions
    f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "hproblem" => hconvex.toBlockProximalGradientAssumptions
local notation "x0I" => hconvex.interior_effective_domain_point x0

set_option quotPrecheck false in
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0I k
set_option quotPrecheck false in
local notation "x[" k "," i "]" =>
  cyclic_block_proximal_gradient_inner_iterate hproblem x[k] i

local notation "F" =>
  composite_model_objective f (separableSum g)

set_option quotPrecheck false in
local notation "Δ[" k "]" => (F x[k]).toReal - FOpt

local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "Lmax" => cbpg_max_block_stepsize Li
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)

/-- Helper for Lemma 11.6: the convex CBPG assumptions include the base block proximal-gradient
owner used throughout Chapter 11. -/
lemma cbpg_base_problem
    (hconvex' : CyclicBlockProximalGradientConvexAssumptions
      f g block_gradient XStar FOpt Lf Li) :
    BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li := by
  letI : CyclicBlockProximalGradientConvexAssumptions
      f g block_gradient XStar FOpt Lf Li := hconvex'
  exact
    CyclicBlockProximalGradientConvexAssumptions.toBlockProximalGradientAssumptions
      (f := f) (g := g) (block_gradient := block_gradient)
      (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (Li := Li)

/-- Helper for Lemma 11.6: convexity of the smooth term is one of the primitive convex CBPG
assumptions. -/
lemma cbpg_f_convex
    (hconvex' : CyclicBlockProximalGradientConvexAssumptions
      f g block_gradient XStar FOpt Lf Li) :
    is_convex_function f := by
  letI : CyclicBlockProximalGradientConvexAssumptions
      f g block_gradient XStar FOpt Lf Li := hconvex'
  simpa using
    (CyclicBlockProximalGradientConvexAssumptions.f_convex
      (f := f) (g := g) (block_gradient := block_gradient)
      (XStar := XStar) (FOpt := FOpt) (Lf := Lf) (Li := Li))

/-- Helper for Lemma 11.6: the convex CBPG assumptions canonically induce the Chapter 10 convex
composite owner for `f` and the aggregate regularizer `separableSum g`. -/
lemma cbpg_toIsConvexCompositeSmoothMinimizationProblem :
    IsConvexCompositeSmoothMinimizationProblem
      f (separableSum g) XStar FOpt Lf := by
  have hbase : IsCompositeSmoothMinimizationProblem f (separableSum g) XStar FOpt Lf := by
    -- Reuse the Chapter 11-to-Chapter 10 bridge once, then add convexity of `f`.
    exact
      BlockProximalGradientAssumptions.toIsCompositeSmoothMinimizationProblem
        (cbpg_base_problem hconvex)
  have hf_convex : is_convex_function f := cbpg_f_convex hconvex
  -- Package the Chapter 11 block owner together with the source convexity clause for `f`.
  refine
    { f_ne_bot := hbase.f_ne_bot
      g_proper := hbase.g_proper
      f_closed := hbase.f_closed
      g_closed := hbase.g_closed
      f_convex := hf_convex
      g_convex := hbase.g_convex
      g_effective_domain_subset_interior_f_effective_domain :=
        hbase.g_effective_domain_subset_interior_f_effective_domain
      f_toReal_smooth_on_interior_effective_domain :=
        hbase.f_toReal_smooth_on_interior_effective_domain
      optimal_set_eq := hbase.optimal_set_eq
      optimal_set_nonempty := hbase.optimal_set_nonempty
      optimal_value_isGLB := hbase.optimal_value_isGLB }

/-- Helper for Lemma 11.6: the aggregate objective `F = f + separableSum g` is lower
semicontinuous under the standing convex CBPG assumptions. -/
lemma cbpg_objective_closed :
    LowerSemicontinuous F := by
  let hbase :
      IsCompositeSmoothMinimizationProblem f (separableSum g) XStar FOpt Lf :=
    BlockProximalGradientAssumptions.toIsCompositeSmoothMinimizationProblem
      (cbpg_base_problem hconvex)
  let hproblem' : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li :=
    cbpg_base_problem hconvex
  -- Closedness of `f` and of `separableSum g` combines once we rule out `-∞` in the sum term.
  refine LowerSemicontinuous.add'
      hbase.f_closed
      hbase.g_closed ?_
  intro z
  have hseparable_ne_bot : separableSum g z ≠ ⊥ := by
    rw [separableSum_apply]
    exact
      ereal_sum_ne_bot Finset.univ
        (fun i ↦ g i (z i))
        (fun i _ ↦ (hproblem'.block_g_proper i).ne_bot _)
  exact EReal.continuousAt_add (.inr hseparable_ne_bot) (.inl (hbase.f_ne_bot z))

/-- Helper for Lemma 11.6: the optimal set `XStar` is closed because it is exactly the
real-valued optimal sublevel set `{x | F x ≤ FOpt}`. -/
lemma cbpg_optimal_set_isClosed :
    IsClosed XStar := by
  have hcomposite :
      IsConvexCompositeSmoothMinimizationProblem
        f (separableSum g) XStar FOpt Lf :=
    cbpg_toIsConvexCompositeSmoothMinimizationProblem hconvex x0
  have hsublevel_closed : IsClosed (F ⁻¹' Set.Iic (FOpt : EReal)) :=
    (lowerSemicontinuous_iff_isClosed_real_sublevelSets F).mp
      (cbpg_objective_closed hconvex x0)
      FOpt
  have hXStar_eq :
      XStar = F ⁻¹' Set.Iic (FOpt : EReal) := by
    ext z
    constructor
    · intro hz
      -- An optimizer attains the optimal value, hence lies in the `FOpt` sublevel.
      have hz_eq : F z = (FOpt : EReal) :=
        hcomposite.objective_eq_optimalValue_of_mem_optimalSet hz
      simp [hz_eq]
    · intro hz
      -- Conversely, any point below `FOpt` is already a global minimizer because `FOpt` is the
      -- greatest lower bound of the objective values.
      rw [hcomposite.optimal_set_eq]
      refine (mem_unconstrained_problem_solutions_iff_forall_le).2 ?_
      intro y
      exact le_trans hz (hcomposite.optimal_value_isGLB.1 ⟨y, rfl⟩)
  simpa [hXStar_eq] using hsublevel_closed

/-- Helper for Lemma 11.6: every point admits a nearest optimizer witness in `XStar`. This is the
header bridge from the theorem's `infDist` radius bound to the source proof's fixed optimizer
comparison point. -/
lemma cbpg_exists_nearest_optimizer
    (z : (i : Fin p) → Ei i) :
    ∃ xStar, xStar ∈ XStar ∧ dist z xStar = infDist z XStar := by
  have hbase : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li :=
    cbpg_base_problem hconvex
  have hXStar_closed : IsClosed XStar :=
    cbpg_optimal_set_isClosed hconvex x0
  -- Closedness and nonemptiness turn the metric infimum into an attained distance.
  obtain ⟨xStar, hxStar, hdist⟩ :=
    hXStar_closed.exists_infDist_eq_dist hbase.optimal_set_nonempty z
  exact ⟨xStar, hxStar, hdist.symm⟩

/-- Helper for Lemma 11.6: every auxiliary iterate `x^{k,m}` with `m ≤ p` remains in the
effective domain of the block-separable regularizer. -/
lemma cbpg_inner_iterate_mem_effective_domain
    (k : ℕ) (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  -- Reuse the canonical Lemma 11.4 domain-propagation owner instead of duplicating it locally.
  simpa using
    cbpg_auxiliary_iterate_mem_effective_domain (cbpg_base_problem hconvex) x0 k m hm

/-- Helper for Lemma 11.6: if a later inner stage updates block `m > j`, then the already-updated
coordinate `j` is unchanged by that one-block update. -/
lemma cbpg_block_coordinate_fixed_by_later_stage
    (k : ℕ) (j : Fin p) {m : ℕ} (hjm : j.1 < m) (hm : m < p) :
    x[k, m + 1] j = x[k, m] j := by
  let jm : Fin p := ⟨m, hm⟩
  have hjm_ne : j ≠ jm := by
    intro hEq
    have hvals : j.1 = m := by
      simpa [jm] using congrArg Fin.val hEq
    omega
  -- Rewrite the later stage as the one-block update in block `m`, then evaluate the `j`-th
  -- coordinate away from the active block.
  have hsucc :=
    cyclic_block_proximal_gradient_method_inner_succ
      (cbpg_base_problem hconvex) x0I k hm
  have hcoord := congrArg (fun z ↦ z j) hsucc
  simpa [jm, hjm_ne] using hcoord

/-- Helper for Lemma 11.6: once block `j` has been updated at stage `j + 1`, all later inner
stages keep its coordinate fixed. In particular, `x_j^{k,j} = x_j^{k+1}` in the source notation.
-/
lemma cbpg_block_coordinate_stable_after_update
    (k : ℕ) (j : Fin p) {m : ℕ}
    (hjm : j.1 + 1 ≤ m) (hm : m ≤ p) :
    x[k, m] j = x[k, j.1 + 1] j := by
  have hp_eq_m : x[k, p] j = x[k, m] j := by
    -- Work backwards from the terminal stage `p`; every later-stage update leaves block `j`
    -- unchanged once the cycle has already passed `j`.
    refine Nat.decreasingInduction' (m := m) (n := p) ?_ hm rfl
    intro n hn_lt hmn hn_eq
    have hjn : j.1 < n := by
      omega
    calc
      x[k, p] j = x[k, n + 1] j := hn_eq
      _ = x[k, n] j :=
        cbpg_block_coordinate_fixed_by_later_stage
          hconvex x0 k j (m := n) hjn hn_lt
  have hp_eq_stage : x[k, p] j = x[k, j.1 + 1] j := by
    -- Apply the same backward argument to the first stage after block `j` is updated.
    refine Nat.decreasingInduction' (m := j.1 + 1) (n := p) ?_ (Nat.succ_le_of_lt j.2) rfl
    intro n hn_lt hjn hn_eq
    have hlt : j.1 < n := by
      omega
    calc
      x[k, p] j = x[k, n + 1] j := hn_eq
      _ = x[k, n] j :=
        cbpg_block_coordinate_fixed_by_later_stage
          hconvex x0 k j (m := n) hlt hn_lt
  -- Both stages agree with the terminal stage on coordinate `j`, so they agree with each other.
  calc
    x[k, m] j = x[k, p] j := hp_eq_m.symm
    _ = x[k, j.1 + 1] j := hp_eq_stage

/-- Helper for Lemma 11.6: the coordinate created when block `j` is updated is exactly the final
coordinate of the next outer iterate. -/
lemma cbpg_block_coordinate_stage_eq_next_iterate
    (k : ℕ) (j : Fin p) :
    x[k, j.1 + 1] j = x[k + 1] j := by
  have hstable :
      x[k, p] j = x[k, j.1 + 1] j :=
    cbpg_block_coordinate_stable_after_update
      hconvex x0 k j (m := p) (Nat.succ_le_of_lt j.2) le_rfl
  -- The terminal inner stage is the next outer iterate by definition of the CBPG cycle.
  calc
    x[k, j.1 + 1] j = x[k, p] j := hstable.symm
    _ = x[k + 1] j := by
      rw [cyclic_block_proximal_gradient_method_succ]

/-- Helper for Lemma 11.6: once the source-faithful convexity-plus-prox argument is carried out,
the squared objective gap at the next CBPG outer iterate is controlled by the squared outer-step
norm and the initial-sublevel radius bound. -/
theorem cbpg_objective_gap_sq_le_step_sq_of_initial_sublevel_radius
    (Rα : PosReal)
    (hRα :
      ∀ ⦃x : (i : Fin p) → Ei i⦄,
        F x ≤ F x[0] →
        infDist x XStar ≤ Rα)
    (k : ℕ) :
    Δ[k + 1] ^ (2 : ℕ) ≤
      (p : ℝ) * (((Lf : ℝ) + (Lmax : ℝ)) ^ (2 : ℕ)) * ((Rα : ℝ) ^ (2 : ℕ)) *
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
  -- Route correction: the stage-domain invariants, the bridge `x_j^{k,j} = x_j^{k+1}`, and the
  -- `toPiLp` tail comparison are the remaining local bridges. The remaining source-faithful work is exactly the
  -- optimizer-side support sum `(11.17)` plus the convex first-order inequality for `f`.
  rcases cbpg_exists_nearest_optimizer hconvex x0 x[k + 1] with
    ⟨xStar, hxStar, hxStar_dist⟩
  let hcomposite := cbpg_toIsConvexCompositeSmoothMinimizationProblem hconvex x0
  have hxStar_value : F xStar = (FOpt : EReal) := by
    -- The fixed nearest optimizer witness already realizes the optimal objective value.
    exact hcomposite.objective_eq_optimalValue_of_mem_optimalSet hxStar
  -- TODO: choose `xStar ∈ XStar`, sum `block_partial_gradient_mapping_support_ineq_real` at
  -- `y = xStar j`, combine that with the convexity estimate for `f`, and then use
  -- the stage-to-outer-step norm bridge together with the radius bound.
  sorry

-- Proof sketch: combine the outer-step sufficient-decrease estimate from
-- `cbpg_sufficient_decrease_outer_step` with the textbook argument using convexity of `f`,
-- blockwise prox optimality, and the block Lipschitz constants to obtain
-- `((F x[k + 1]).toReal - FOpt)^2 ≤ p (L_f + L_max)^2 R^2 ‖x[k + 1] - x[k]‖^2`, where `R`
-- is any radius controlling the initial sublevel set in the distance-to-`XStar` form supplied by
-- Theorem 11.6.
-- Rearranging and substituting the lower bound from equation (11.11) gives the displayed
-- quadratic objective-gap decrease estimate.
/-- Lemma 11.6: under Assumption 11.1 together with the convexity and initial-sublevel radius
bound from Assumption 11.15, every outer cyclic block proximal-gradient step satisfies the
textbook quadratic decrease estimate for any radius `R_α` that bounds the distance from the
initial sublevel set `{x | F(x) ≤ F(x^0)}` to the optimal set `X^*`. -/
theorem cbpg_step_decrease_ge_sq_objective_gap
    (Rα : PosReal)
    (hRα :
      ∀ ⦃x : (i : Fin p) → Ei i⦄,
        F x ≤ F x[0] →
        infDist x XStar ≤ Rα)
    (k : ℕ) :
    F x[k] - F x[k + 1] ≥
      (((cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) : ℝ) : EReal)) := by
  let factor : ℝ :=
    (p : ℝ) * (((Lf : ℝ) + (Lmax : ℝ)) ^ (2 : ℕ)) * ((Rα : ℝ) ^ (2 : ℕ))
  have hp_pos_nat : 0 < p := by
    simpa using Fintype.card_pos_iff.mpr ‹Nonempty (Fin p)›
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp_pos_nat
  have hsum_pos : 0 < (Lf : ℝ) + (Lmax : ℝ) := by
    exact add_pos_of_nonneg_of_pos (show 0 ≤ (Lf : ℝ) by exact_mod_cast Lf.2) (Lmax.2)
  have hsum_sq_pos : 0 < (((Lf : ℝ) + (Lmax : ℝ)) ^ (2 : ℕ)) := by
    simpa [pow_two] using sq_pos_of_pos hsum_pos
  have hR_sq_pos : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    simpa [pow_two] using sq_pos_of_pos Rα.2
  have hfactor_pos : 0 < factor := by
    -- Every factor in the source denominator is positive in the nontrivial block case.
    dsimp [factor]
    positivity
  have hcoef_nonneg : 0 ≤ cbpg_quadratic_gap_constant Lf Li Rα := by
    -- The chapter coefficient is nonnegative because its denominator is positive.
    rw [cbpg_quadratic_gap_constant_def]
    have hden_pos :
        0 < 2 * (p : ℝ) * (((Lf : ℝ) + (Lmax : ℝ)) ^ (2 : ℕ)) * ((Rα : ℝ) ^ (2 : ℕ)) := by
      positivity
    exact (div_nonneg Lmin.2.le hden_pos.le)
  have hgap_sq :
      Δ[k + 1] ^ (2 : ℕ) ≤
        factor * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
    -- Isolate the source-faithful squared-gap estimate and rewrite its scalar factor.
    simpa [factor] using
      cbpg_objective_gap_sq_le_step_sq_of_initial_sublevel_radius
        hconvex x0 Rα hRα k
  have hreal :
      cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) ≤
        ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
    -- Multiply the gap bound by the nonnegative chapter coefficient and simplify the product.
    calc
      cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) ≤
          cbpg_quadratic_gap_constant Lf Li Rα *
            (factor * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hgap_sq hcoef_nonneg
      _ = ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
        rw [cbpg_quadratic_gap_constant_def]
        dsimp [factor]
        have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
        have hsum_ne : ((Lf : ℝ) + (Lmax : ℝ)) ≠ 0 := hsum_pos.ne'
        have hR_ne : (Rα : ℝ) ≠ 0 := ne_of_gt Rα.2
        field_simp [hp_ne, hsum_ne, hR_ne]
  have hereal :
      ((((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≥
        (((cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) : ℝ) : EReal)) := by
    exact_mod_cast hreal
  -- The outer sufficient-decrease owner gives the step-norm lower bound, and the previous
  -- algebra translates that step bound into the displayed quadratic objective-gap decrease.
  exact le_trans hereal (cbpg_sufficient_decrease_outer_step (cbpg_base_problem hconvex) x0 k)

end

end

end
