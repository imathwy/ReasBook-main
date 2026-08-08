import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Corollary_10_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_14
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
variable [Fact (is_convex_function g)]
variable
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

local notation "F" => composite_model_objective f g

set_option quotPrecheck false in
local notation:max "G[" L "]" => G[L, f, g]

set_option quotPrecheck false in
local notation "B1[" htraj "; " s ", " γ ", " η "]" =>
  uses_proximal_gradient_backtracking_B1_rule
    f g hg_effective_domain_subset_interior_f_effective_domain _ _ htraj s γ η

/- Theorem 10.15 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling identifies the relevant owner abstractions already present in the chapter:
- `Lemma_10_14`, which already isolates the primitive regularity and domain-compatibility data
  actually used by the sufficient-decrease arguments here;
- `is_proximal_gradient_trajectory` from Algorithm 10.1 for the iterate sequence `x^k`;
- `gradient_mapping` from Definition 10.5 and `best_achieved_function_value` from
  Definition 8.8 for the canonical residual observable `x ↦ ‖G_d(x)‖` and its prefix minimum;
- `Function.const` applied to an admissible
  `ProximalGradientConstantStepsizeParameter` from Definition 10.11 for the constant rule;
- `uses_proximal_gradient_backtracking_B1_rule` from Algorithm 10.2 for the B1 rule;
- `IsGLB` for the lower-bound data needed only in clauses (3)-(5).

Triage:
- `source-facing`: Theorem 10.15 itself, whose public statements keep the textbook constant-step
  and B1 cases.
- `core/canonical`: the primitive regularity hypotheses already exposed by Lemma 10.14, together
  with the trajectory, gradient-mapping, running-minimum, constant-map, B1-rule, and `IsGLB`
  owners.
- `bridge/view`: no extra wrapper is introduced; the admissible-rule disjunction and the
  case-dependent coefficients remain theorem-local data. -/

section SufficientDecreaseRule

variable {x : ℕ → E} {L : ℕ → PosReal}
variable (htraj : is_proximal_gradient_trajectory f g x L)
variable (hrule :
  (∃ barL : ProximalGradientConstantStepsizeParameter Lf,
      L = Function.const ℕ (barL : PosReal)) ∨
    ∃ s : PosReal, ∃ γ : ProximalGradientBacktrackingDecreaseFraction,
      ∃ η : ProximalGradientBacktrackingGrowthFactor,
        B1[htraj; s, γ, η])

include hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain htraj hrule

/-- Helper for Theorem 10.15: every positive-index proximal-gradient iterate lies in
`effective_domain g` because it is realized by the prox-gradient operator. -/
lemma proximal_gradient_positive_iterate_mem_effective_domain_g
    (k : ℕ) :
    x (k + 1) ∈ effective_domain g := by
  -- Rewrite the realized successor to the prox-gradient operator output and reuse the Chapter 10
  -- domain-membership lemma for that operator.
  rw [proximal_gradient_trajectory_succ_eq_prox_grad_operator (f := f) (g := g) htraj k]
  exact
    prox_grad_operator_mem_effective_domain_g
      (f := f) (g := g) (L := L k) (x := proximal_gradient_trajectory_iterate htraj k)

omit hf_effective_domain_convex hf_toReal_smooth_on_interior_effective_domain htraj hrule in
/-- Helper for Theorem 10.15: on `effective_domain g`, the composite objective is a finite real
sum of the finite `f`- and `g`-values. -/
lemma proximal_gradient_objective_eq_real_of_mem_effective_domain_g
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) := by
  have hfxPoint : xPoint ∈ effective_domain f := by
    exact interior_subset (hg_effective_domain_subset_interior_f_effective_domain hxPoint)
  have hfx_val :
      f xPoint = ((((f xPoint).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hfxPoint).ne (hf_ne_bot xPoint)).symm
  have hgx_val :
      g xPoint = ((((g xPoint).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne
        (‹IsProperExtendedRealFunction g›.ne_bot xPoint)).symm
  -- Once both summands are finite, the composite objective is just the real-valued sum cast to
  -- `EReal`.
  rw [composite_model_objective_apply, hfx_val, hgx_val]
  simp [EReal.coe_add]

/-- Helper for Theorem 10.15: if the current iterate lies in `effective_domain g`, then the
one-step objective gap is an ordinary real difference cast to `EReal`. -/
lemma proximal_gradient_objective_gap_eq_coe_sub_toReal_of_mem_effective_domain_g
    (k : ℕ) (hxkg : x k ∈ effective_domain g) :
    F (x k) - F (x (k + 1)) =
      (((((F (x k)).toReal - (F (x (k + 1))).toReal : ℝ))) : EReal) := by
  have hxk1g :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj) k
  have hxk_val :
      F (x k) = ((((f (x k)).toReal + (g (x k)).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxkg
  have hxk1_val :
      F (x (k + 1)) = ((((f (x (k + 1))).toReal + (g (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxk1g
  have hxk_toReal :
      (F (x k)).toReal = (f (x k)).toReal + (g (x k)).toReal := by
    rw [hxk_val]
    simpa using EReal.toReal_coe ((f (x k)).toReal + (g (x k)).toReal)
  have hxk1_toReal :
      (F (x (k + 1))).toReal = (f (x (k + 1))).toReal + (g (x (k + 1))).toReal := by
    rw [hxk1_val]
    simpa using EReal.toReal_coe ((f (x (k + 1))).toReal + (g (x (k + 1))).toReal)
  -- Rewrite both objective values to finite real casts and then use the canonical `EReal` cast of
  -- a real difference.
  rw [hxk_toReal, hxk1_toReal, hxk_val, hxk1_val]
  simp [EReal.coe_sub]

omit hrule in
/-- Helper for Theorem 10.15: on a step whose current iterate lies in `effective_domain g`, any
nonnegative real lower bound on the one-step objective gap yields monotonicity. -/
lemma proximal_gradient_objective_step_le_of_mem_effective_domain_g
    {k : ℕ} (hxkg : x k ∈ effective_domain g) {gap : ℝ}
    (hgap :
      F (x k) - F (x (k + 1)) ≥ ((gap : ℝ) : EReal))
    (hgap_nonneg : 0 ≤ gap) :
    F (x (k + 1)) ≤ F (x k) := by
  have hxk_val :
      F (x k) = ((((f (x k)).toReal + (g (x k)).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxkg
  have hxk1g :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj) k
  have hxk1_val :
      F (x (k + 1)) = ((((f (x (k + 1))).toReal + (g (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxk1g
  have hgap_real :
      gap ≤
        ((f (x k)).toReal + (g (x k)).toReal) -
          ((f (x (k + 1))).toReal + (g (x (k + 1))).toReal) := by
    rw [hxk_val, hxk1_val] at hgap
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_sub] using hgap)
  have hmono_real :
      (f (x (k + 1))).toReal + (g (x (k + 1))).toReal ≤
        (f (x k)).toReal + (g (x k)).toReal := by
    nlinarith
  -- Convert the real monotonicity back to the original `EReal` objective values.
  rw [hxk1_val, hxk_val]
  exact EReal.coe_le_coe_iff.mpr hmono_real

omit hrule in
/-- Helper for Theorem 10.15: on a step whose current iterate lies in `effective_domain g`, any
strictly positive real lower bound on the one-step objective gap yields strict decrease. -/
lemma proximal_gradient_objective_step_lt_of_mem_effective_domain_g
    {k : ℕ} (hxkg : x k ∈ effective_domain g) {gap : ℝ}
    (hgap :
      F (x k) - F (x (k + 1)) ≥ ((gap : ℝ) : EReal))
    (hgap_pos : 0 < gap) :
    F (x (k + 1)) < F (x k) := by
  have hxk_val :
      F (x k) = ((((f (x k)).toReal + (g (x k)).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxkg
  have hxk1g :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj) k
  have hxk1_val :
      F (x (k + 1)) = ((((f (x (k + 1))).toReal + (g (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxk1g
  have hgap_real :
      gap ≤
        ((f (x k)).toReal + (g (x k)).toReal) -
          ((f (x (k + 1))).toReal + (g (x (k + 1))).toReal) := by
    rw [hxk_val, hxk1_val] at hgap
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_sub] using hgap)
  have hmono_real :
      (f (x (k + 1))).toReal + (g (x (k + 1))).toReal <
        (f (x k)).toReal + (g (x k)).toReal := by
    nlinarith
  -- Convert the strict real inequality back to the original `EReal` objective values.
  rw [hxk1_val, hxk_val]
  exact EReal.coe_lt_coe_iff.mpr hmono_real

-- Proof sketch: apply the constant-stepsize or B1 sufficient-decrease inequality from
-- Lemma 10.14 at each iteration `k`, and deduce `F(x^(k+1)) ≤ F(x^k)` from the nonnegativity of
-- the squared residual term.
/-- Theorem 10.15 (1): clause (a). Under the primitive regularity hypotheses isolated in
Lemma 10.14, if the proximal-gradient trajectory uses either a constant stepsize
`barL ∈ (L_f / 2, ∞)` or backtracking procedure B1, then the objective sequence `F(x^k)` is
nonincreasing. -/
theorem proximal_gradient_objective_values_antitone :
    Antitone (fun k ↦ F (x k)) := by
  -- Route correction: the earlier generic `EReal` telescope route is unnecessary for clause (a).
  -- The real-gap bridge is only needed on finite steps; the constant-step initial exception
  -- `x^0 ∉ effective_domain g` is handled separately by `F(x^0) = ⊤`.
  refine antitone_nat_of_succ_le ?_
  intro k
  rcases hrule with ⟨barL, hconst⟩ | ⟨s, γ, η, hB1⟩
  · by_cases hk0 : k = 0
    · subst hk0
      by_cases hx0g : x 0 ∈ effective_domain g
      · -- On the finite initial step, the sufficient-decrease inequality gives a nonnegative real
        -- objective gap.
        have hdecrease :=
          proximal_gradient_constant_stepsize_sufficient_decrease
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            barL x (by simpa [hconst] using htraj) 0
        have hcoeff_nonneg :
            0 ≤
              (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
                ‖G[barL] (proximal_gradient_trajectory_iterate
                  (by simpa [hconst] using htraj) 0)‖ ^ (2 : ℕ) := by
          have hnum_nonneg : 0 ≤ (barL : ℝ) - (Lf : ℝ) / 2 := by
            exact sub_nonneg.mpr barL.lower_bound.le
          have hden_nonneg : 0 ≤ (barL : ℝ) ^ (2 : ℕ) := by positivity
          exact mul_nonneg (div_nonneg hnum_nonneg hden_nonneg) (sq_nonneg _)
        exact
          proximal_gradient_objective_step_le_of_mem_effective_domain_g
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := by simpa [hconst] using htraj)
            hx0g hdecrease hcoeff_nonneg
      · -- Outside `effective_domain g`, the initial composite objective is `⊤`, so the first
        -- monotonicity step is immediate because the successor is always feasible.
        have hgx0_top : g (x 0) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa using hx0g))
        have hFx0_top : F (x 0) = ⊤ := by
          simp [composite_model_objective_apply, hgx0_top, hf_ne_bot (x 0)]
        rw [hFx0_top]
        exact le_top
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hxjg :
          x (j + 1) ∈ effective_domain g :=
        proximal_gradient_positive_iterate_mem_effective_domain_g
          (f := f)
          (g := g)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj) j
      have hdecrease :=
        proximal_gradient_constant_stepsize_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          barL x (by simpa [hconst] using htraj) (j + 1)
      have hcoeff_nonneg :
          0 ≤
            (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
              ‖G[barL] (proximal_gradient_trajectory_iterate
                (by simpa [hconst] using htraj) (j + 1))‖ ^ (2 : ℕ) := by
        have hnum_nonneg : 0 ≤ (barL : ℝ) - (Lf : ℝ) / 2 := by
          exact sub_nonneg.mpr barL.lower_bound.le
        have hden_nonneg : 0 ≤ (barL : ℝ) ^ (2 : ℕ) := by positivity
        exact mul_nonneg (div_nonneg hnum_nonneg hden_nonneg) (sq_nonneg _)
      simpa [Nat.add_assoc] using
        proximal_gradient_objective_step_le_of_mem_effective_domain_g
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := by simpa [hconst] using htraj)
          hxjg hdecrease hcoeff_nonneg
  · -- In the B1 branch, every iterate already comes with the required feasibility certificate.
    have hkB1 :
        ∃ hxk : (proximal_gradient_trajectory_iterate htraj k : E) ∈ effective_domain g,
          ∃ i : ℕ,
            is_backtracking_procedure_B1_index
              f g s γ η
              hg_effective_domain_subset_interior_f_effective_domain
              ⟨(proximal_gradient_trajectory_iterate htraj k : E), hxk⟩ i ∧
            L k = proximal_gradient_backtracking_trial_stepsize s η i := hB1 k
    rcases hkB1 with ⟨hxk, i, hi, hLk⟩
    have hdecrease :=
      proximal_gradient_backtracking_B1_sufficient_decrease
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot := hf_ne_bot)
        (hf_effective_domain_convex := hf_effective_domain_convex)
        (hg_effective_domain_subset_interior_f_effective_domain :=
          hg_effective_domain_subset_interior_f_effective_domain)
        (hf_toReal_smooth_on_interior_effective_domain :=
          hf_toReal_smooth_on_interior_effective_domain)
        s γ η x L htraj hB1 k
    have hcoeff_nonneg :
        0 ≤
          ((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))) *
            ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) := by
      have hden_pos :
          0 < max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
        exact lt_of_lt_of_le s.2 (le_max_left _ _)
      exact mul_nonneg (div_nonneg (le_of_lt γ.1.2) (le_of_lt hden_pos)) (sq_nonneg _)
    exact
      proximal_gradient_objective_step_le_of_mem_effective_domain_g
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot := hf_ne_bot)
        (hf_effective_domain_convex := hf_effective_domain_convex)
        (hg_effective_domain_subset_interior_f_effective_domain :=
          hg_effective_domain_subset_interior_f_effective_domain)
        (hf_toReal_smooth_on_interior_effective_domain :=
          hf_toReal_smooth_on_interior_effective_domain)
        (htraj := htraj)
        (by simpa [proximal_gradient_trajectory_iterate] using hxk)
        hdecrease hcoeff_nonneg

section

variable [FiniteDimensional ℝ E]

/-- Helper for Theorem 10.15: if the gradient mapping vanishes at the `k`-th iterate, then the
proximal-gradient update fixes that iterate. -/
lemma proximal_gradient_iterate_succ_eq_self_of_gradient_mapping_eq_zero
    (k : ℕ)
    (hzero : G[L k] (proximal_gradient_trajectory_iterate htraj k) = 0) :
    x (k + 1) = x k := by
  have hfixed :
      T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) =
        (proximal_gradient_trajectory_iterate htraj k : E) := by
    -- Zero residual means the prox-gradient operator leaves the current iterate unchanged.
    rw [gradient_mapping_apply] at hzero
    rcases smul_eq_zero.mp hzero with hLzero | hsub
    · exact False.elim ((L k).2.ne' hLzero)
    · exact (sub_eq_zero.mp hsub).symm
  -- Rewrite the realized successor as the prox-gradient operator output and then use the fixed
  -- point identity.
  calc
    x (k + 1) = T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) := by
      exact proximal_gradient_trajectory_succ_eq_prox_grad_operator (f := f) (g := g) htraj k
    _ = (proximal_gradient_trajectory_iterate htraj k : E) := hfixed
    _ = x k := rfl

/-- Helper for Theorem 10.15: vanishing of the gradient mapping at the `k`-th iterate is
equivalent to stationarity of that iterate for the composite objective. -/
lemma proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
    (L0 : PosReal) (k : ℕ) :
    G[L0] (proximal_gradient_trajectory_iterate htraj k) = 0 ↔
      is_stationary_point f g (x k) := by
  let xk := proximal_gradient_trajectory_iterate htraj k
  have hdiff : is_differentiable_at f (xk : E) :=
    is_differentiable_at_of_mem_interior_effective_domain
      hf_ne_bot
      hf_toReal_smooth_on_interior_effective_domain
      xk.property
  -- The Chapter 10 stationarity bridge applies directly to the realized iterate `x^k`.
  simpa [xk, proximal_gradient_trajectory_iterate] using
    (gradient_mapping_eq_zero_iff_is_stationary_point
      (f := f) (g := g) L0 xk hdiff)

-- Proof sketch: in each admissible stepsize regime, Lemma 10.14 identifies strict decrease with
-- nonvanishing of the appropriate gradient mapping. Then use Theorem 10.7 to rewrite vanishing of
-- that gradient mapping at `x^k` as the Chapter 3 stationary-point condition.
/-- Theorem 10.15 (2): clause (a). Under the same regularity hypotheses, the one-step decrease is
strict exactly when the current iterate `x^k` is not stationary for the composite problem
`min_x {f(x) + g(x)}`. -/
theorem proximal_gradient_step_strict_decrease_iff_not_stationary
    (k : ℕ) :
    F (x (k + 1)) < F (x k) ↔
      ¬ is_stationary_point f g (x k) := by
  -- Route correction: strict decrease is read from the same finite-gap bridge as clause (1), with
  -- the exceptional constant-step initial case again discharged by `F(x^0) = ⊤`.
  rcases hrule with ⟨barL, hconst⟩ | ⟨s, γ, η, hB1⟩
  · constructor
    · intro hlt hstat
      have hzero :
          G[barL] (proximal_gradient_trajectory_iterate
            (by simpa [hconst] using htraj) k) = 0 := by
        exact
          (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := by simpa [hconst] using htraj)
            (L0 := barL) (k := k)).mpr hstat
      have hfixed :
          x (k + 1) = x k :=
        proximal_gradient_iterate_succ_eq_self_of_gradient_mapping_eq_zero
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := by simpa [hconst] using htraj)
          k hzero
      rw [hfixed] at hlt
      exact (lt_irrefl _ hlt).elim
    · intro hnotstat
      by_cases hk0 : k = 0
      · subst hk0
        by_cases hx0g : x 0 ∈ effective_domain g
        · have hdecrease :=
            proximal_gradient_constant_stepsize_sufficient_decrease
              (f := f)
              (g := g)
              (Lf := Lf)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              barL x (by simpa [hconst] using htraj) 0
          have hnonzero :
              G[barL] (proximal_gradient_trajectory_iterate
                (by simpa [hconst] using htraj) 0) ≠ 0 := by
            intro hzero
            exact hnotstat <|
              (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
                (f := f)
                (g := g)
                (Lf := Lf)
                (hf_ne_bot := hf_ne_bot)
                (hf_effective_domain_convex := hf_effective_domain_convex)
                (hg_effective_domain_subset_interior_f_effective_domain :=
                  hg_effective_domain_subset_interior_f_effective_domain)
                (hf_toReal_smooth_on_interior_effective_domain :=
                  hf_toReal_smooth_on_interior_effective_domain)
                (htraj := by simpa [hconst] using htraj)
                (L0 := barL) (k := 0)).mp hzero
          have hcoeff_pos :
              0 <
                (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
                  ‖G[barL] (proximal_gradient_trajectory_iterate
                    (by simpa [hconst] using htraj) 0)‖ ^ (2 : ℕ) := by
            have hnum_pos : 0 < (barL : ℝ) - (Lf : ℝ) / 2 := by
              exact sub_pos.mpr barL.lower_bound
            have hden_pos : 0 < (barL : ℝ) ^ (2 : ℕ) := by
              nlinarith [show 0 < ((barL : PosReal) : ℝ) from (barL : PosReal).2]
            have hnorm_sq_pos :
                0 <
                  ‖G[barL] (proximal_gradient_trajectory_iterate
                    (by simpa [hconst] using htraj) 0)‖ ^ (2 : ℕ) := by
              exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hnonzero)
            exact mul_pos (div_pos hnum_pos hden_pos) hnorm_sq_pos
          exact
            proximal_gradient_objective_step_lt_of_mem_effective_domain_g
              (f := f)
              (g := g)
              (Lf := Lf)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              (htraj := by simpa [hconst] using htraj)
              hx0g hdecrease hcoeff_pos
        · have hgx0_top : g (x 0) = ⊤ := by
            exact le_antisymm le_top (not_lt.mp (by simpa using hx0g))
          have hFx0_top : F (x 0) = ⊤ := by
            simp [composite_model_objective_apply, hgx0_top, hf_ne_bot (x 0)]
          have hx1g :
              x 1 ∈ effective_domain g :=
            proximal_gradient_positive_iterate_mem_effective_domain_g
              (f := f)
              (g := g)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              (htraj := htraj) 0
          have hFx1_val :
              F (x 1) = ((((f (x 1)).toReal + (g (x 1)).toReal : ℝ)) : EReal) :=
            proximal_gradient_objective_eq_real_of_mem_effective_domain_g
              (f := f)
              (g := g)
              (hf_ne_bot := hf_ne_bot)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              hx1g
          rw [hFx1_val, hFx0_top]
          simpa using EReal.coe_lt_top ((f (x 1)).toReal + (g (x 1)).toReal)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have hxjg :
            x (j + 1) ∈ effective_domain g :=
          proximal_gradient_positive_iterate_mem_effective_domain_g
            (f := f)
            (g := g)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := htraj) j
        have hdecrease :=
          proximal_gradient_constant_stepsize_sufficient_decrease
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            barL x (by simpa [hconst] using htraj) (j + 1)
        have hnonzero :
            G[barL] (proximal_gradient_trajectory_iterate
              (by simpa [hconst] using htraj) (j + 1)) ≠ 0 := by
          intro hzero
          exact hnotstat <|
            (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
              (f := f)
              (g := g)
              (Lf := Lf)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              (htraj := by simpa [hconst] using htraj)
              (L0 := barL) (k := j + 1)).mp hzero
        have hcoeff_pos :
            0 <
              (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
                ‖G[barL] (proximal_gradient_trajectory_iterate
                  (by simpa [hconst] using htraj) (j + 1))‖ ^ (2 : ℕ) := by
          have hnum_pos : 0 < (barL : ℝ) - (Lf : ℝ) / 2 := by
            exact sub_pos.mpr barL.lower_bound
          have hden_pos : 0 < (barL : ℝ) ^ (2 : ℕ) := by
            nlinarith [show 0 < ((barL : PosReal) : ℝ) from (barL : PosReal).2]
          have hnorm_sq_pos :
              0 <
                ‖G[barL] (proximal_gradient_trajectory_iterate
                  (by simpa [hconst] using htraj) (j + 1))‖ ^ (2 : ℕ) := by
            exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hnonzero)
          exact mul_pos (div_pos hnum_pos hden_pos) hnorm_sq_pos
        simpa [Nat.add_assoc] using
          proximal_gradient_objective_step_lt_of_mem_effective_domain_g
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := by simpa [hconst] using htraj)
            hxjg hdecrease hcoeff_pos
  · constructor
    · intro hlt hstat
      have hzero :
          G[L k] (proximal_gradient_trajectory_iterate htraj k) = 0 := by
        exact
          (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := htraj)
            (L0 := L k) (k := k)).mpr hstat
      have hfixed :
          x (k + 1) = x k :=
        proximal_gradient_iterate_succ_eq_self_of_gradient_mapping_eq_zero
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj)
          k hzero
      rw [hfixed] at hlt
      exact (lt_irrefl _ hlt).elim
    · intro hnotstat
      have hkB1 :
          ∃ hxk : (proximal_gradient_trajectory_iterate htraj k : E) ∈ effective_domain g,
            ∃ i : ℕ,
              is_backtracking_procedure_B1_index
                f g s γ η
                hg_effective_domain_subset_interior_f_effective_domain
                ⟨(proximal_gradient_trajectory_iterate htraj k : E), hxk⟩ i ∧
              L k = proximal_gradient_backtracking_trial_stepsize s η i := hB1 k
      rcases hkB1 with ⟨hxk, i, hi, hLk⟩
      have hdecrease :=
        proximal_gradient_backtracking_B1_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          s γ η x L htraj hB1 k
      have hnonzero :
          G[s] (proximal_gradient_trajectory_iterate htraj k) ≠ 0 := by
        intro hzero
        exact hnotstat <|
          (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := htraj)
            (L0 := s) (k := k)).mp hzero
      have hden_pos :
          0 < max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
        exact lt_of_lt_of_le s.2 (le_max_left _ _)
      have hcoeff_pos :
          0 <
            ((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))) *
              ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) := by
        have hnorm_sq_pos :
            0 < ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) := by
          exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hnonzero)
        exact mul_pos (div_pos γ.1.2 hden_pos) hnorm_sq_pos
      exact
        proximal_gradient_objective_step_lt_of_mem_effective_domain_g
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj)
          (by simpa [proximal_gradient_trajectory_iterate] using hxk)
          hdecrease hcoeff_pos

end

end SufficientDecreaseRule

section LowerBound

variable {FOpt : ℝ}
variable
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

set_option quotPrecheck false in
local notation "R[" htraj "; " d ", " k "]" =>
  best_achieved_function_value
    (fun y ↦ ‖G[d] y‖) (proximal_gradient_trajectory_iterate htraj) k

/-- Helper for Theorem 10.15: the squared running-best residual on a prefix is bounded above by
the average of the squared residuals on that prefix. -/
lemma best_residual_sq_mul_prefix_length_le_sum
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (d : PosReal) (k : ℕ) :
    (k + 1 : ℝ) * R[htraj; d, k] ^ (2 : ℕ) ≤
      Finset.sum (Finset.range (k + 1))
        (fun n ↦ ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
  have hbest_nonneg : 0 ≤ R[htraj; d, k] := by
    -- The running minimum is attained by one prefix residual norm, hence is nonnegative.
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image
          fun n ↦ ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖)
        (objective_value_prefix_nonempty
          (fun y ↦ ‖G[d] y‖) (proximal_gradient_trajectory_iterate htraj) k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1),
        R[htraj; d, k] ^ (2 : ℕ) ≤
          ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ) := by
    intro n hn
    have hbest_le :=
      best_achieved_function_value_le_objective_value
        (f := fun y ↦ ‖G[d] y‖) (proximal_gradient_trajectory_iterate htraj) k n hn
    nlinarith [hbest_nonneg, norm_nonneg (G[d] (proximal_gradient_trajectory_iterate htraj n)),
      hbest_le]
  -- Summing the pointwise lower bound across the whole prefix yields the structural estimate.
  calc
    (k + 1 : ℝ) * R[htraj; d, k] ^ (2 : ℕ) =
        Finset.sum (Finset.range (k + 1)) (fun _ ↦ R[htraj; d, k] ^ (2 : ℕ)) := by
      simp
    _ ≤ Finset.sum (Finset.range (k + 1))
          (fun n ↦ ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
      exact Finset.sum_le_sum hpointwise

/-- Helper for Theorem 10.15: a real-valued antitone sequence that is bounded below has
successive differences converging to `0`. -/
lemma objective_gap_tendsto_zero_of_antitone_bddBelow
    {φ : ℕ → ℝ}
    (hanti : Antitone φ)
    (hbelow : BddBelow (Set.range φ)) :
    Filter.Tendsto (fun k ↦ φ k - φ (k + 1)) Filter.atTop (nhds 0) := by
  let ℓ : ℝ := ⨅ k, φ k
  have hobj :
      Filter.Tendsto (fun k ↦ φ k) Filter.atTop (nhds ℓ) :=
    tendsto_atTop_ciInf hanti hbelow
  have hobj_shift :
      Filter.Tendsto (fun k ↦ φ (k + 1)) Filter.atTop (nhds ℓ) := by
    have hshift :
        Filter.Tendsto (fun k : ℕ ↦ k + 1) Filter.atTop Filter.atTop :=
      (show StrictMono (fun k : ℕ ↦ k + 1) from
        fun a b hab ↦ Nat.add_lt_add_right hab 1).tendsto_atTop
    simpa [ℓ] using hobj.comp hshift
  -- Subtracting the shifted copy leaves a sequence converging to `ℓ - ℓ = 0`.
  simpa [ℓ] using hobj.sub hobj_shift

/-- Helper for Theorem 10.15: a finite composite-objective gap to the lower bound `FOpt` is the
cast of the corresponding real difference. -/
lemma proximal_gradient_objective_minus_FOpt_eq_coe_sub_toReal_of_mem_effective_domain_g
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    ((((F xPoint).toReal - FOpt : ℝ) : EReal)) =
      F xPoint - (FOpt : EReal) := by
  have hxPoint_val :
      F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hf_ne_bot_local)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      hxPoint
  have hxPoint_toReal :
      (F xPoint).toReal = (f xPoint).toReal + (g xPoint).toReal := by
    rw [hxPoint_val]
    simpa using EReal.toReal_coe ((f xPoint).toReal + (g xPoint).toReal)
  -- Rewrite the finite objective value through its real representative before subtracting `FOpt`.
  rw [hxPoint_toReal, hxPoint_val]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.15: any feasible iterate has composite objective value at least the
optimal lower bound `FOpt`. -/
lemma proximal_gradient_toReal_ge_FOpt_of_isGLB
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    FOpt ≤ (F xPoint).toReal := by
  have hxPoint_val :
      F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hf_ne_bot_local)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      hxPoint
  have hxPoint_toReal :
      (F xPoint).toReal = (f xPoint).toReal + (g xPoint).toReal := by
    rw [hxPoint_val]
    simpa using EReal.toReal_coe ((f xPoint).toReal + (g xPoint).toReal)
  have hxPoint_finite :
      (((F xPoint).toReal : ℝ) : EReal) = F xPoint := by
    rw [hxPoint_toReal, hxPoint_val]
  have hlower : (FOpt : EReal) ≤ F xPoint := hFOpt.1 ⟨xPoint, rfl⟩
  -- Once the feasible objective value is known to be finite, the `EReal` lower bound reads as a
  -- plain real inequality.
  rw [← hxPoint_finite] at hlower
  exact EReal.coe_le_coe_iff.mp hlower

/-- Helper for Theorem 10.15: converting a one-step `EReal` sufficient-decrease estimate to the
finite real layer only requires feasibility of the current iterate. -/
lemma proximal_gradient_real_step_gap_lower_bound_of_mem_effective_domain_g
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex_local : Convex ℝ (effective_domain f))
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    (hf_smooth_local :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) (hxkg : x k ∈ effective_domain g) {gap : ℝ}
    (hgap :
      F (x k) - F (x (k + 1)) ≥ ((gap : ℝ) : EReal)) :
    gap ≤ (F (x k)).toReal - (F (x (k + 1))).toReal := by
  have hgap' : ((gap : ℝ) : EReal) ≤ F (x k) - F (x (k + 1)) := by
    simpa using hgap
  -- The objective-gap bridge isolates the whole `EReal` transport in one rewrite.
  have hgap'' :
      ((gap : ℝ) : EReal) ≤
        ((((F (x k)).toReal - (F (x (k + 1))).toReal : ℝ)) : EReal) := by
    have htmp : ((gap : ℝ) : EReal) ≤ F (x k) - F (x (k + 1)) := hgap'
    rw [proximal_gradient_objective_gap_eq_coe_sub_toReal_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (Lf := Lf)
      (hf_ne_bot := hf_ne_bot_local)
      (hf_effective_domain_convex := hf_effective_domain_convex_local)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      (hf_toReal_smooth_on_interior_effective_domain := hf_smooth_local)
      (htraj := htraj)
      k hxkg] at htmp
    exact htmp
  exact EReal.coe_le_coe_iff.mp hgap''

/-- Helper for Theorem 10.15: every iterate produced by backtracking rule `B1` is feasible for
the nonsmooth term `g`. -/
lemma proximal_gradient_backtracking_iterate_mem_effective_domain_g
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : B1[htraj; s, γ, η])
    (k : ℕ) :
    x k ∈ effective_domain g := by
  rcases hB1 k with ⟨hxk, _, _, _⟩
  simpa [proximal_gradient_trajectory_iterate] using hxk

/-- Helper for Theorem 10.15: in the constant-stepsize regime, each positive iterate satisfies
the real sufficient-decrease inequality used in clauses `(b)` and `(c)`. -/
lemma proximal_gradient_constant_stepsize_real_sufficient_decrease
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x (Function.const ℕ barL))
    (k : ℕ) :
    (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
        ‖G[barL] (proximal_gradient_trajectory_iterate htraj (k + 1))‖ ^ (2 : ℕ) ≤
      (F (x (k + 1))).toReal - (F (x (k + 2))).toReal := by
  -- TODO: convert Lemma 10.14 at index `k + 1` through the finite-gap adapter above.
  sorry

/-- Helper for Theorem 10.15: in the backtracking-B1 regime, each iterate satisfies the real
sufficient-decrease inequality used in clauses `(b)` and `(c)`. -/
lemma proximal_gradient_backtracking_B1_real_sufficient_decrease
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : B1[htraj; s, γ, η])
    (k : ℕ) :
    (γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) *
        ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) ≤
      (F (x k)).toReal - (F (x (k + 1))).toReal := by
  -- TODO: convert the B1 sufficient-decrease estimate through the finite-gap adapter above.
  sorry

-- Proof sketch: the sufficient-decrease estimate from Lemma 10.14 gives
-- `F(x^k) - F(x^(k+1)) ≥ M ‖G_d(x^k)‖²`. If `FOpt` is the greatest lower bound of the composite
-- objective, then `F(x^k)` is bounded below, so its successive differences tend to `0`, forcing
-- `G_d(x^k) → 0`.
/-- Theorem 10.15 (3): clause (b), constant-step case. If the proximal-gradient trajectory uses
the constant stepsize `barL ∈ (L_f / 2, ∞)` and `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the corresponding residual sequence `G_barL(x^k)` converges to `0`. -/
theorem proximal_gradient_constant_stepsize_residual_tendsto_zero
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal)) :
    Filter.Tendsto
      (fun k ↦ G[barL] (proximal_gradient_trajectory_iterate htraj k))
      Filter.atTop (nhds 0) := by
  -- TODO: run the shifted-tail real proof using
  -- `proximal_gradient_constant_stepsize_real_sufficient_decrease`.
  sorry

-- Proof sketch: the B1 sufficient-decrease estimate from Lemma 10.14 gives
-- `F(x^k) - F(x^(k+1)) ≥ M ‖G_s(x^k)‖²` with
-- `M = γ / max {s, η L_f / (2 (1 - γ))}`. If `FOpt` is the greatest lower bound of the
-- composite objective, then `F(x^k)` is bounded below, so its successive differences tend to
-- `0`, forcing `G_s(x^k) → 0`.
/-- Theorem 10.15 (3): clause (b), backtracking-B1 case. If the trajectory uses backtracking
procedure B1 with parameters `(s, γ, η)` and `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the corresponding residual sequence `G_s(x^k)` converges to `0`. -/
theorem proximal_gradient_backtracking_B1_residual_tendsto_zero
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : B1[htraj; s, γ, η])
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal)) :
    Filter.Tendsto
      (fun k ↦ G[s] (proximal_gradient_trajectory_iterate htraj k))
      Filter.atTop (nhds 0) := by
  -- TODO: run the unshifted real proof using
  -- `proximal_gradient_backtracking_B1_real_sufficient_decrease`.
  sorry

section

-- Proof sketch: sum the sufficient-decrease inequality from Lemma 10.14 over `n = 0, ..., k`,
-- telescope the objective values, and bound the sum below by `(k + 1)` times the squared running
-- minimum residual norm.
/-- Theorem 10.15 (4): clause (c), constant-step case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the squared complexity bound holds:
`M (k + 1) (min_{0 ≤ n ≤ k} ‖G_barL(x^n)‖)^2 ≤ F(x^0) - F_opt`, where
`M = ((barL : ℝ) - L_f / 2) / barL^2`. -/
theorem proximal_gradient_constant_stepsize_best_residual_norm_sq_le_objective_gap
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    (k : ℕ) :
    (((((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) * (k + 1 : ℝ) *
        R[htraj; barL, k] ^ (2 : ℕ) :
        ℝ) : EReal) ≤
      F (x 0) - (FOpt : EReal) := by
  -- TODO: telescope the real one-step inequalities over the prefix and rewrite the initial gap
  -- through `proximal_gradient_objective_minus_FOpt_eq_coe_sub_toReal_of_mem_effective_domain_g`.
  sorry

-- Proof sketch: sum the B1 sufficient-decrease inequality from Lemma 10.14 over
-- `n = 0, ..., k`, telescope the objective values, and bound the sum below by `(k + 1)` times
-- the squared running minimum residual norm for the canonical B1 residual `G_s`.
/-- Theorem 10.15 (4): clause (c), backtracking-B1 case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the squared complexity bound holds:
`M (k + 1) (min_{0 ≤ n ≤ k} ‖G_s(x^n)‖)^2 ≤ F(x^0) - F_opt`, where
`M = γ / max {s, η L_f / (2 (1 - γ))}`. -/
theorem proximal_gradient_backtracking_B1_best_residual_norm_sq_le_objective_gap
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : B1[htraj; s, γ, η])
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    (k : ℕ) :
    (((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) *
        (k + 1 : ℝ) *
          R[htraj; s, k] ^ (2 : ℕ) :
        ℝ) : EReal) ≤
      F (x 0) - (FOpt : EReal) := by
  -- TODO: telescope the B1 real one-step inequalities over the prefix and rewrite the initial
  -- gap through `proximal_gradient_objective_minus_FOpt_eq_coe_sub_toReal_of_mem_effective_domain_g`.
  sorry

end

section

variable [FiniteDimensional ℝ E]

-- Proof sketch: let `xBar` be a cluster point of the trajectory. The Lipschitz estimate from
-- Lemma 10.10 controls `‖G_d(xBar) - G_d(x^{k_j})‖` along a subsequence converging to `xBar`, and
-- clause (3) gives `G_d(x^{k_j}) → 0`; hence `G_d(xBar) = 0`. Theorem 10.7 then turns vanishing
-- of the gradient mapping into stationarity.
/-- Theorem 10.15 (5): clause (d), constant-step case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then every sequential limit point of a proximal-gradient trajectory
generated with the constant stepsize `barL ∈ (L_f / 2, ∞)` is a stationary point of the
composite problem `min_x {f(x) + g(x)}`. -/
theorem proximal_gradient_constant_stepsize_cluster_point_is_stationary
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    {xBar : E} (hxBar : MapClusterPt xBar Filter.atTop x) :
    is_stationary_point f g xBar := by
  -- TODO: prove that a cluster point of the feasible tail belongs to `interior (effective_domain f)`;
  -- then `cluster_point_residual_eq_zero_of_lipschitz` and Theorem 10.7 close the source proof.
  sorry

-- Proof sketch: let `xBar` be a cluster point of the trajectory. The Lipschitz estimate from
-- Lemma 10.10 controls `‖G_s(xBar) - G_s(x^{k_j})‖` along a subsequence converging to `xBar`, and
-- clause (3) gives `G_s(x^{k_j}) → 0`; hence `G_s(xBar) = 0`. Theorem 10.7 then turns vanishing
-- of the gradient mapping into stationarity.
/-- Theorem 10.15 (5): clause (d), backtracking-B1 case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then every sequential limit point of a proximal-gradient trajectory
generated with backtracking procedure B1 is a stationary point of the composite problem
`min_x {f(x) + g(x)}`. -/
theorem proximal_gradient_backtracking_B1_cluster_point_is_stationary
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : B1[htraj; s, γ, η])
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    {xBar : E} (hxBar : MapClusterPt xBar Filter.atTop x) :
    is_stationary_point f g xBar := by
  -- TODO: prove that a B1 cluster point lies in `interior (effective_domain f)`; after that, the
  -- residual-zero helper and Theorem 10.7 finish the source argument verbatim.
  sorry

end

end LowerBound

end

end
