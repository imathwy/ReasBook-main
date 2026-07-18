import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Algorithm_11_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Lemma_11_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Theorem_11_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Theorem_11_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap11.Lemma_11_7

noncomputable section

universe v

open Metric

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, CompleteSpace (Ei i)] [∀ i, ProperSpace (Ei i)]
variable [Nonempty (Fin p)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

/-- Helper for Theorem 11.7: the Chapter 11 quadratic-gap coefficient
`L_min / (2 p (L_f + L_max)^2 R^2)`. -/
private def cbpg_quadratic_gap_constant
    (Lf : NNReal) (Li : (i : Fin p) → PosReal) (R : PosReal) : ℝ :=
  (cbpg_min_block_stepsize Li : ℝ) /
    (2 * (p : ℝ) * (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) *
      ((R : ℝ) ^ (2 : ℕ)))

/- Theorem 11.7 is `source-facing`: it gives the convex CBPG objective-gap rate. The owner
abstractions already live upstream:
- `CyclicBlockProximalGradientConvexAssumptions` is the Chapter 11 source-facing problem owner;
- `cyclic_block_proximal_gradient_method` is the owner of the CBPG outer iterates;
- `cbpg_quadratic_gap_constant` is the canonical Chapter 11 coefficient
  `L_min / (2 p (L_f + L_max)^2 R_α^2)`;
- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence` and
  `nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence` are the scalar recurrence owners
  from Lemma 11.7.

Primitive data are therefore only the convex CBPG assumptions and the canonical initial datum
`x0 ∈ effective_domain (separableSum g)`. The objective gap is derived API, and the passage from
the CBPG step estimate to the scalar recurrence is a `bridge/view`, not a second wrapper owner. -/

section

variable
  (hconvex : CyclicBlockProximalGradientConvexAssumptions
    f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "hproblem" =>
  hconvex.toBlockProximalGradientAssumptions
local notation "x0I" =>
  hconvex.interior_effective_domain_point x0
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
set_option quotPrecheck false in
local notation "RadiusBound" =>
  fun Rα : PosReal ↦
    ∀ ⦃x⦄,
      F x ≤ F x[0] →
      infDist x XStar ≤ Rα
set_option quotPrecheck false in
local notation "GapBound[" Rα "," k "]" =>
  max
    (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * Δ[0])
    (4 / (cbpg_quadratic_gap_constant Lf Li Rα * ((k - 1 : ℕ) : ℝ)))
set_option quotPrecheck false in
local notation "IterationThreshold[" Rα "," ε "]" =>
  max
      ((2 / Real.log 2) *
        (Real.log (Δ[0]) + Real.log (1 / (ε : ℝ))))
      (4 / (cbpg_quadratic_gap_constant Lf Li Rα * (ε : ℝ))) +
    1

/-- Helper for Theorem 11.7: every auxiliary iterate `x^{k,m}` with `m ≤ p` remains in the
effective domain of the block-separable regularizer. -/
lemma cbpg_inner_stage_mem_effective_domain
    (k : ℕ) (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  simpa using
    cbpg_auxiliary_iterate_mem_effective_domain
      (hconvex.toBlockProximalGradientAssumptions) x0 k m hm

/-- Helper for Theorem 11.7: every outer CBPG iterate remains in the effective domain of the
block-separable regularizer. -/
lemma cbpg_outer_iterate_mem_effective_domain_theorem_11_7
    (k : ℕ) :
    x[k] ∈ effective_domain (separableSum g) := by
  simpa using
    cbpg_inner_stage_mem_effective_domain
      (hconvex := hconvex) (x0 := x0) k 0 (Nat.zero_le p)

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite. -/
lemma cbpg_outer_objective_value_finite
    (k : ℕ) :
    F x[k] ≠ ⊤ ∧ F x[k] ≠ ⊥ := by
  have hxg : x[k] ∈ effective_domain (separableSum g) :=
    cbpg_outer_iterate_mem_effective_domain_theorem_11_7
      (hconvex := hconvex) (x0 := x0) k
  have hxf : x[k] ∈ effective_domain f := by
    -- The regularizer domain lies in `interior (effective_domain f)`, hence `f` is finite there.
    let hbase := hconvex.toBlockProximalGradientAssumptions
    exact interior_subset (hbase.g_effective_domain_subset_interior_f_effective_domain hxg)
  have hf_top : f x[k] ≠ ⊤ := (mem_effective_domain.mp hxf).ne
  have hg_top : separableSum g x[k] ≠ ⊤ := (mem_effective_domain.mp hxg).ne
  have hf_bot : f x[k] ≠ ⊥ :=
    hconvex.toBlockProximalGradientAssumptions.f_ne_bot (x[k])
  have hg_bot : separableSum g x[k] ≠ ⊥ := by
    -- Proper block penalties keep the separable sum away from `-∞`.
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ
      (fun i ↦ g i (x[k] i))
      (fun i _ ↦ (hconvex.toBlockProximalGradientAssumptions.block_g_proper i).ne_bot _)
  constructor
  · simpa [composite_model_objective] using EReal.add_ne_top hf_top hg_top
  · simpa [composite_model_objective] using EReal.add_ne_bot_iff.mpr ⟨hf_bot, hg_bot⟩

/-- Helper for Theorem 11.7: the quadratic CBPG gap coefficient is positive for every positive
radius parameter. -/
lemma cbpg_quadratic_gap_constant_pos
    (Rα : PosReal) :
    0 < cbpg_quadratic_gap_constant Lf Li Rα := by
  have hp_nat : 0 < p := by
    simpa using Fintype.card_pos_iff.mpr ‹Nonempty (Fin p)›
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast hp_nat
  have hsum : 0 < (Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ) := by
    exact add_pos_of_nonneg_of_pos (show 0 ≤ (Lf : ℝ) by exact_mod_cast Lf.2)
      (PosReal.coe_pos (cbpg_max_block_stepsize Li))
  have hsum_sq : 0 < (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) := by
    nlinarith [hsum]
  have hR_sq : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    rw [pow_two]
    exact mul_pos (PosReal.coe_pos Rα) (PosReal.coe_pos Rα)
  have htwo_p : 0 < 2 * (p : ℝ) := by positivity
  have hden :
      0 <
        2 * (p : ℝ) *
          (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) *
          ((Rα : ℝ) ^ (2 : ℕ)) := by
    exact mul_pos (mul_pos htwo_p hsum_sq) hR_sq
  dsimp [cbpg_quadratic_gap_constant]
  exact div_pos (PosReal.coe_pos (cbpg_min_block_stepsize Li)) hden

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite from
above. -/
lemma cbpg_objective_value_ne_top
    (k : ℕ) :
    F x[k] ≠ ⊤ := by
  exact (cbpg_outer_objective_value_finite (hconvex := hconvex) (x0 := x0) k).1

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite from
below. -/
lemma cbpg_objective_value_ne_bot
    (k : ℕ) :
    F x[k] ≠ ⊥ := by
  exact (cbpg_outer_objective_value_finite (hconvex := hconvex) (x0 := x0) k).2

/-- Helper for Theorem 11.7: the CBPG objective gap sequence is nonnegative. -/
lemma cbpg_objective_gap_nonneg
    (k : ℕ) :
    0 ≤ Δ[k] := by
  have hlower : (FOpt : EReal) ≤ F x[k] :=
    hconvex.optimal_value_isGLB.1 ⟨x[k], rfl⟩
  have htop := cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) k
  have hbot := cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) k
  lift (F x[k]) to ℝ using ⟨htop, hbot⟩ with rk
  norm_num at hlower ⊢
  linarith

/-- Helper for Theorem 11.7: once the two consecutive objective values are known to be finite,
their EReal difference is the coercion of the corresponding real difference. -/
lemma cbpg_objective_step_decrease_real_form
    (k : ℕ) :
    F x[k] - F x[k + 1] =
      ((((F x[k]).toReal - (F x[k + 1]).toReal : ℝ)) : EReal) := by
  -- Rewrite both finite objective values as real coercions before using `EReal.coe_sub`.
  have hxk_val :
      F x[k] = (((F x[k]).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) k)
        (cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) k)).symm
  have hxk1_val :
      F x[k + 1] = (((F x[k + 1]).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) (k + 1))
        (cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) (k + 1))).symm
  -- After the coercion rewrite, the EReal subtraction reduces to the real subtraction.
  rw [hxk_val, hxk1_val]
  simp [EReal.coe_sub]

/-- Helper for Theorem 11.7: subtracting two consecutive gaps cancels the common optimal-value
offset and leaves the real difference of the corresponding objective values. -/
lemma cbpg_objective_gap_difference_eq_toReal_difference
    (k : ℕ) :
    Δ[k] - Δ[k + 1] =
      (F x[k]).toReal - (F x[k + 1]).toReal := by
  -- Expand the gap definition and cancel the common `FOpt` term.
  calc
    Δ[k] - Δ[k + 1]
        = ((F x[k]).toReal - FOpt) - ((F x[k + 1]).toReal - FOpt) := by
          rfl
    _ = (F x[k]).toReal - (F x[k + 1]).toReal := by
          ring

/-- Helper for Theorem 11.7: the one-step CBPG decrease estimate induces the scalar quadratic
recurrence for the objective-gap sequence. -/
lemma cbpg_objective_gap_step_recurrence
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (k : ℕ) :
    Δ[k] - Δ[k + 1] ≥
      cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) := by
  -- Route correction: keep the source-faithful plan fixed. The only missing piece is the earlier
  -- Lemma 11.6 owner; the cast-down and cancellation steps are now factored out and verified here.
  -- Convert the one-step EReal decrease estimate from Lemma 11.6 into an inequality in `ℝ`.
  have hstepE :
      (((cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) : ℝ) : EReal)) ≤
        F x[k] - F x[k + 1] := sorry
  have hstep_realE :
      (((cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) : ℝ) : EReal)) ≤
        ((((F x[k]).toReal - (F x[k + 1]).toReal : ℝ)) : EReal) := by
    rw [cbpg_objective_step_decrease_real_form
      (hconvex := hconvex) (x0 := x0) k] at hstepE
    exact hstepE
  have hstep_real :
      (F x[k]).toReal - (F x[k + 1]).toReal ≥
        cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) := by
    simpa [ge_iff_le] using EReal.coe_le_coe_iff.mp hstep_realE
  -- Cancel the common optimal-value offset in the consecutive gap difference.
  calc
    Δ[k] - Δ[k + 1]
        = (F x[k]).toReal - (F x[k + 1]).toReal := by
          simpa using
            cbpg_objective_gap_difference_eq_toReal_difference
              (hconvex := hconvex) (x0 := x0) k
    _ ≥ cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) := hstep_real

/-- Helper for Theorem 11.7: the convex CBPG assumptions supply a radius controlling the initial
sublevel set through the distance-to-`XStar` formulation used in Lemma 11.6. -/
lemma cbpg_exists_initial_sublevel_radius :
    ∃ Rα : PosReal, RadiusBound Rα := by
  have hx0f : (x0 : (i : Fin p) → Ei i) ∈ effective_domain f := by
    let hbase := hconvex.toBlockProximalGradientAssumptions
    exact interior_subset (hbase.g_effective_domain_subset_interior_f_effective_domain x0.2)
  have hf_top : f x0 ≠ ⊤ := (mem_effective_domain.mp hx0f).ne
  have hg_top : separableSum g x0 ≠ ⊤ := (mem_effective_domain.mp x0.2).ne
  have hf_bot : f x0 ≠ ⊥ := hconvex.toBlockProximalGradientAssumptions.f_ne_bot x0
  have hg_bot : separableSum g x0 ≠ ⊥ := by
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ
      (fun i ↦ g i ((x0 : (i : Fin p) → Ei i) i))
      (fun i _ ↦ (hconvex.toBlockProximalGradientAssumptions.block_g_proper i).ne_bot _)
  have hF_top : F x0 ≠ ⊤ := by
    simpa [composite_model_objective] using EReal.add_ne_top hf_top hg_top
  have hF_bot : F x0 ≠ ⊥ := by
    simpa [composite_model_objective] using EReal.add_ne_bot_iff.mpr ⟨hf_bot, hg_bot⟩
  have hF_val : F x0 = (((F x0).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hF_top hF_bot).symm
  have hα_pos : 0 < |(F x0).toReal| + 1 := by
    positivity
  let α : PosReal := ⟨|(F x0).toReal| + 1, hα_pos⟩
  have hα : F x0 ≤ ((α : ℝ) : EReal) := by
    have hle : (F x0).toReal ≤ |(F x0).toReal| + 1 := by
      nlinarith [le_abs_self (F x0).toReal]
    have hleE :
        ((((F x0).toReal : ℝ)) : EReal) ≤
          (((|(F x0).toReal| + 1 : ℝ)) : EReal) := by
      exact_mod_cast hle
    rw [hF_val]
    simpa [α] using hleE
  simpa using
    hconvex.bounded_initial_sublevel_distance_to_optimal_set
      (x0 := (x0 : (i : Fin p) → Ei i)) (α := α) hα

/-- Helper for Theorem 11.7: after setting the scalar recurrence parameter to the reciprocal of
the CBPG quadratic-gap coefficient, the sublinear term from Lemma 11.7 rewrites to the textbook
quantity `4 / (c t)`. -/
lemma cbpg_sublinear_term_eq
    (Rα : PosReal) (t : ℝ) :
    let γ : PosReal :=
      ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
        inv_pos.mpr
          (cbpg_quadratic_gap_constant_pos Rα)⟩
    4 * (γ : ℝ) / t =
      4 / (cbpg_quadratic_gap_constant Lf Li Rα * t) := by
  dsimp
  have hc : cbpg_quadratic_gap_constant Lf Li Rα ≠ 0 :=
    (cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα).ne'
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [hc, ht]

-- Proof sketch: specialize the Chapter 11 quadratic decrease estimate
-- `cbpg_step_decrease_ge_sq_objective_gap` to the gap sequence
-- `a_k = Δ[k]`, derive nonnegativity from the canonical optimal-value
-- owner in `hconvex`, and apply Lemma 11.7's scalar recurrence estimate.
/-- If a radius `R_α` bounds the distance from the initial sublevel set
`{x | F(x) ≤ F(x^0)}` to the optimal set `X^*`, then the objective gap at iteration `k ≥ 2`
is bounded by the maximum of the geometric term
`(1 / 2)^((k - 1) / 2) (F(x^0) - F_opt)` and the sublinear term
`8 p (L_f + L_max)^2 R_α^2 / (L_min (k - 1))`. -/
theorem cbpg_objective_gap_le_max_geometric_or_sublinear_of_initial_sublevel_radius
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (k : ℕ) (hk : 2 ≤ k) :
    Δ[k] ≤ GapBound[Rα,k] := by
  let γ : PosReal :=
    ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
      inv_pos.mpr (cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα)⟩
  have hstep :
      ∀ n : ℕ,
        Δ[n] - Δ[n + 1] ≥ (1 / (γ : ℝ)) * (Δ[n + 1] ^ (2 : ℕ)) := by
    intro n
    simpa [γ, cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα] using
      cbpg_objective_gap_step_recurrence
        (hconvex := hconvex) (x0 := x0) Rα hRα n
  have hmain :=
    _root_.nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := fun n ↦ Δ[n])
      (γ := γ)
      (ha_nonneg := cbpg_objective_gap_nonneg (hconvex := hconvex) (x0 := x0))
      (hstep := hstep)
      hk
  have hsub :
      4 * (γ : ℝ) / ((k - 1 : ℕ) : ℝ) =
        4 / (cbpg_quadratic_gap_constant Lf Li Rα * ((k - 1 : ℕ) : ℝ)) := by
    simpa [γ] using
      cbpg_sublinear_term_eq (Lf := Lf) (Li := Li) (Rα := Rα) (((k - 1 : ℕ) : ℝ))
  rw [hsub] at hmain
  exact hmain

-- Proof sketch: obtain an initial-sublevel radius witness from the canonical bridge
-- `hconvex.bounded_initial_sublevel_distance_to_optimal_set`, then apply the preceding theorem.
/-- Theorem 11.7 (1): under Assumptions 11.1 and 11.15, there exists a radius `R_α` together with
the corresponding initial-sublevel distance witness such that the CBPG objective gap at
iteration `k ≥ 2` is bounded by the maximum of the geometric and sublinear terms with that
`R_α`. -/
theorem cbpg_objective_gap_le_max_geometric_or_sublinear
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ Rα : PosReal,
      RadiusBound Rα ∧
      Δ[k] ≤ GapBound[Rα,k] := by
  rcases cbpg_exists_initial_sublevel_radius (hconvex := hconvex) (x0 := x0) with ⟨Rα, hRα⟩
  exact ⟨Rα, hRα,
    cbpg_objective_gap_le_max_geometric_or_sublinear_of_initial_sublevel_radius
      (hconvex := hconvex) (x0 := x0) Rα hRα k hk⟩

-- Proof sketch: combine the previous maximum bound with the explicit lower bound on `n`. The
-- logarithmic term controls the geometric contribution, and the `1 / ε` term controls the
-- sublinear contribution, yielding `Δ[n] ≤ ε`.
/-- If a radius `R_α` controls the initial sublevel set and the iteration index `n` satisfies the
textbook lower bound involving `ε`, then the CBPG objective gap at step `n` is at most `ε`. -/
theorem cbpg_objective_gap_le_of_iteration_count_bound_of_initial_sublevel_radius
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (ε : PosReal) (n : ℕ)
    (hn : IterationThreshold[Rα,ε] ≤ (n : ℝ)) :
    Δ[n] ≤ ε := by
  let γ : PosReal :=
    ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
      inv_pos.mpr (cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα)⟩
  have hstep :
      ∀ k : ℕ,
        Δ[k] - Δ[k + 1] ≥ (1 / (γ : ℝ)) * (Δ[k + 1] ^ (2 : ℕ)) := by
    intro k
    simpa [γ, cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα] using
      cbpg_objective_gap_step_recurrence
        (hconvex := hconvex) (x0 := x0) Rα hRα k
  have hn' :
      max
          ((2 / Real.log 2) * (Real.log (Δ[0]) + Real.log (1 / (ε : ℝ))))
          (4 * (γ : ℝ) / (ε : ℝ)) +
        1 ≤
        (n : ℝ) := by
    have hsub :
        4 * (γ : ℝ) / (ε : ℝ) =
          4 / (cbpg_quadratic_gap_constant Lf Li Rα * (ε : ℝ)) := by
      simpa [γ] using
        cbpg_sublinear_term_eq (Lf := Lf) (Li := Li) (Rα := Rα) (ε : ℝ)
    simpa [hsub] using hn
  exact
    _root_.nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence
      (a := fun k ↦ Δ[k])
      (γ := γ)
      (ha_nonneg := cbpg_objective_gap_nonneg (hconvex := hconvex) (x0 := x0))
      (hstep := hstep)
      ε
      hn'

-- Proof sketch: extract an initial-sublevel radius witness from the canonical convex CBPG owner
-- and apply the preceding theorem with that witness.
/-- Theorem 11.7 (2): under Assumptions 11.1 and 11.15, there exists a radius `R_α` together with
the corresponding initial-sublevel distance witness such that, whenever the iteration index `n`
satisfies the textbook lower bound with that `R_α`, the objective gap at step `n` is at most
`ε`. -/
theorem cbpg_objective_gap_le_of_iteration_count_bound
    (ε : PosReal) (n : ℕ) :
    ∃ Rα : PosReal,
      RadiusBound Rα ∧
      (IterationThreshold[Rα,ε] ≤ (n : ℝ) →
        Δ[n] ≤ ε) := by
  rcases cbpg_exists_initial_sublevel_radius (hconvex := hconvex) (x0 := x0) with ⟨Rα, hRα⟩
  exact ⟨Rα, hRα, fun hn ↦
    cbpg_objective_gap_le_of_iteration_count_bound_of_initial_sublevel_radius
      (hconvex := hconvex) (x0 := x0) Rα hRα ε n hn⟩

end

end
