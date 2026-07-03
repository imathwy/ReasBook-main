import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_44 (from Chap03) -/
universe u

open scoped BigOperators EuclideanOrthant

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-
Definition 3.44 lies in the finite-constraint Lagrangian-duality domain.

Sampled owner-style declarations in this domain:
* `LagrangianProblem.lagrangian`, `dualFunction`, `dualFeasibleSet`, and `dualOptimalValue` in
  `Chap01/Definition_1_10_2`, the Chapter 1 owner API for the textbook Lagrangian, dual
  function, and dual optimal value;
* `SetConstrainedMinimizationProblem.unconstrained` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_3`
  and `Chap01/Definition_1_3_7`, the canonical ambient minimization owner used to define
  `problem.dualFunction`;
* `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the owner for the nonnegative multiplier orthant.

Best owner abstraction:
* source-facing: the textbook Lagrangian-duality formulas of Definition 3.44;
* core/canonical: `problem : LagrangianProblem Q m`;
* bridge/view: the explicit sum, infimum, and orthant-supremum expansions below.

Primitive data:
* `problem.objective`
* `problem.constraints`

Derived API:
* `problem.constraintVector`
* `problem.lagrangian`
* `problem.dualFunction`
* `problem.dualDomain`
* `problem.dualFeasibleSet`
* `problem.dualOptimalValue`

The owner declarations already live upstream in Chapter 1, so this file should recall those
owners directly and keep only the source-facing expansion formulas as companions. -/
/-
Definition 3.44: the textbook Lagrangian is the canonical owner `problem.lagrangian`. -/
recall lagrangian (problem : LagrangianProblem Q m) (x : Q) (l : Λ) : ℝ

/-
Definition 3.44: the textbook dual function is the canonical owner `problem.dualFunction`. -/
recall dualFunction (problem : LagrangianProblem Q m) (l : Λ) : EReal

/-
Definition 3.44: the textbook dual optimal value is the canonical owner
`problem.dualOptimalValue`. -/
recall dualOptimalValue (problem : LagrangianProblem Q m) : EReal

/-- Helper for Definition 3.44: the inner product with the constraint vector expands as the
coordinatewise weighted sum of the scalar constraint values. -/
lemma inner_constraintVector_eq_sum
    (problem : LagrangianProblem Q m) (x : Q) (l : Λ) :
    inner ℝ l (problem.constraintVector x) =
      ∑ j : Fin m, l j * problem.constraints j x := by
  -- Rewrite the Euclidean inner product as the coordinatewise finite sum.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Replace the constraint-vector coordinate by the underlying scalar constraint value.
  simpa [problem.constraintVector_apply] using
    (RCLike.inner_apply' (l j) (problem.constraints j x))

/-- The Lagrangian evaluates to the objective plus the weighted sum of the constraint values. -/
-- Proof sketch: unfold `LagrangianProblem.lagrangian`, rewrite the inner product on
-- `EuclideanSpace ℝ (Fin m)` as a finite sum, and then identify the coordinates of
-- `problem.constraintVector x` with the constraint functions `problem.constraints j x`.
theorem lagrangian_eq_objective_add_sum
    (problem : LagrangianProblem Q m) (x : Q) (l : Λ) :
    problem.lagrangian x l =
      problem.objective x + ∑ j : Fin m, l j * problem.constraints j x := by
  -- Unfold the owner Lagrangian and rewrite its inner-product term by the coordinate formula.
  rw [LagrangianProblem.lagrangian, problem.coe_apply, inner_constraintVector_eq_sum]

/-- The project records the textbook dual function as the extended-real infimum of the
Lagrangian over the decision set. -/
-- Proof sketch: this is the defining equation of `problem.dualFunction`, obtained by unfolding
-- the owner definition of the dual function.
theorem dualFunction_eq_sInf_range_lagrangian
    (problem : LagrangianProblem Q m) (l : Λ) :
    problem.dualFunction l =
      sInf (Set.range fun x : Q ↦ (problem.lagrangian x l : EReal)) := by
  simpa [LagrangianProblem.dualFunction, SetConstrainedMinimizationProblem.unconstrained] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image
      (SetConstrainedMinimizationProblem.unconstrained fun x : Q ↦ problem.lagrangian x l))

/-- Helper for Definition 3.44: multipliers outside the dual domain contribute the value `⊥` to
the dual function. -/
lemma dualFunction_eq_bot_of_not_mem_dualDomain
    (problem : LagrangianProblem Q m) {l : Λ} (hl : l ∉ problem.dualDomain) :
    problem.dualFunction l = ⊥ := by
  -- Outside `dualDomain`, the defining inequality `⊥ < ψ(l)` fails, so the value must be `⊥`.
  exact le_bot_iff.mp <| le_of_not_gt <| by
    simpa [problem.mem_dualDomain_iff] using hl

/-- Helper for Definition 3.44: every dual value attained on the nonnegative orthant is either
`⊥` or already attained on the dual-feasible set. -/
lemma dualFunction_image_nonnegativeOrthant_subset_insert_bot_dualFeasibleSet
    (problem : LagrangianProblem Q m) :
    problem.dualFunction '' ℝ₊^m ⊆
      insert ⊥ (problem.dualFunction '' problem.dualFeasibleSet) := by
  intro y hy
  rcases hy with ⟨l, hl_nonneg, rfl⟩
  by_cases hdom : l ∈ problem.dualDomain
  · -- In the dual domain, nonnegativity is exactly dual feasibility.
    right
    refine ⟨l, ?_, rfl⟩
    rw [problem.mem_dualFeasibleSet_iff]
    refine ⟨hdom, ?_⟩
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hl_nonneg
  · -- Outside the dual domain, the image point collapses to `⊥`.
    left
    exact problem.dualFunction_eq_bot_of_not_mem_dualDomain hdom

/-- The dual optimal value is the supremum of the dual function over the nonnegative orthant. -/
-- Proof sketch: compare the source-level supremum over `ℝ_+^m` with the owner's supremum over
-- `problem.dualFeasibleSet = problem.dualDomain ∩ nonnegativeOrthant m`; multipliers outside
-- `problem.dualDomain` contribute the value `⊥`, so they do not change the supremum.
theorem dualOptimalValue_eq_sSup_image_nonnegativeOrthant
    (problem : LagrangianProblem Q m) :
    problem.dualOptimalValue = sSup (problem.dualFunction '' ℝ₊^m) := by
  -- Compare the owner's feasible-image supremum with the textbook orthant-image supremum.
  rw [LagrangianProblem.dualOptimalValue]
  apply le_antisymm
  · -- The owner's dual-feasible set is contained in the full nonnegative orthant.
    refine sSup_le_sSup ?_
    intro y hy
    rcases hy with ⟨l, hl, rfl⟩
    refine ⟨l, ?_, rfl⟩
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
      (problem.mem_dualFeasibleSet_iff.mp hl).2
  · -- The extra orthant multipliers contribute only `⊥`, which does not change the supremum.
    exact sSup_le_sSup_of_subset_insert_bot <|
      problem.dualFunction_image_nonnegativeOrthant_subset_insert_bot_dualFeasibleSet

end LagrangianProblem

/-! ### Proposition_3_44 (from Chap03) -/
noncomputable section

universe u

open MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "dim" => Module.finrank ℝ E
local notation "δ" => 1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))

/- Proposition 3.44 lies in the intrinsic finite-dimensional real normed-space
volume-ratio / interior-ball comparison domain.

Sampled owner-style declarations:
- `Set.SatisfiesInteriorBallCondition` in `Definition_3_59`, the chapter owner of the
  radius-`ρ` interior-ball hypothesis;
- `MeasureTheory.Measure.addHaar_real_closedBall` in mathlib, the canonical closed-ball
  Haar-measure scaling formula in finite-dimensional real normed spaces;
- `inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex` in `Theorem_3_51`, the
  chapter owner radius/volume comparison surface for an inner ball inside an outer ball;
- `localization_radius_le_outer_radius_mul_volume_ratio_rpow` in `Theorem_3_2_9`, the intrinsic
  localization-radius specialization of that owner surface to cutting-plane localization sets;
- the closed-ball-infimum best-value decay theorem in `Theorem_3_54`, a downstream user of the
  same closed-ball volume-ratio decay term stated relative to the direct ball infimum
  `sInf (f '' Metric.closedBall xStar R)`.

Best owner abstraction:
- source-facing: the bridge from an abstract geometric volume-decay hypothesis on `E_k` to the
  normalized `dim`-th-root volume-ratio and exponential bounds;
- core/canonical: the ambient Haar/Lebesgue closed-ball scaling owner together with the chapter's
  ball-radius/volume-ratio surface;
- bridge/view: the explicit decay inequality below.

Primitive data:
- the finite-dimensional real normed space `E`, the set `Q`, the interior-ball radius `ρ`, the
  center `x0`, the outer radius `R`, the stage index `k`, and the comparison set `Ek`;
- the source-facing owner hypothesis `Q.SatisfiesInteriorBallCondition ρ`;
- the positive dimension hypothesis `0 < Module.finrank ℝ E`;
- the natural outer-radius sign condition `0 ≤ R`, needed because
  `Metric.closedBall x0 R = ∅` for `R < 0`;
- the direct stagewise decay hypothesis on the Haar/Lebesgue measure `μ Ek`.

Derived API:
- the normalized `dim`-th-root volume ratio
  `Real.rpow (Measure.real μ Ek / Measure.real μ Q) (1 / (dim : ℝ))`;
- the closed-ball comparison factor
  `Real.rpow (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q) (1 / (dim : ℝ))`;
- the exponential upper bound `(R / ρ) * Real.exp (-k / (2 (dim + 1)^2))`.

Source/core/bridge triage:
- source-facing: Proposition 3.44's two quantitative inequalities;
- core/canonical: the standard closed-ball Haar/Lebesgue scaling formula and the chapter's
  radius/volume owner surface;
- bridge/view: passage from the raw volume-decay hypothesis to the displayed ratio and
  exponential bounds.

The earlier measurable-set and ambient-ball-subset hypotheses on `Q` and `E_k` were redundant for
this bridge theorem once the stagewise Haar-measure decay bound itself is taken as primitive
input, so the refined statement keeps only the data that actually changes the displayed
inequalities.
-/

/-- Proposition 3.44 at the intrinsic owner level: if `Q ⊆ E` satisfies the radius-`ρ`
interior-ball condition in a finite-dimensional real normed space `E`, if
`0 < Module.finrank ℝ E`, if `R ≥ 0`, and if a stage set `E_k` has Haar/Lebesgue measure bounded
by `δ^(k * Module.finrank ℝ E / 2) * vol(B₂(x0, R))`, then the normalized
`Module.finrank ℝ E`-th-root volume ratio of `E_k` satisfies the corresponding geometric-decay
estimate and the resulting exponential upper bound
`(R / ρ) * exp (-k / (2 (Module.finrank ℝ E + 1)^2))`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
-- Proof sketch: first convert the assumed finite `ENNReal` measure decay bound for `E_k` into the
-- corresponding real-volume inequality, then take the `dim`-th root to obtain the first
-- inequality. For the second inequality, extract a center `xBar` and a contained radius-`ρ`
-- ball from `Q.SatisfiesInteriorBallCondition ρ`, use monotonicity of volume to bound `vol(Q)`
-- below by the volume of that radius-`ρ` ball, rewrite the closed-ball volumes using the
-- standard finite-dimensional Haar/Lebesgue ball-scaling formula, and then bound
-- `(1 - u)^(k / 2)` by
-- `exp (-u k / 2)` with `u = 1 / (dim + 1)^2`.
theorem volume_ratio_rpow_decay_under_interior_ball_condition
    (hdim : 0 < dim) {μ : Measure E} [μ.IsAddHaarMeasure]
    {Q : Set E} {ρ : ℝ} (hQ : Q.SatisfiesInteriorBallCondition ρ)
    {x0 : E} {R : ℝ} (hR : 0 ≤ R) (k : ℕ) {Ek : Set E}
    (hvol_decay :
      μ Ek ≤
        ENNReal.ofReal (Real.rpow δ (((k * dim : ℕ) : ℝ) / 2)) *
          μ (Metric.closedBall x0 R)) :
    Real.rpow (μ.real Ek / μ.real Q) (1 / (dim : ℝ)) ≤
        Real.rpow δ ((k : ℝ) / 2) *
          Real.rpow
            (μ.real (Metric.closedBall x0 R) / μ.real Q)
            (1 / (dim : ℝ)) ∧
      Real.rpow δ ((k : ℝ) / 2) *
          Real.rpow
            (μ.real (Metric.closedBall x0 R) / μ.real Q)
            (1 / (dim : ℝ)) ≤
        (R / ρ) * Real.exp (-((k : ℝ) / (2 * (((dim : ℝ) + 1) ^ (2 : ℕ))))) := by
  rcases hQ with ⟨hρ, xBar, hball⟩
  set z : ℝ := 1 / (dim : ℝ)
  set a : ℝ := (((k * dim : ℕ) : ℝ) / 2)
  set ballR : Set E := Metric.closedBall x0 R
  have hdim_ne : (dim : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdim
  have hz_nonneg : 0 ≤ z := by
    positivity
  have hz_ne : z ≠ 0 := by
    dsimp [z]
    positivity
  have hs_ge_one : (1 : ℝ) ≤ (((dim : ℝ) + 1) ^ (2 : ℕ)) := by
    have hdim_nonneg : 0 ≤ (dim : ℝ) := by
      exact_mod_cast Nat.zero_le dim
    nlinarith
  have hfrac_le_one : 1 / (((dim : ℝ) + 1) ^ (2 : ℕ)) ≤ 1 := by
    simpa using (one_div_le_one_div_of_le zero_lt_one hs_ge_one)
  have hδ_nonneg : 0 ≤ δ := by
    linarith
  have hballR_lt_top : μ ballR < ⊤ := by
    simpa [ballR] using (measure_closedBall_lt_top : μ (Metric.closedBall x0 R) < ⊤)
  have hdecay_finite :
      ENNReal.ofReal (Real.rpow δ a) * μ ballR ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hballR_lt_top.ne
  have hEk_finite : μ Ek ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hvol_decay hdecay_finite.lt_top)
  have hvol_decay_real :
      μ.real Ek ≤ Real.rpow δ a * μ.real ballR := by
    have htoReal := ENNReal.toReal_mono hdecay_finite hvol_decay
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal] at htoReal
    · simpa [Measure.real] using htoReal
    · exact Real.rpow_nonneg hδ_nonneg a
  have hδ_le_exp :
      δ ≤ Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ)))) := by
    change 1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ)) ≤
      Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))))
    simpa using Real.one_sub_le_exp_neg (1 / (((dim : ℝ) + 1) ^ (2 : ℕ)))
  by_cases hQ_zero : μ.real Q = 0
  · constructor
    · have hzeroEk : Real.rpow (μ.real Ek / μ.real Q) z = 0 := by
        rw [hQ_zero, div_zero]
        exact Real.zero_rpow hz_ne
      have hzeroBall : Real.rpow (μ.real ballR / μ.real Q) z = 0 := by
        rw [hQ_zero, div_zero]
        exact Real.zero_rpow hz_ne
      rw [hzeroEk, hzeroBall, mul_zero]
    · have hzero : Real.rpow (μ.real ballR / μ.real Q) z = 0 := by
        rw [hQ_zero, div_zero]
        exact Real.zero_rpow hz_ne
      rw [hzero, mul_zero]
      positivity
  · have hQ_pos : 0 < μ.real Q := by
      exact lt_of_le_of_ne (by positivity) (by simpa [eq_comm] using hQ_zero)
    have hQ_finite : μ Q ≠ ⊤ := by
      have hQ_pos_toReal : 0 < (μ Q).toReal := by
        simpa [Measure.real] using hQ_pos
      rw [ENNReal.toReal_pos_iff] at hQ_pos_toReal
      exact hQ_pos_toReal.2.ne
    have hratio_le :
        μ.real Ek / μ.real Q ≤
          (Real.rpow δ a * μ.real ballR) / μ.real Q := by
      exact (div_le_div_iff_of_pos_right hQ_pos).2 hvol_decay_real
    have ha_mul : a * z = (k : ℝ) / 2 := by
      dsimp [a, z]
      rw [Nat.cast_mul]
      field_simp [hdim_ne]
    have hfirst :
        Real.rpow (μ.real Ek / μ.real Q) z ≤
          Real.rpow δ ((k : ℝ) / 2) * Real.rpow (μ.real ballR / μ.real Q) z := by
      have hmul_rpow :
          Real.rpow (Real.rpow δ a * (μ.real ballR / μ.real Q)) z =
            Real.rpow (Real.rpow δ a) z * Real.rpow (μ.real ballR / μ.real Q) z := by
        simpa using
          (Real.mul_rpow
            (Real.rpow_nonneg hδ_nonneg a)
            (by positivity : 0 ≤ μ.real ballR / μ.real Q))
      have hrpow_mul :
          Real.rpow (Real.rpow δ a) z = Real.rpow δ (a * z) := by
        simpa using (Real.rpow_mul hδ_nonneg a z).symm
      calc
        Real.rpow (μ.real Ek / μ.real Q) z ≤
            Real.rpow ((Real.rpow δ a * μ.real ballR) / μ.real Q) z := by
          exact Real.rpow_le_rpow (by positivity) hratio_le hz_nonneg
        _ = Real.rpow (Real.rpow δ a * (μ.real ballR / μ.real Q)) z := by
          rw [mul_div_assoc]
        _ = Real.rpow (Real.rpow δ a) z * Real.rpow (μ.real ballR / μ.real Q) z := hmul_rpow
        _ = Real.rpow δ (a * z) * Real.rpow (μ.real ballR / μ.real Q) z := by
          rw [hrpow_mul]
        _ = Real.rpow δ ((k : ℝ) / 2) * Real.rpow (μ.real ballR / μ.real Q) z := by
          rw [ha_mul]
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hdim
    have hunit_pos : 0 < μ.real (Metric.ball (0 : E) 1) := by
      have hball_pos : 0 < μ (Metric.ball (0 : E) 1) :=
        Metric.measure_ball_pos μ 0 zero_lt_one
      have hball_lt_top : μ (Metric.ball (0 : E) 1) < ⊤ := by
        simpa using (measure_ball_lt_top : μ (Metric.ball (0 : E) 1) < ⊤)
      simpa using ENNReal.toReal_pos hball_pos.ne' hball_lt_top.ne
    have hinner_pos : 0 < μ.real (Metric.ball xBar ρ) := by
      have hball_pos : 0 < μ (Metric.ball xBar ρ) :=
        Metric.measure_ball_pos μ xBar hρ
      have hball_lt_top : μ (Metric.ball xBar ρ) < ⊤ := by
        simpa using (measure_ball_lt_top : μ (Metric.ball xBar ρ) < ⊤)
      simpa using ENNReal.toReal_pos hball_pos.ne' hball_lt_top.ne
    have hQ_lower : μ.real (Metric.ball xBar ρ) ≤ μ.real Q :=
      measureReal_mono hball hQ_finite
    have hratio_ball_le :
        μ.real ballR / μ.real Q ≤
          μ.real ballR / μ.real (Metric.ball xBar ρ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left (inv_anti₀ hinner_pos hQ_lower) (by positivity)
    have hclosed_eq :
        μ.real ballR = R ^ dim * μ.real (Metric.ball (0 : E) 1) := by
      simpa [ballR] using Measure.addHaar_real_closedBall μ x0 hR
    have hinner_eq :
        μ.real (Metric.ball xBar ρ) = ρ ^ dim * μ.real (Metric.ball (0 : E) 1) := by
      rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball μ xBar ρ]
      rw [Measure.addHaar_real_closedBall μ xBar hρ.le]
    have hratio_pow_le :
        μ.real ballR / μ.real Q ≤ (R / ρ) ^ (dim : ℝ) := by
      calc
        μ.real ballR / μ.real Q ≤ μ.real ballR / μ.real (Metric.ball xBar ρ) := hratio_ball_le
        _ = (R / ρ) ^ (dim : ℝ) := by
          rw [hclosed_eq, hinner_eq, Real.rpow_natCast, div_pow]
          field_simp [hunit_pos.ne', pow_ne_zero dim hρ.ne']
    have hz_mul : (dim : ℝ) * z = 1 := by
      dsimp [z]
      field_simp [hdim_ne]
    have hratio_root_le :
        Real.rpow (μ.real ballR / μ.real Q) z ≤ R / ρ := by
      have hrpow_pow :
          Real.rpow ((R / ρ) ^ (dim : ℝ)) z = Real.rpow (R / ρ) ((dim : ℝ) * z) := by
        simpa using
          (Real.rpow_mul (by positivity : 0 ≤ R / ρ) (dim : ℝ) z).symm
      calc
        Real.rpow (μ.real ballR / μ.real Q) z ≤ Real.rpow ((R / ρ) ^ (dim : ℝ)) z := by
          exact Real.rpow_le_rpow (by positivity) hratio_pow_le hz_nonneg
        _ = R / ρ := by
          rw [hrpow_pow, hz_mul]
          exact Real.rpow_one (R / ρ)
    have hgeom_le_exp :
        Real.rpow δ ((k : ℝ) / 2) ≤
          Real.exp (-((k : ℝ) / (2 * (((dim : ℝ) + 1) ^ (2 : ℕ))))) := by
      have hexp_rpow :
          Real.rpow (Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))))) ((k : ℝ) / 2) =
            Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) * ((k : ℝ) / 2)) := by
        simpa using
          (Real.exp_mul (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ)))) ((k : ℝ) / 2)).symm
      calc
        Real.rpow δ ((k : ℝ) / 2) ≤
            Real.rpow (Real.exp (-(1 / (((dim : ℝ) + 1) ^ (2 : ℕ))))) ((k : ℝ) / 2) := by
          exact Real.rpow_le_rpow hδ_nonneg hδ_le_exp (by positivity)
        _ = Real.exp (-((k : ℝ) / (2 * (((dim : ℝ) + 1) ^ (2 : ℕ))))) := by
          rw [hexp_rpow]
          have hs_ne : (((dim : ℝ) + 1) ^ (2 : ℕ)) ≠ 0 := by
            positivity
          field_simp [hs_ne]
    refine ⟨hfirst, ?_⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul hratio_root_le hgeom_le_exp
        (Real.rpow_nonneg hδ_nonneg _)
        (by positivity : 0 ≤ R / ρ))

end

/-! ### Theorem_3_44 (from Chap03) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.44 lies in the chapter's constrained strong-convexity / relative-subdifferential
domain.

Sampled owner-style declarations:
- `constrainedSubdifferential` and `mem_constrainedSubdifferential_iff` in `Definition_3_1_5`
- mathlib `StrongConvexOn`
- the Chapter 3 owner recall `StrongConvexOn Q μ f` in `Definition_3_2_2`

Best owner abstraction:
- source-facing: the constrained-subdifferential notation `∂[Q] f(x)` for real-valued objectives
- core/canonical: `constrainedSubdifferential`
- bridge/view: the codomain-coercion view `subdifferentialWithin Q f x`

Primitive data:
- the constrained `WithTop`-valued subdifferential owner
- a real-valued objective `f`

Derived API:
- `subdifferentialWithin`
- `mem_subdifferentialWithin_iff`
- `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin`

Source/core/bridge triage:
- source-facing: Theorem 3.44's quadratic affine lower bound for real-valued strongly convex
  functions, written on `g ∈ ∂[Q] f(x)`
- core/canonical: `constrainedSubdifferential` and `StrongConvexOn`
- bridge/view: `subdifferentialWithin`, the real-valued view of the constrained owner

This file therefore keeps the source-facing notation `∂[Q] f(x)` on its main theorem surfaces and
uses `subdifferentialWithin` only as the thin real-valued bridge/view, instead of duplicating a
second primitive subgradient predicate. The bridge/view itself only needs the same seminormed
inner-product ambient layer as `Definition_3_1_5`; the stronger normed ambient structure is
required only for the quadratic strong-convexity lower bound. -/

section Bridge

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Bridge/view: the relative subdifferential of a real-valued function is the constrained
`WithTop`-valued subdifferential of its canonical coercion. Public theorem surfaces in this file
prefer the source-facing notation `∂[Q] f(x)`. -/
abbrev subdifferentialWithin (Q : Set E) (f : E → ℝ) (x : E) : Set E :=
  ∂[Q] (fun y ↦ (f y : WithTop ℝ))(x)

/- Real-valued surface notation for the constrained subdifferential, reusing the same textbook
spelling `∂[Q] f(x)` as the upstream `WithTop` owner. -/
scoped[WithTopConvexAnalysis] notation:max "∂[" Q "] " f:arg "(" x:arg ")" =>
  subdifferentialWithin Q f x

/-- For real-valued objectives, membership in the constrained-subdifferential notation `∂[Q] f(x)`
is exactly the affine lower-support condition on `Q`. -/
@[simp]
theorem mem_subdifferentialWithin_iff
    {Q : Set E} {f : E → ℝ} {x g : E} :
    g ∈ ∂[Q] f(x) ↔
      x ∈ Q ∧ ∀ ⦃y : E⦄, y ∈ Q → f y ≥ f x + inner ℝ g (y - x) := by
  constructor
  · intro hg
    change g ∈ ∂[Q] (fun y ↦ (f y : WithTop ℝ))(x) at hg
    rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨hxQ, -, hminorant⟩
    refine ⟨hxQ, ?_⟩
    intro y hy
    exact_mod_cast hminorant hy
  · rintro ⟨hxQ, hminorant⟩
    change g ∈ ∂[Q] (fun y ↦ (f y : WithTop ℝ))(x)
    refine (mem_constrainedSubdifferential_iff).2 ?_
    refine ⟨hxQ, by
      change (f x : WithTop ℝ) < ⊤
      simp, ?_⟩
    intro y hy
    exact_mod_cast hminorant hy

end Bridge

section StrongConvex

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace StrongConvexOn

/-- Theorem 3.44: if `f` is `μ`-strongly convex on `Q`, then every feasible subgradient
`g ∈ ∂[Q] f(x)` gives the quadratic affine lower bound
`f y ≥ f x + ⟪g, y - x⟫ + (μ / 2) * ‖y - x‖^2` for every `y ∈ Q`. -/
-- Proof sketch: tilt `f` by the affine functional `z ↦ -⟪g, z⟫`. The subgradient hypothesis says
-- that `x` minimizes this tilted objective on `Q`, while strong convexity is preserved under
-- affine perturbations. The canonical owner theorem
-- `quadratic_growth_of_isMinOn_of_mem` applied to that tilted objective then yields the stated
-- lower bound after rearranging the affine term.
theorem lower_bound_of_mem_subdifferentialWithin
    {Q : Set E} {μ : ℝ} {f : E → ℝ} {x y g : E}
    (hf : StrongConvexOn Q μ f)
    (hg : g ∈ ∂[Q] f(x)) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ g (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  rw [mem_subdifferentialWithin_iff] at hg
  rcases hg with ⟨hx, hsubgrad⟩
  let k : E → ℝ := fun z ↦ -inner ℝ g z + f z
  have hlinear : ConvexOn ℝ Q (fun z ↦ -inner ℝ g z) := by
    let ℓ : E →ᵃ[ℝ] ℝ :=
      AffineMap.const ℝ E 0 + ((innerSL ℝ (-g)).toLinearMap).toAffineMap
    have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
      simpa [Function.comp, ℓ] using (convexOn_id convex_univ).comp_affineMap ℓ
    refine ⟨hf.1, ?_⟩
    intro z hz w hw a b ha hb hab
    simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using
      hℓ.2 (by simp) (by simp) ha hb hab
  have hk : StrongConvexOn Q μ k := by
    simpa [k, add_comm] using hf.add_convexOn hlinear
  have hxmin : IsMinOn k Q x := by
    intro z hz
    have hzsub := hsubgrad hz
    have hzsub' := hzsub
    rw [inner_sub_right] at hzsub'
    change -inner ℝ g x + f x ≤ -inner ℝ g z + f z
    linarith
  have hkbound :
      k y ≥ k x + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) :=
    hk.quadratic_growth_of_isMinOn_of_mem hx hxmin y hy
  have hkbound' : -inner ℝ g y + f y ≥ -inner ℝ g x + f x + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    simpa [k] using hkbound
  have hinner : inner ℝ g (y - x) = inner ℝ g y - inner ℝ g x := by
    rw [inner_sub_right]
  linarith

end StrongConvexOn

end StrongConvex

end
