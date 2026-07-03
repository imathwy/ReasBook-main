import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_13_11 (from Chap13) -/
noncomputable section

open InnerProductSpace (toDualMap)
open Matrix
open Metric
open scoped Gradient RealInnerProductSpace

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "B" => closedBall (0 : E) 1
variable (A : Matrix (Fin n) (Fin n) ℝ)
local notation "qA" => quadratic_affine_function_on_lp (2 : ENNReal) (-A) 0 0

private theorem qA_apply (x : E) :
    qA x = -((1 / 2 : ℝ) * ⟪A.toEuclideanLin x, x⟫) := by
  simpa using quadratic_affine_function_on_lp_two_apply_eq (-A) (0 : E) x

/- This item is `source-facing`: it specializes the Chapter 13 generalized conditional-gradient
trajectory to the quadratic maximization problem on the Euclidean unit ball.

Domain sampling in the Euclidean quadratic / conditional-gradient domain gives the owner layers:

- `is_generalized_conditional_gradient_trajectory` for the iterate/search-point/stepsize data;
- `uses_generalized_conditional_gradient_exact_line_search_rule` for the exact line-search
  condition on the composite objective;
- `is_stationary_point_on` for the Chapter 3 constrained stationarity predicate on the ball;
- `Matrix.toEuclideanLin` for the canonical action of a real matrix on `ℝ^n`;
- the Chapter 5/6 quadratic owner `qA = quadratic_affine_function_on_lp (2 : ENNReal) (-A) 0 0`;
- the bridge theorem `quadratic_affine_function_on_lp_two_apply_eq`, which rewrites that owner to
  the intrinsic Euclidean quadratic `x ↦ -((1 / 2 : ℝ) * ⟪A.toEuclideanLin x, x⟫)`.

Primitive data here are just the matrix `A`, the trajectory data `(xᵏ, pᵏ, tₖ)`, and the closed
ball constraint. The canonical quadratic owner therefore belongs in the theorem statement, while
the intrinsic Euclidean formula is recovered by `qA_apply` as a thin local bridge for later proof
rewrites. -/

/-- Helper for Example 13.11: the closed-unit-ball indicator is a convex extended-real-valued
function. -/
lemma unit_ball_extendedIndicator_is_convex_function :
    is_convex_function (extendedIndicator B) := by
  -- Prove the Jensen inequality directly on the feasible unit ball.
  rw [is_convex_function_iff_segment_ineq]
  intro x hx y hy t ht
  have hxB : x ∈ B := by
    simpa [effective_domain_extendedIndicator] using hx
  have hyB : y ∈ B := by
    simpa [effective_domain_extendedIndicator] using hy
  have hcombo : t • x + (1 - t) • y ∈ B := by
    exact (convex_closedBall (0 : E) 1) hxB hyB ht.1 (sub_nonneg.2 ht.2) (by ring)
  simp [extendedIndicator, hxB, hyB, hcombo]

/-- Helper for Example 13.11: the quadratic owner `qA` has gradient `x ↦ -A x`. -/
lemma qA_hasGradientAt
    (hA : A.PosSemidef) (x : E) :
    HasGradientAt qA (-A.toEuclideanLin x) x := by
  let T : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hsymm : (T : E →ₗ[ℝ] E).IsSymmetric :=
    by
      change A.toEuclideanLin.IsSymmetric
      exact (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.1
  -- Route correction: differentiate the symmetric Rayleigh form directly, then scale by `-1/2`
  -- to match the source objective `qA`.
  have hinner :
      HasFDerivAt (fun y : E => ⟪T y, y⟫) (2 • innerSL ℝ (T x)) x := by
    simpa [hsymm.coe_reApplyInnerSelf_apply] using
      (hsymm.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt
  have hscaled :
      HasFDerivAt (fun y : E => -((1 / 2 : ℝ) * ⟪T y, y⟫))
        ((-(1 / 2 : ℝ)) • (2 • innerSL ℝ (T x))) x := by
    simpa using hinner.const_mul (-(1 / 2 : ℝ))
  have hfrechet :
      ((-(1 / 2 : ℝ)) • (2 • innerSL ℝ (T x))) =
        (InnerProductSpace.toDual ℝ E) (-T x) := by
    ext y
    simp [real_inner_comm]
  rw [hfrechet] at hscaled
  -- Rewrite the Chapter 5 quadratic owner back to the intrinsic Euclidean formula.
  have hquad :
      HasGradientAt (fun y : E ↦ -((1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫))
        (-A.toEuclideanLin x) x := by
    simpa [T] using hscaled.hasGradientAt
  convert hquad using 1
  funext y
  rw [qA_apply]

/-- Helper for Example 13.11: if `x` is feasible but not stationary on the unit ball, then
`A x ≠ 0`. -/
lemma matrix_image_ne_zero_of_not_stationary_on_ball
    (hA : A.PosSemidef) {x : E} (hx : x ∈ B)
    (hns : ¬ is_stationary_point_on qA B x) :
    A.toEuclideanLin x ≠ 0 := by
  intro hzero
  apply hns
  -- A zero matrix image gives zero gradient, so the variational inequality is trivially true.
  rw [is_stationary_point_on_iff_forall_inner_nonneg]
  refine ⟨(qA_hasGradientAt (A := A) hA x).differentiableAt, hx, ?_⟩
  intro y hy
  rw [(qA_hasGradientAt (A := A) hA x).gradient, hzero]
  simp

/-- Helper for Example 13.11: on the Euclidean unit ball, minimizing the Chapter 13 linearized
subproblem for `qA` is equivalent to maximizing the Chapter 10 functional `q ↦ ⟪A x, q⟫`. -/
lemma mem_qA_unit_ball_argmin_iff_mem_primalCounterparts
    (hA : A.PosSemidef) {x p : E} :
    p ∈ generalized_conditional_gradient_argmin qA (extendedIndicator B) x ↔
      p ∈ Λ[toDualMap ℝ E (A.toEuclideanLin x)] := by
  have hB_nonempty : Set.Nonempty B := by
    refine ⟨0, ?_⟩
    simp
  have hargmin :
      p ∈ generalized_conditional_gradient_argmin qA (extendedIndicator B) x ↔
        p ∈ B ∧ IsMinOn (fun q ↦ inner ℝ q (∇ qA x)) B p := by
    -- Rewrite the Chapter 13 argmin owner into feasibility plus minimization of the linearized
    -- objective on the unit ball.
    have hqA_toReal : (fun z : E ↦ (Function.toEReal qA z).toReal) = qA := by
      funext z
      exact EReal.toReal_coe _
    have hbridge :=
      mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
        (f := Function.toEReal qA) (C := B) (xk := x) (p := p) hB_nonempty
    rw [hqA_toReal] at hbridge
    exact hbridge
  calc
    p ∈ generalized_conditional_gradient_argmin qA (extendedIndicator B) x ↔
        p ∈ B ∧ IsMinOn (fun q ↦ inner ℝ q (∇ qA x)) B p := hargmin
    _ ↔ p ∈ B ∧ IsMinOn (fun q ↦ inner ℝ q (-A.toEuclideanLin x)) B p := by
      rw [(qA_hasGradientAt (A := A) hA x).gradient]
    _ ↔ p ∈ Λ[toDualMap ℝ E (A.toEuclideanLin x)] := by
      rw [mem_Λ_iff]
      constructor
      · rintro ⟨hpB, hpmin⟩
        refine ⟨hpB, ?_⟩
        -- Minimizing `q ↦ ⟪q, -A x⟫` is equivalent to maximizing `q ↦ ⟪A x, q⟫`.
        rw [isMinOn_iff] at hpmin
        rw [isMaxOn_iff]
        intro q hq
        have hq_le : inner ℝ p (-A.toEuclideanLin x) ≤ inner ℝ q (-A.toEuclideanLin x) :=
          hpmin q hq
        have hneg_le :
            -inner ℝ q (-A.toEuclideanLin x) ≤ -inner ℝ p (-A.toEuclideanLin x) :=
          neg_le_neg hq_le
        simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hneg_le
      · rintro ⟨hpB, hpmax⟩
        refine ⟨hpB, ?_⟩
        -- Conversely, maximizing the Chapter 10 functional is minimizing the negated linearized
        -- objective from the conditional-gradient subproblem.
        rw [isMaxOn_iff] at hpmax
        rw [isMinOn_iff]
        intro q hq
        have hq_le :
            (toDualMap ℝ E (A.toEuclideanLin x)) q ≤
              (toDualMap ℝ E (A.toEuclideanLin x)) p :=
          hpmax q hq
        have hneg_le :
            -((toDualMap ℝ E (A.toEuclideanLin x)) p) ≤
              -((toDualMap ℝ E (A.toEuclideanLin x)) q) :=
          neg_le_neg hq_le
        simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hneg_le

/-- Helper for Example 13.11: the Chapter 13 linear minimization oracle on the unit ball is the
normalized matrix image. -/
lemma argmin_eq_normalized_matrix_image
    (hA : A.PosSemidef) {x p : E} (hx : x ∈ B)
    (hp : p ∈ generalized_conditional_gradient_argmin qA (extendedIndicator B) x)
    (hns : ¬ is_stationary_point_on qA B x) :
    p = ‖A.toEuclideanLin x‖⁻¹ • A.toEuclideanLin x := by
  have hAx_ne :
      A.toEuclideanLin x ≠ 0 :=
    matrix_image_ne_zero_of_not_stationary_on_ball (A := A) hA hx hns
  -- The local oracle bridge reduces the Chapter 13 argmin point to the singleton from
  -- Proposition 10.59.
  have hp_counterpart : p ∈ Λ[toDualMap ℝ E (A.toEuclideanLin x)] := by
    exact (mem_qA_unit_ball_argmin_iff_mem_primalCounterparts (A := A) hA).mp hp
  have hp_singleton :
      p ∈ ({‖A.toEuclideanLin x‖⁻¹ • A.toEuclideanLin x} : Set E) := by
    rwa [primalCounterparts_toDualMap_eq_singleton_normalized
      (a := A.toEuclideanLin x) hAx_ne] at hp_counterpart
  simpa [Set.mem_singleton_iff] using hp_singleton

/-- Helper for Example 13.11: along any segment starting at `x`, the quadratic objective expands
into its initial value plus a linear term and a nonpositive curvature correction. -/
lemma quadratic_segment_eq_initial_add_linear_curvature
    (hA : A.PosSemidef) (x p : E) (s : ℝ) :
    qA (x + s • (p - x)) =
      qA x + s * ⟪∇ qA x, p - x⟫ -
        (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
  let d : E := p - x
  let T : E →ₗ[ℝ] E := A.toEuclideanLin
  have hsymm : (T : E →ₗ[ℝ] E).IsSymmetric :=
    by
      change A.toEuclideanLin.IsSymmetric
      exact (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.1
  have hcross : ⟪T d, x⟫ = ⟪T x, d⟫ := by
    -- Symmetry turns the two mixed terms in the quadratic expansion into the same scalar.
    calc
      ⟪T d, x⟫ = ⟪d, T x⟫ := hsymm d x
      _ = ⟪T x, d⟫ := by simp [real_inner_comm]
  have hgrad : ∇ qA x = -T x := by
    rw [(qA_hasGradientAt (A := A) hA x).gradient]
  have hraw :
      qA (x + s • d) =
        qA x - s * ⟪T x, d⟫ - (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪T d, d⟫ := by
    -- Expand the quadratic along the segment and combine the mixed terms using `hcross`.
    rw [qA_apply, qA_apply, LinearMap.map_add, LinearMap.map_smul, inner_add_left,
      inner_add_right, inner_add_right, inner_smul_left, inner_smul_right, hcross]
    rw [inner_smul_left, inner_smul_right]
    simp [T]
    ring_nf
  -- Replace the explicit linear term by the gradient from `qA_hasGradientAt`.
  calc
    qA (x + s • (p - x)) =
        qA x - s * ⟪T x, d⟫ - (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪T d, d⟫ := by
      simpa [d] using hraw
    _ = qA x + s * ⟪∇ qA x, p - x⟫ -
          (1 / 2 : ℝ) * s ^ (2 : ℕ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
      rw [hgrad]
      simp [d, T, inner_neg_left, sub_eq_add_neg]

/-- Helper for Example 13.11: on `[0,1]`, the secant-gap curvature term from the quadratic
segment expansion is nonnegative. -/
lemma secant_gap_nonneg_of_posSemidef
    (hA : A.PosSemidef) (x p : E) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (1 / 2 : ℝ) * s * (1 - s) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
  have hs_nonneg : 0 ≤ s * (1 - s) := by
    -- The scalar secant factor is nonnegative exactly on the unit interval.
    nlinarith [hs.1, hs.2]
  have hcurv : 0 ≤ ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    -- Positive semidefiniteness controls the segment curvature in every direction.
    have hpositive : (A.toEuclideanLin).IsPositive :=
      (Matrix.isPositive_toEuclideanLin_iff).2 hA
    simpa [real_inner_comm] using hpositive.inner_nonneg_right (p - x)
  nlinarith

/-- Helper for Example 13.11: the quadratic restriction to a unit-ball oracle segment lies above
the secant through its endpoints. -/
lemma quadratic_segment_ge_endpoint_combo
    (hA : A.PosSemidef) (x p : E) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - s) * qA x + s * qA p ≤ qA (x + s • (p - x)) := by
  have hseg :=
    quadratic_segment_eq_initial_add_linear_curvature (A := A) hA x p s
  have hp_endpoint : x + (1 : ℝ) • (p - x) = p := by
    simp
  have hend :
      qA p =
        qA x + ⟪∇ qA x, p - x⟫ -
          (1 / 2 : ℝ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    -- Evaluate the segment expansion at the endpoint `s = 1`.
    simpa [hp_endpoint] using
      (quadratic_segment_eq_initial_add_linear_curvature (A := A) hA x p (1 : ℝ))
  have hgap :
      0 ≤ (1 / 2 : ℝ) * s * (1 - s) * ⟪A.toEuclideanLin (p - x), p - x⟫ :=
    secant_gap_nonneg_of_posSemidef (A := A) hA x p hs
  have hrewrite :
      qA (x + s • (p - x)) - ((1 - s) * qA x + s * qA p) =
        (1 / 2 : ℝ) * s * (1 - s) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    let c : ℝ := ⟪A.toEuclideanLin (p - x), p - x⟫
    rw [hseg, hend]
    simp
    ring
  have hnonneg :
      0 ≤ qA (x + s • (p - x)) - ((1 - s) * qA x + s * qA p) := by
    rw [hrewrite]
    exact hgap
  -- Compare the value at `s` with the secant interpolation of the endpoint formulas.
  exact sub_nonneg.mp hnonneg

/-- Helper for Example 13.11: if the oracle direction has strictly negative linearized slope,
then the endpoint `p` strictly improves the quadratic objective over `x`. -/
lemma quadratic_endpoint_lt_initial_of_inner_lt_zero
    (hA : A.PosSemidef) {x p : E}
    (hinner_lt : ⟪∇ qA x, p - x⟫ < 0) :
    qA p < qA x := by
  let d : E := p - x
  have hcurv : 0 ≤ ⟪A.toEuclideanLin d, d⟫ := by
    -- Positive semidefiniteness controls the curvature correction at the endpoint.
    have hpositive : (A.toEuclideanLin).IsPositive :=
      (Matrix.isPositive_toEuclideanLin_iff).2 hA
    simpa [d, real_inner_comm] using hpositive.inner_nonneg_right d
  have hend :
      qA p =
        qA x + ⟪∇ qA x, p - x⟫ -
          (1 / 2 : ℝ) * ⟪A.toEuclideanLin (p - x), p - x⟫ := by
    -- The endpoint `p` is the segment value at `s = 1`.
    have hp_endpoint : x + (1 : ℝ) • (p - x) = p := by
      simp
    simpa [hp_endpoint] using
      (quadratic_segment_eq_initial_add_linear_curvature (A := A) hA x p (1 : ℝ))
  -- The strictly negative linear term dominates because the curvature correction is nonpositive.
  linarith [hend, hinner_lt, hcurv]

/-- Helper for Example 13.11: a minimizer on `[0,1]` whose value is bounded below by the secant
through the endpoints must equal the right endpoint when that endpoint is strictly lower than the
left endpoint. -/
lemma eq_right_endpoint_of_min_le_right_of_secant
    {φ : ℝ → ℝ} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hmin_right : φ τ ≤ φ 1)
    (hsecant : (1 - τ) * φ 0 + τ * φ 1 ≤ φ τ)
    (hend : φ 1 < φ 0) :
    τ = 1 := by
  -- The secant lower bound is strict unless `τ = 1`, so a minimizer no larger than `φ 1` must
  -- sit at the right endpoint.
  by_contra hne
  have hlt : τ < 1 := lt_of_le_of_ne hτ.2 hne
  have hstrict :
      φ 1 < (1 - τ) * φ 0 + τ * φ 1 := by
    nlinarith
  linarith

/-- Helper for Example 13.11: exact line search on a feasible unit-ball segment compares the
quadratic value at the chosen stepsize with the right endpoint in real form. -/
lemma exact_line_search_real_compare_endpoint_on_feasible_segment
    {x p : E} {τ : ℝ}
    (hx : x ∈ B) (hp : p ∈ B)
    (ht : τ ∈ conditional_gradient_exact_line_search_stepsizes
      (composite_model_objective (Function.toEReal qA) (extendedIndicator B)) x p) :
    qA (x + τ • (p - x)) ≤ qA p := by
  have hg_ne_bot : ∀ y : E, extendedIndicator B y ≠ ⊥ := by
    intro y
    by_cases hy : y ∈ B
    · simp [extendedIndicator, hy]
    · simp [extendedIndicator, hy]
  have hx_dom : x ∈ effective_domain (extendedIndicator B) := by
    simpa [effective_domain_extendedIndicator] using hx
  have hp_dom : p ∈ effective_domain (extendedIndicator B) := by
    simpa [effective_domain_extendedIndicator] using hp
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 :=
    (mem_conditional_gradient_exact_line_search_stepsizes_iff.mp ht).1
  have htrial_dom :
      x + τ • (p - x) ∈ effective_domain (extendedIndicator B) :=
    conditional_gradient_trial_mem_effective_domain_of_mem_Icc
      (g := extendedIndicator B)
      unit_ball_extendedIndicator_is_convex_function hx_dom hp_dom hτ
  have htrial : x + τ • (p - x) ∈ B := by
    simpa [effective_domain_extendedIndicator] using htrial_dom
  have hcompare :
      composite_model_objective (Function.toEReal qA) (extendedIndicator B)
          (x + τ • (p - x)) ≤
        composite_model_objective (Function.toEReal qA) (extendedIndicator B) p := by
    -- Route correction: normalize the exact-line-search owner before stripping the indicator and
    -- `EReal` coercions, so the later rewrites only touch feasible points.
    rw [mem_conditional_gradient_exact_line_search_stepsizes_iff, isMinOn_iff] at ht
    rcases ht with ⟨_, hmin⟩
    simpa using hmin 1 (by constructor <;> norm_num)
  have hcompare_coe :
      (((qA (x + τ • (p - x)) : ℝ) : EReal)) ≤ (((qA p : ℝ) : EReal)) := by
    -- Feasibility turns the composite objective back into the real quadratic owner.
    rw [composite_model_objective_eq_coe_real_of_mem_effective_domain
          (f := qA) (g := extendedIndicator B) hg_ne_bot htrial_dom,
        composite_model_objective_eq_coe_real_of_mem_effective_domain
          (f := qA) (g := extendedIndicator B) hg_ne_bot hp_dom] at hcompare
    simpa [extendedIndicator, htrial, hp] using hcompare
  exact EReal.coe_le_coe_iff.mp hcompare_coe

/-- Helper for Example 13.11: a strict endpoint improvement forces the exact line search stepsize
to be the right endpoint of the unit interval. -/
lemma exact_line_search_stepsize_eq_one_of_endpoint_improvement
    (hA : A.PosSemidef) {x p : E} {τ : ℝ}
    (hx : x ∈ B) (hp : p ∈ B)
    (ht : τ ∈ conditional_gradient_exact_line_search_stepsizes
      (composite_model_objective (Function.toEReal qA) (extendedIndicator B)) x p)
    (hend : qA p < qA x) :
    τ = 1 := by
  let φ : ℝ → ℝ := fun s ↦ qA (x + s • (p - x))
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 :=
    (mem_conditional_gradient_exact_line_search_stepsizes_iff.mp ht).1
  have hmin_right : φ τ ≤ φ 1 := by
    -- The previous helper removes the indicator layer and compares the chosen step to the
    -- endpoint `s = 1`.
    simpa [φ] using
      exact_line_search_real_compare_endpoint_on_feasible_segment
        (A := A) (x := x) (p := p) (τ := τ) hx hp ht
  have hsecant : (1 - τ) * φ 0 + τ * φ 1 ≤ φ τ := by
    -- Positive semidefiniteness makes the quadratic restriction lie above its endpoint secant.
    simpa [φ] using quadratic_segment_ge_endpoint_combo (A := A) hA x p hτ
  have hendφ : φ 1 < φ 0 := by
    simpa [φ] using hend
  exact eq_right_endpoint_of_min_le_right_of_secant hτ hmin_right hsecant hendφ

-- Proof sketch: use the generalized conditional-gradient update rule
-- `x^(k+1) = x^k + t_k (p^k - x^k)` from Algorithm 13.2 together with the exact line-search
-- condition on the quadratic-on-ball composite objective. For a positive-semidefinite matrix, the
-- one-dimensional restriction is concave, so its minimum on `[0, 1]` is attained at an endpoint.
-- Nonstationarity on the ball rules out `t_k = 0`, forcing `t_k = 1`; the linear minimization
-- oracle on the Euclidean unit ball then gives
-- `p^k = ‖A x^k‖⁻¹ • A x^k`, and substituting into the update yields the power-method step.
/-- Example 13.11: for the quadratic maximization problem on the Euclidean unit ball with
`A ∈ 𝕊_+^n`, if `(xᵏ, pᵏ, tₖ)` is a generalized conditional-gradient trajectory for the quadratic
term `x ↦ -(1 / 2) ⟪x, A x⟫` and the closed-ball indicator, if each `tₖ` is chosen by exact line
search, and if `xᵏ` is not a constrained stationary point on the unit ball, then the next iterate
is exactly the normalized matrix image
`xᵏ⁺¹ = (1 / ‖A xᵏ‖) • A xᵏ`, i.e. the standard power-method update. -/
theorem generalized_conditional_gradient_step_eq_power_method_of_not_stationary
    (hA : A.PosSemidef)
    {x p : ℕ → E} {t : ℕ → Set.Icc (0 : ℝ) 1}
    (htraj :
      is_generalized_conditional_gradient_trajectory
        qA (extendedIndicator B) x p t)
    (hline :
      uses_generalized_conditional_gradient_exact_line_search_rule
        qA (extendedIndicator B) x p t)
    (k : ℕ)
    (hk : ¬ is_stationary_point_on qA B (x k)) :
    x (k + 1) = ‖A.toEuclideanLin (x k)‖⁻¹ • A.toEuclideanLin (x k) := by
  have hqA_ne_bot : ∀ y : E, extendedIndicator B y ≠ ⊥ := by
    intro y
    by_cases hy : y ∈ B
    · simp [extendedIndicator, hy]
    · simp [extendedIndicator, hy]
  have hxk_dom :
      x k ∈ effective_domain (extendedIndicator B) :=
    generalized_conditional_gradient_trajectory_mem_effective_domain
      (f := qA) (g := extendedIndicator B) hqA_ne_bot
      unit_ball_extendedIndicator_is_convex_function htraj k
  have hxk : x k ∈ B := by
    simpa [effective_domain_extendedIndicator] using hxk_dom
  have hpk_argmin :
      p k ∈ generalized_conditional_gradient_argmin qA (extendedIndicator B) (x k) :=
    htraj.argmin_mem k
  have hpk_dom :
      p k ∈ effective_domain (extendedIndicator B) :=
    generalized_conditional_gradient_argmin_mem_effective_domain
      (f := qA) (g := extendedIndicator B) hxk_dom hpk_argmin
  have hpk : p k ∈ B := by
    simpa [effective_domain_extendedIndicator] using hpk_dom
  have hpk_eq :
      p k = ‖A.toEuclideanLin (x k)‖⁻¹ • A.toEuclideanLin (x k) :=
    argmin_eq_normalized_matrix_image (A := A) hA hxk hpk_argmin hk
  have hneg_dir :
      ∃ y ∈ B, ⟪∇ qA (x k), y - x k⟫ < (0 : ℝ) := by
    -- Route correction: use the source variational inequality directly to witness a strictly
    -- descending feasible direction when `x k` is not stationary.
    by_contra hcontra
    apply hk
    rw [is_stationary_point_on_iff_forall_inner_nonneg]
    refine ⟨(qA_hasGradientAt (A := A) hA (x k)).differentiableAt, hxk, ?_⟩
    intro y hy
    by_contra hyneg
    exact hcontra ⟨y, hy, lt_of_not_ge hyneg⟩
  have hinner_lt : ⟪∇ qA (x k), p k - x k⟫ < (0 : ℝ) := by
    rcases hneg_dir with ⟨y, hyB, hyneg⟩
    have hpmin :
        IsMinOn (fun q ↦ inner ℝ q (∇ qA (x k))) B (p k) := by
      have hqA_toReal : (fun z : E ↦ (Function.toEReal qA z).toReal) = qA := by
        funext z
        exact EReal.toReal_coe _
      rcases
        (mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
          (f := Function.toEReal qA) (C := B) (xk := x k)
          (p := p k) ⟨0, by simp⟩).mp hpk_argmin with
        ⟨_, hpmin⟩
      rw [hqA_toReal] at hpmin
      exact hpmin
    rw [isMinOn_iff] at hpmin
    have hpy : inner ℝ (p k) (∇ qA (x k)) ≤ inner ℝ y (∇ qA (x k)) :=
      hpmin y hyB
    have hyshift :
        inner ℝ y (∇ qA (x k)) - inner ℝ (x k) (∇ qA (x k)) < (0 : ℝ) := by
      simpa [real_inner_comm, inner_sub_right] using hyneg
    have hpshift :
        inner ℝ (p k) (∇ qA (x k)) - inner ℝ (x k) (∇ qA (x k)) < (0 : ℝ) := by
      linarith [hpy, hyshift]
    simpa [real_inner_comm, inner_sub_right] using hpshift
  have hendpoint_lt : qA (p k) < qA (x k) :=
    quadratic_endpoint_lt_initial_of_inner_lt_zero (A := A) hA hinner_lt
  have ht_eq_one : (t k : ℝ) = 1 :=
    exact_line_search_stepsize_eq_one_of_endpoint_improvement
      (A := A) hA hxk hpk (hline k) hendpoint_lt
  have hstep_to_oracle : x (k + 1) = p k := by
    -- Once exact line search picks `tₖ = 1`, the affine trajectory update lands at the oracle
    -- point `pᵏ`.
    simpa [ht_eq_one] using htraj.step_eq k
  -- Substitute the unit stepsize update and the closed-form oracle point to recover the power
  -- method exactly.
  calc
    x (k + 1) = p k := hstep_to_oracle
    _ = ‖A.toEuclideanLin (x k)‖⁻¹ • A.toEuclideanLin (x k) := hpk_eq

end
