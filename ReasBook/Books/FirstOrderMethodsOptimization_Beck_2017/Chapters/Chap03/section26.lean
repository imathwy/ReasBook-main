import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_26 (from Chap03) -/
open Matrix
open WithLp (toLp ofLp)

section

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.26 is a `bridge/view` item in the chapter's coordinate `ℓ∞` subdifferential
API. The owner abstractions already live upstream: Theorem 3.19 gives the affine-map pullback
rule on `subdifferential`, and Proposition 3.24 gives the vector-side owner formula through
`euclideanSubdifferentialAt` for the residual `ℓ∞` norm on `Fin m → ℝ`. The only primitive data
here are the affine matrix map `A.mulVecLin` and the offset `b`; the transpose-image formula is
derived from those owners. -/

recall subdifferential_precompose_affineMap_eq
recall euclidean_subdifferentialAt_linf_eq_piecewise

-- Proof sketch: apply the affine chain rule to the `ℓ∞` norm, then reuse the source-facing
-- residual formula from Proposition 3.24. The owner-level affine pullback step is the transpose
-- image description below; Proposition 3.26 is its source-facing zero/nonzero case split.
private theorem euclidean_subdifferentialAt_affine_linf_eq_transpose_image
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : En) :
    euclideanSubdifferentialAt (fun y : En ↦ ‖A.mulVecLin (ofLp y) + b‖) x =
      A.transpose.toEuclideanLin ''
        euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) (toLp 2 (A.mulVecLin (ofLp x) + b)) :=
  sorry

-- Proof sketch: first rewrite the affine `ℓ∞` subdifferential using the owner-level transpose
-- coordinate description from Proposition 3.24. When the residual `A.mulVecLin x + b` vanishes,
-- the `ℓ∞` subdifferential is the canonical `WithLp 1` unit ball `{z | ‖toLp 1 z‖ ≤ 1}`, whose
-- pullback along `A` is the transpose image `Aᵀ.mulVecLin '' {z | ‖toLp 1 z‖ ≤ 1}`. Otherwise,
-- the active signed-coordinate image from Proposition 3.24 pulls back along `A` to the transpose
-- image of those active combinations.
/-- Proposition 3.26: for the affine `ℓ∞` objective `x ↦ ‖A x + b‖∞`, the Euclidean/vector-side
subdifferential is the transpose image of the `ℓ₁` unit ball `{z | ‖toLp 1 z‖ ≤ 1}` when
`A x + b = 0`, and otherwise it is the transpose image of the active signed-coordinate image from
Proposition 3.24, evaluated at the residual `A x + b`. -/
theorem euclidean_subdifferentialAt_affine_linf_eq_piecewise
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : En) :
    euclideanSubdifferentialAt (fun y : En ↦ ‖A.mulVecLin (ofLp y) + b‖) x =
      if A.mulVecLin (ofLp x) + b = 0 then
        A.transpose.toEuclideanLin '' {z : Em | ‖toLp 1 (ofLp z)‖ ≤ 1}
      else
        A.transpose.toEuclideanLin ''
          ((fun coeff : Fin m → ℝ ↦
              toLp 2 fun i ↦ coeff i * Real.sign ((A.mulVecLin (ofLp x) + b) i)) ''
            activeCoordinateFace (fun i ↦ |(A.mulVecLin (ofLp x) + b) i|)) :=
by
  let r : Em := toLp 2 (A.mulVecLin (ofLp x) + b)
  rw [euclidean_subdifferentialAt_affine_linf_eq_transpose_image]
  change A.transpose.toEuclideanLin '' euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) r =
    if A.mulVecLin (ofLp x) + b = 0 then
      A.transpose.toEuclideanLin '' {z : Em | ‖toLp 1 (ofLp z)‖ ≤ 1}
    else
      A.transpose.toEuclideanLin ''
        ((fun coeff : Fin m → ℝ ↦
            toLp 2 fun i ↦ coeff i * Real.sign ((A.mulVecLin (ofLp x) + b) i)) ''
          activeCoordinateFace (fun i ↦ |(A.mulVecLin (ofLp x) + b) i|))
  have hr :
      A.transpose.toEuclideanLin '' euclideanSubdifferentialAt (fun y : Em ↦ ‖ofLp y‖) r =
        A.transpose.toEuclideanLin '' (
          if r = 0 then
            {z : Em | ‖toLp 1 (ofLp z)‖ ≤ 1}
          else
            (fun coeff : Fin m → ℝ ↦ toLp 2 fun i ↦ coeff i * Real.sign (r i)) ''
              activeCoordinateFace (fun i ↦ |r i|)) := by
    exact congrArg (fun s : Set Em ↦ A.transpose.toEuclideanLin '' s)
      (euclidean_subdifferentialAt_linf_eq_piecewise r)
  by_cases hr0 : r = 0
  · have h : A.mulVecLin (ofLp x) + b = 0 := by
      simpa [r] using congrArg ofLp hr0
    rw [if_pos h, hr0]
    have hr' := hr
    simp [hr0] at hr'
    simpa using hr'
  · have h : ¬A.mulVecLin (ofLp x) + b = 0 := by
      intro h'
      apply hr0
      simpa [r] using congrArg (toLp 2) h'
    rw [if_neg h]
    have hr' := hr
    simp [hr0] at hr'
    simpa [r] using hr'

end

/-! ### Theorem_3_26 (from Chap03) -/
noncomputable section

open Matrix
open WithLp (toLp)

section

variable {m n p : ℕ}
variable
  {f : (Fin n → ℝ) → ℝ}
  {g : (Fin n → ℝ) → Fin m → ℝ}
  {A : Matrix (Fin p) (Fin n) ℝ} {b : Fin p → ℝ}
  {xTilde : Fin n → ℝ}
  {fOpt rho1 rho2 delta : ℝ}

local notation "IneqSpace" => EuclideanSpace ℝ (Fin m)
local notation "EqSpace" => EuclideanSpace ℝ (Fin p)
local notation "ineqViolationVec" => (toLp 2 ((g xTilde)⁺) : IneqSpace)
local notation "eqResidualVec" => (toLp 2 (A *ᵥ xTilde + b) : EqSpace)
local notation "penalizedGap" =>
  f xTilde - fOpt + rho1 * ‖ineqViolationVec‖ + rho2 * ‖eqResidualVec‖

-- Proof sketch: the two penalty terms are norms multiplied by real coefficients, so they are
-- nonnegative. Dropping them from the left-hand side of the penalty estimate leaves the desired
-- upper bound for the objective gap.
/-- Theorem 3.26 (1): any point satisfying the penalized upper bound immediately satisfies
`f(x̃) - f_opt ≤ δ`. -/
theorem objective_gap_le_of_penalized_bound
    (hRho1Nonneg : 0 ≤ rho1) (hRho2Nonneg : 0 ≤ rho2)
    (hPenalty : penalizedGap ≤ delta) :
    f xTilde - fOpt ≤ delta := by
  have hPenalty1 : 0 ≤ rho1 * ‖ineqViolationVec‖ :=
    mul_nonneg hRho1Nonneg (norm_nonneg _)
  have hPenalty2 : 0 ≤ rho2 * ‖eqResidualVec‖ :=
    mul_nonneg hRho2Nonneg (norm_nonneg _)
  linarith

variable
  {X : Set (Fin n → ℝ)}
  {yStar : Fin m → ℝ} {zStar : Fin p → ℝ}

local notation "ineqMultiplierVec" => (toLp 2 yStar : IneqSpace)
local notation "eqMultiplierVec" => (toLp 2 zStar : EqSpace)

/- Theorem 3.26 is `source-facing` in the affine-constrained perturbation/penalty API. Its
`core/canonical` owner abstraction is `IsDualOptimalSolution`; the chapter perturbation owner
`value_function` and the bridge theorem
`isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero` from
`Theorem_3_24` explain why this owner is canonical. This file keeps only the source-facing penalty
estimates and does not add a parallel local owner API on top of those declarations. -/
recall IsDualOptimalSolution
recall isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero

-- Proof sketch: the dual-optimal solution with value `fOpt` gives the same affine lower bound
-- used in Theorem 3.24, now evaluated at the Euclidean bridge points
-- `u = toLp 2 ((g xTilde)⁺)` and `t = toLp 2 (A *ᵥ xTilde + b)`. Combining
-- that lower bound with the penalized estimate yields
-- `(rho1 - ‖toLp 2 yStar‖) * ‖toLp 2 ((g xTilde)⁺)‖ +
--   (rho2 - ‖toLp 2 zStar‖) * ‖toLp 2 (A *ᵥ xTilde + b)‖ ≤ delta`.
-- The extra assumption `‖toLp 2 zStar‖ ≤ rho2` makes the equality-residual term nonnegative, so
-- it may be discarded; the assumptions `0 < rho1` and `2 * ‖toLp 2 yStar‖ ≤ rho1` then give the
-- stated `2 / rho1` bound.
/-- Theorem 3.26 (2): given a dual optimal multiplier pair with optimal value `fOpt`, the positive
part of the inequality-constraint violation at `x̃`, measured in the Euclidean norm on
`WithLp 2 (Fin m → ℝ)`, is bounded by `(2 / ρ₁) δ` when the penalty parameter `ρ₁` dominates the
Euclidean norm of the inequality multiplier and `ρ₂` is at least the Euclidean norm of the
equality multiplier. -/
theorem positive_constraint_violation_le_two_div_rho1_of_penalized_bound
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hPenalty : penalizedGap ≤ delta)
    (hRho1Pos : 0 < rho1)
    (hRho1 : 2 * ‖ineqMultiplierVec‖ ≤ rho1)
    (hRho2 : ‖eqMultiplierVec‖ ≤ rho2) :
    ‖ineqViolationVec‖ ≤ (2 / rho1) * delta := sorry

-- Proof sketch: use the same dual-optimal affine lower bound with value `fOpt`,
-- `u = toLp 2 ((g xTilde)⁺)` and
-- `t = toLp 2 (A *ᵥ xTilde + b)`. The penalized estimate gives
-- `(rho1 - ‖toLp 2 yStar‖) * ‖toLp 2 ((g xTilde)⁺)‖ +
--   (rho2 - ‖toLp 2 zStar‖) * ‖toLp 2 (A *ᵥ xTilde + b)‖ ≤ delta`.
-- The extra assumption `‖toLp 2 yStar‖ ≤ rho1` makes the inequality-violation term nonnegative,
-- so it may be discarded; the assumptions `0 < rho2` and `2 * ‖toLp 2 zStar‖ ≤ rho2` then give
-- the claimed residual bound.
/-- Theorem 3.26 (3): given a dual optimal multiplier pair with optimal value `fOpt`, the equality
constraint residual at `x̃`, measured in the Euclidean norm on `WithLp 2 (Fin p → ℝ)`, is bounded
by `(2 / ρ₂) δ` when the penalty parameter `ρ₂` dominates the Euclidean norm of the equality
multiplier and `ρ₁` is at least the Euclidean norm of the inequality multiplier. -/
theorem equality_constraint_residual_le_two_div_rho2_of_penalized_bound
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hPenalty : penalizedGap ≤ delta)
    (hRho2Pos : 0 < rho2)
    (hRho2 : 2 * ‖eqMultiplierVec‖ ≤ rho2)
    (hRho1 : ‖ineqMultiplierVec‖ ≤ rho1) :
    ‖eqResidualVec‖ ≤ (2 / rho2) * delta := sorry

end
