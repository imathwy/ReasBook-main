import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_18 (from Chap02) -/
open scoped BigOperators lp

noncomputable section

local notation "ℝ∞" => ℓ²(ℕ, ℝ)
local notation "e1" => (lp.single 2 0 (1 : ℝ) : ℝ∞)

/-!
Definition 2.18 lies in the Hilbert-space quadratic lower-bound construction on
`ℝ∞ = ℓ²(ℕ, ℝ)`.

Sampled owner-style declarations in this domain:
* `ContinuousLinearMap.mkContinuous` in mathlib for the bounded-operator owner abstraction
* `lp.single` in mathlib for the first basis vector of `ℓ²(ℕ, ℝ)`
* `nesterovQuadraticObjective` in `Proposition_2_6` for the canonical quadratic owner attached to
  a bounded operator
* `inner` and `∑'` in mathlib for the quadratic-form and series surfaces used below

Best owner abstraction:
* `nesterovLowerBoundTridiagonalOperator : ℝ∞ →L[ℝ] ℝ∞`
* `nesterovLowerBoundOperatorObjective : ℝ → ℝ → ℝ∞ → ℝ`

Primitive data:
* the tridiagonal coordinate formula
* the induced bounded operator on `ℓ²(ℕ, ℝ)`
* the associated linear perturbation of the canonical quadratic owner

Derived API:
* the coordinate formulas for the tridiagonal operator
* the textbook expansion of the hard-instance objective
* the quadratic-form and objective series identities

Source/core/bridge triage:
* source-facing: the tridiagonal operator `A` and the hard-instance objective `f_{μ,Q_f}`
* core/canonical: the bounded-operator owner `ℝ∞ →L[ℝ] ℝ∞` and the quadratic owner
  `nesterovQuadraticObjective`
* bridge/view: the coordinate formulas and the series formulas recorded below
-/

/-- The coordinate formula underlying the infinite tridiagonal lower-bound operator. -/
private def tridiagonalApplyFn (x : ℝ∞) : ℕ → ℝ
  | 0 => 2 * x 0 - x 1
  | n + 1 => -x n + 2 * x (n + 1) - x (n + 2)

/-- Helper for Definition 2.18: the one-step successor shift on `ℓ₂(ℕ, ℝ)`. -/
private def successorShiftFn (x : ℝ∞) : ℕ → ℝ := fun n ↦ x (n + 1)

/-- Helper for Definition 2.18: the successor shift preserves square summability. -/
private theorem successorShift_mem (x : ℝ∞) :
    Memℓp (successorShiftFn x) 2 := by
  -- The tail of a square-summable series is square-summable.
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  exact memℓp_gen (by
    simpa [successorShiftFn] using hx.comp_injective Nat.succ_injective)

/-- Helper for Definition 2.18: the successor shift as an `ℓ₂(ℕ, ℝ)` vector. -/
private def successorShift (x : ℝ∞) : ℝ∞ :=
  ⟨successorShiftFn x, successorShift_mem x⟩

/-- Helper for Definition 2.18: the predecessor shift with a zero head. -/
private def predecessorShiftFn (x : ℝ∞) : ℕ → ℝ
  | 0 => 0
  | n + 1 => x n

/-- Helper for Definition 2.18: inserting a zero head preserves the predecessor-shift square
series. -/
private theorem predecessor_shift_sq_norm_tsum_eq (x : ℝ∞) :
    ∑' n : ℕ, ‖predecessorShiftFn x n‖ ^ (2 : ℝ) = ∑' n : ℕ, ‖x n‖ ^ (2 : ℝ) := by
  -- Summability of the original square series lets us recover the shifted series from its tail.
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  have htail :
      Summable (fun n : ℕ => ‖predecessorShiftFn x (n + 1)‖ ^ (2 : ℝ)) := by
    simpa [predecessorShiftFn] using hx
  have hpred :
      Summable (fun n : ℕ => ‖predecessorShiftFn x n‖ ^ (2 : ℝ)) :=
    (summable_nat_add_iff 1).1 htail
  -- Split off the zero head and identify the remaining tail with the original series.
  calc
    ∑' n : ℕ, ‖predecessorShiftFn x n‖ ^ (2 : ℝ)
        = ‖predecessorShiftFn x 0‖ ^ (2 : ℝ) +
            ∑' n : ℕ, ‖predecessorShiftFn x (n + 1)‖ ^ (2 : ℝ) := by
          symm
          simpa using (hpred.sum_add_tsum_nat_add 1)
    _ = ∑' n : ℕ, ‖x n‖ ^ (2 : ℝ) := by
          simp [predecessorShiftFn]

/-- Helper for Definition 2.18: the predecessor shift preserves square summability. -/
private theorem predecessorShift_mem (x : ℝ∞) :
    Memℓp (predecessorShiftFn x) 2 := by
  -- Recover full summability from the shifted tail, which is exactly the original square series.
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  have htail :
      Summable (fun n : ℕ => ‖predecessorShiftFn x (n + 1)‖ ^ (2 : ℝ)) := by
    simpa [predecessorShiftFn] using hx
  exact memℓp_gen ((summable_nat_add_iff 1).1 htail)

/-- Helper for Definition 2.18: the predecessor shift as an `ℓ₂(ℕ, ℝ)` vector. -/
private def predecessorShift (x : ℝ∞) : ℝ∞ :=
  ⟨predecessorShiftFn x, predecessorShift_mem x⟩

/-- Helper for Definition 2.18: the raw tridiagonal formula is `2I - S - S*` coordinatewise. -/
private theorem tridiagonalApplyFn_eq_two_smul_sub_shifts (x : ℝ∞) :
    tridiagonalApplyFn x =
      (2 : ℝ) • (x : ℕ → ℝ) - successorShiftFn x - predecessorShiftFn x := by
  -- Check the coordinate identity at `0` and at every successor index.
  funext n
  cases n with
  | zero =>
      simp [tridiagonalApplyFn, successorShiftFn, predecessorShiftFn, sub_eq_add_neg]
  | succ n =>
      simp [tridiagonalApplyFn, successorShiftFn, predecessorShiftFn, sub_eq_add_neg]
      ring

/-- Helper for Definition 2.18: the successor shift does not increase the `ℓ₂` norm. -/
private theorem successorShift_norm_le (x : ℝ∞) :
    ‖successorShift x‖ ≤ ‖x‖ := by
  -- Compare the tail series with the full square-norm series.
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  refine lp.norm_le_of_tsum_le (by norm_num) (lp.norm_nonneg' _) ?_
  have hsplit : ‖x 0‖ ^ (2 : ℝ) + ∑' n : ℕ, ‖x (n + 1)‖ ^ (2 : ℝ) = ∑' n : ℕ, ‖x n‖ ^ (2 : ℝ) := by
    simpa using (hx.sum_add_tsum_nat_add 1)
  have htail : ∑' n : ℕ, ‖x (n + 1)‖ ^ (2 : ℝ) ≤ ∑' n : ℕ, ‖x n‖ ^ (2 : ℝ) := by
    have hx0 : 0 ≤ ‖x 0‖ ^ (2 : ℝ) := by
      positivity
    linarith
  calc
    ∑' n : ℕ, ‖successorShift x n‖ ^ (2 : ℝ) ≤ ∑' n : ℕ, ‖x n‖ ^ (2 : ℝ) := by
      simpa [successorShift, successorShiftFn] using htail
    _ = ‖x‖ ^ (2 : ℝ) := by
      symm
      exact lp.norm_rpow_eq_tsum (by norm_num) x

/-- Helper for Definition 2.18: the predecessor shift does not increase the `ℓ₂` norm. -/
private theorem predecessorShift_norm_le (x : ℝ∞) :
    ‖predecessorShift x‖ ≤ ‖x‖ := by
  -- Compare the predecessor-shift square series directly with the square series of `x`.
  refine lp.norm_le_of_tsum_le (by norm_num) (lp.norm_nonneg' _) ?_
  calc
    ∑' n : ℕ, ‖predecessorShift x n‖ ^ (2 : ℝ)
        = ∑' n : ℕ, ‖x n‖ ^ (2 : ℝ) := by
          simpa [predecessorShift] using predecessor_shift_sq_norm_tsum_eq x
    _ = ‖x‖ ^ ENNReal.toReal 2 := by
          simpa using (lp.norm_rpow_eq_tsum (by norm_num) x).symm
    _ ≤ ‖x‖ ^ ENNReal.toReal 2 := le_rfl

/-- The tridiagonal coordinate formula sends an `ℓ₂` vector to another `ℓ₂` vector. -/
-- Proof sketch: estimate each output coordinate by a finite linear combination of neighboring
-- coordinates of `x`, then use square-summability of `x` and stability of `ℓ₂` under shifts and
-- finite sums.
private theorem tridiagonalApplyFn_mem (x : ℝ∞) :
    Memℓp (tridiagonalApplyFn x) 2 := by
  -- Rewrite the coordinate formula as a sum of three already-controlled `ℓ₂` vectors.
  have hmem :
      Memℓp (((2 : ℝ) • (x : ℕ → ℝ)) - ((successorShift x : ℝ∞) : ℕ → ℝ) -
        ((predecessorShift x : ℝ∞) : ℕ → ℝ)) 2 := by
    exact (((lp.memℓp x).const_smul (2 : ℝ)).sub (lp.memℓp (successorShift x))).sub
      (lp.memℓp (predecessorShift x))
  exact tridiagonalApplyFn_eq_two_smul_sub_shifts x ▸ hmem

/-- Helper for Definition 2.18: the raw tridiagonal formula is additive. -/
private theorem tridiagonalApplyFn_add (x y : ℝ∞) :
    tridiagonalApplyFn (x + y) = tridiagonalApplyFn x + tridiagonalApplyFn y := by
  -- Check additivity at the first coordinate and at every successor coordinate.
  funext n
  cases n with
  | zero =>
      change 2 * (x 0 + y 0) - (x 1 + y 1) =
          (2 * x 0 - x 1) + (2 * y 0 - y 1)
      ring
  | succ n =>
      change -(x n + y n) + 2 * (x (n + 1) + y (n + 1)) - (x (n + 2) + y (n + 2)) =
          (-x n + 2 * x (n + 1) - x (n + 2)) + (-y n + 2 * y (n + 1) - y (n + 2))
      ring

/-- Helper for Definition 2.18: the raw tridiagonal formula commutes with scalar multiplication. -/
private theorem tridiagonalApplyFn_smul (c : ℝ) (x : ℝ∞) :
    tridiagonalApplyFn (c • x) = c • tridiagonalApplyFn x := by
  -- Check homogeneity at `0` and at every successor index.
  funext n
  cases n with
  | zero =>
      simp [tridiagonalApplyFn]
      linarith
  | succ n =>
      simp [tridiagonalApplyFn]
      linarith

/-- The tridiagonal coordinate formula viewed as an element of `ℓ₂(ℕ, ℝ)`. -/
private def tridiagonalApply (x : ℝ∞) : ℝ∞ :=
  ⟨tridiagonalApplyFn x, tridiagonalApplyFn_mem x⟩

/-- Helper for Definition 2.18: the tridiagonal coordinate formula is `2I - S - S*`. -/
private theorem tridiagonalApply_eq_two_smul_sub_shifts (x : ℝ∞) :
    tridiagonalApply x = (2 : ℝ) • x - successorShift x - predecessorShift x := by
  -- Reduce the operator identity to the coordinate formula on the underlying functions.
  ext n
  simpa [tridiagonalApply, successorShift, predecessorShift] using
    congrArg (fun f : ℕ → ℝ => f n) (tridiagonalApplyFn_eq_two_smul_sub_shifts x)

/-- The tridiagonal coordinate formula is additive. -/
-- Proof sketch: compare coordinates at `0` and `n + 1`; each coordinate is a linear expression in
-- the corresponding coordinates of the input.
private theorem tridiagonalApply_add (x y : ℝ∞) :
    tridiagonalApply (x + y) = tridiagonalApply x + tridiagonalApply y := by
  -- Reduce the `ℓ₂` equality to the explicit coordinate formulas.
  ext n
  simpa [tridiagonalApply] using congrArg (fun f : ℕ → ℝ => f n) (tridiagonalApplyFn_add x y)

/-- The tridiagonal coordinate formula commutes with scalar multiplication. -/
-- Proof sketch: compare coordinates at `0` and `n + 1`; each coordinate is homogeneous of degree
-- one in the input.
private theorem tridiagonalApply_smul (c : ℝ) (x : ℝ∞) :
    tridiagonalApply (c • x) = c • tridiagonalApply x := by
  -- Reduce the `ℓ₂` equality to the explicit coordinate formulas.
  ext n
  simpa [tridiagonalApply] using congrArg (fun f : ℕ → ℝ => f n) (tridiagonalApplyFn_smul c x)

/-- The tridiagonal coordinate formula is bounded by a universal constant. -/
-- Proof sketch: bound each coordinate of `A x` by the sum of the absolute values of at most three
-- neighboring coordinates of `x`, square, and sum to obtain a uniform `ℓ₂` norm estimate.
private theorem tridiagonalApply_bound (x : ℝ∞) :
    ‖tridiagonalApply x‖ ≤ 4 * ‖x‖ := by
  -- Use the shift decomposition and the triangle inequality instead of a raw coordinate estimate.
  calc
    ‖tridiagonalApply x‖ = ‖(2 : ℝ) • x - successorShift x - predecessorShift x‖ := by
      rw [tridiagonalApply_eq_two_smul_sub_shifts]
    _ ≤ ‖(2 : ℝ) • x - successorShift x‖ + ‖predecessorShift x‖ := norm_sub_le _ _
    _ ≤ (‖(2 : ℝ) • x‖ + ‖successorShift x‖) + ‖predecessorShift x‖ := by
      linarith [norm_sub_le ((2 : ℝ) • x) (successorShift x)]
    _ ≤ ‖(2 : ℝ) • x‖ + ‖x‖ + ‖x‖ := by
      linarith [successorShift_norm_le x, predecessorShift_norm_le x]
    _ = 4 * ‖x‖ := by
      simp [norm_smul]
      ring

/-- Definition 2.18: the infinite tridiagonal operator `A` on `ℓ₂(ℕ, ℝ)` used in LecturesConvexOptimization_Nesterov_2018's
lower-bound construction. -/
def nesterovLowerBoundTridiagonalOperator : ℝ∞ →L[ℝ] ℝ∞ :=
  ({ toFun := tridiagonalApply
     map_add' := tridiagonalApply_add
     map_smul' := tridiagonalApply_smul } : ℝ∞ →ₗ[ℝ] ℝ∞).mkContinuous 4
    tridiagonalApply_bound

/-- The tridiagonal operator has the textbook value at the first coordinate. -/
-- Proof sketch: unfold `nesterovLowerBoundTridiagonalOperator`, `tridiagonalApply`, and
-- `tridiagonalApplyFn`.
@[simp] theorem nesterovLowerBoundTridiagonalOperator_apply_zero (x : ℝ∞) :
    nesterovLowerBoundTridiagonalOperator x 0 = 2 * x 0 - x 1 :=
  rfl

/-- The tridiagonal operator has the textbook value at every later coordinate. -/
-- Proof sketch: unfold `nesterovLowerBoundTridiagonalOperator`, `tridiagonalApply`, and
-- `tridiagonalApplyFn`.
@[simp] theorem nesterovLowerBoundTridiagonalOperator_apply_succ (x : ℝ∞) (n : ℕ) :
    nesterovLowerBoundTridiagonalOperator x (n + 1) = -x n + 2 * x (n + 1) - x (n + 2) :=
  rfl

/-- The hard-instance objective attached to the tridiagonal lower-bound operator. -/
def nesterovLowerBoundOperatorObjective (μ Q_f : ℝ) : ℝ∞ → ℝ :=
  nesterovQuadraticObjective μ Q_f nesterovLowerBoundTridiagonalOperator -
    fun x ↦ μ * (Q_f - 1) / 4 * inner ℝ e1 x

/-- Evaluating the hard-instance objective expands to its defining formula. -/
-- Proof sketch: unfold `nesterovLowerBoundOperatorObjective`, expand the canonical quadratic owner
-- `nesterovQuadraticObjective`, and reorder the scalar terms.
@[simp] theorem nesterovLowerBoundOperatorObjective_apply (μ Q_f : ℝ) (x : ℝ∞) :
    nesterovLowerBoundOperatorObjective μ Q_f x =
      (μ * (Q_f - 1) / 8) * inner ℝ x (nesterovLowerBoundTridiagonalOperator x) -
        (μ * (Q_f - 1) / 4) * inner ℝ e1 x +
        (μ / 2) * ‖x‖ ^ (2 : ℕ) := by
  simp [nesterovLowerBoundOperatorObjective, sub_eq_add_neg]
  ring

/-- Helper for Definition 2.18: the successor-shift inner product is the cross series. -/
private theorem successor_shift_inner_eq_cross_series (x : ℝ∞) :
    inner ℝ x (successorShift x) = ∑' n : ℕ, x n * x (n + 1) := by
  -- Expand the `ℓ₂` inner product coordinatewise and identify each term with the textbook cross
  -- term.
  calc
    inner ℝ x (successorShift x) = ∑' n : ℕ, inner ℝ (x n) (successorShift x n) :=
      lp.inner_eq_tsum (𝕜 := ℝ) x (successorShift x)
    _ = ∑' n : ℕ, x n * x (n + 1) := by
      refine tsum_congr ?_
      intro n
      have hcoord :
          inner ℝ (x n) (successorShift x n) =
            successorShift x n * (starRingEnd ℝ) (x n) :=
        RCLike.inner_apply (x n) (successorShift x n)
      simpa [successorShift, successorShiftFn, mul_comm] using hcoord

/-- Helper for Definition 2.18: the predecessor-shift inner product is the same cross series. -/
private theorem predecessor_shift_inner_eq_cross_series (x : ℝ∞) :
    inner ℝ x (predecessorShift x) = ∑' n : ℕ, x n * x (n + 1) := by
  -- Split the predecessor-shift inner product into its zero head and shifted tail.
  have hpred : Summable (fun n : ℕ => inner ℝ (x n) (predecessorShift x n)) := by
    simpa using (lp.summable_inner (𝕜 := ℝ) x (predecessorShift x))
  calc
    inner ℝ x (predecessorShift x) = ∑' n : ℕ, inner ℝ (x n) (predecessorShift x n) :=
      lp.inner_eq_tsum (𝕜 := ℝ) x (predecessorShift x)
    _ = inner ℝ (x 0) (predecessorShift x 0) +
          ∑' n : ℕ, inner ℝ (x (n + 1)) (predecessorShift x (n + 1)) := by
          symm
          simpa using (hpred.sum_add_tsum_nat_add 1)
    _ = ∑' n : ℕ, x n * x (n + 1) := by
          -- The head vanishes, and the tail reindexes to the same cross term.
          simp [predecessorShift, predecessorShiftFn]
          refine tsum_congr ?_
          intro n
          have hcoord :
              inner ℝ (x (n + 1)) (x n) =
                x n * (starRingEnd ℝ) (x (n + 1)) :=
            RCLike.inner_apply (x (n + 1)) (x n)
          simpa [mul_comm] using hcoord

/-- Helper for Definition 2.18: the head-plus-tail square series is the full square series. -/
private theorem head_add_tail_square_series_eq (x : ℝ∞) :
    x 0 ^ (2 : ℕ) + ∑' n : ℕ, x (n + 1) ^ (2 : ℕ) = ∑' n : ℕ, x n ^ (2 : ℕ) := by
  -- Split the square series of `x` at the first coordinate.
  have hxSq : Summable (fun n : ℕ => x n ^ (2 : ℕ)) := by
    simpa [Real.norm_eq_abs, sq_abs] using (lp.memℓp x).summable (by norm_num)
  simpa using (hxSq.sum_add_tsum_nat_add 1)

/-- Helper for Definition 2.18: the tridiagonal quadratic form equals the common normal form. -/
private theorem tridiagonal_inner_eq_normal_form (x : ℝ∞) :
    inner ℝ x (tridiagonalApply x) =
      2 * (∑' n : ℕ, x n ^ (2 : ℕ)) - 2 * (∑' n : ℕ, x n * x (n + 1)) := by
  -- Route correction: normalize `⟪x, (2I - S - S*)x⟫` term by term instead of expanding the
  -- tridiagonal coordinates directly.
  have hself :
      inner ℝ x x = ∑' n : ℕ, x n ^ (2 : ℕ) := by
    -- Convert the coordinatewise inner product of `x` with itself into the square series.
    calc
      inner ℝ x x = ∑' n : ℕ, inner ℝ (x n) (x n) := lp.inner_eq_tsum (𝕜 := ℝ) x x
      _ = ∑' n : ℕ, x n ^ (2 : ℕ) := by
            refine tsum_congr ?_
            intro n
            have hcoord :
                inner ℝ (x n) (x n) = x n * (starRingEnd ℝ) (x n) :=
              RCLike.inner_apply (x n) (x n)
            calc
              inner ℝ (x n) (x n) = x n * x n := by
                simpa using hcoord
              _ = x n ^ (2 : ℕ) := by
                ring
  -- Substitute the two shift identities into the `2I - S - S*` decomposition.
  calc
    inner ℝ x (tridiagonalApply x)
        = inner ℝ x ((2 : ℝ) • x) - inner ℝ x (successorShift x) -
            inner ℝ x (predecessorShift x) := by
          rw [tridiagonalApply_eq_two_smul_sub_shifts]
          simp [inner_sub_right]
    _ = 2 * inner ℝ x x - inner ℝ x (successorShift x) -
          inner ℝ x (predecessorShift x) := by
          simp [inner_smul_right]
    _ = 2 * (∑' n : ℕ, x n ^ (2 : ℕ)) - inner ℝ x (successorShift x) -
          inner ℝ x (predecessorShift x) := by
          rw [hself]
    _ = 2 * (∑' n : ℕ, x n ^ (2 : ℕ)) -
          2 * (∑' n : ℕ, x n * x (n + 1)) := by
          rw [successor_shift_inner_eq_cross_series, predecessor_shift_inner_eq_cross_series]
          ring

/-- Helper for Definition 2.18: the chain-difference series has the same normal form. -/
private theorem chain_series_eq_normal_form (x : ℝ∞) :
    x 0 ^ (2 : ℕ) + ∑' n : ℕ, (x n - x (n + 1)) ^ (2 : ℕ) =
      2 * (∑' n : ℕ, x n ^ (2 : ℕ)) - 2 * (∑' n : ℕ, x n * x (n + 1)) := by
  -- Expand the chain-difference square termwise and sum each series separately.
  have hxSq : Summable (fun n : ℕ => x n ^ (2 : ℕ)) := by
    simpa [Real.norm_eq_abs, sq_abs] using (lp.memℓp x).summable (by norm_num)
  have htailSq : Summable (fun n : ℕ => x (n + 1) ^ (2 : ℕ)) := by
    simpa using hxSq.comp_injective Nat.succ_injective
  have hcross : Summable (fun n : ℕ => x n * x (n + 1)) := by
    -- Summability of the cross term comes from the successor-shift inner product.
    have hs : Summable (fun n : ℕ => inner ℝ (x n) (successorShift x n)) := by
      simpa using (lp.summable_inner (𝕜 := ℝ) x (successorShift x))
    refine hs.congr ?_
    intro n
    have hcoord :
        inner ℝ (x n) (successorShift x n) =
          successorShift x n * (starRingEnd ℝ) (x n) :=
      RCLike.inner_apply (x n) (successorShift x n)
    simpa [successorShift, successorShiftFn, mul_comm] using hcoord
  have hscaled : Summable (fun n : ℕ => (2 : ℝ) * (x n * x (n + 1))) :=
    Summable.mul_left (2 : ℝ) hcross
  have hsub :
      Summable (fun n : ℕ => x n ^ (2 : ℕ) - (2 : ℝ) * (x n * x (n + 1))) :=
    hxSq.sub hscaled
  have htail :
      ∑' n : ℕ, x (n + 1) ^ (2 : ℕ) = ∑' n : ℕ, x n ^ (2 : ℕ) - x 0 ^ (2 : ℕ) := by
    linarith [head_add_tail_square_series_eq x]
  -- After the termwise expansion, the head-plus-tail square identity finishes the normalization.
  calc
    x 0 ^ (2 : ℕ) + ∑' n : ℕ, (x n - x (n + 1)) ^ (2 : ℕ)
        = x 0 ^ (2 : ℕ) +
            ∑' n : ℕ, (x n ^ (2 : ℕ) - (2 : ℝ) * (x n * x (n + 1)) +
              x (n + 1) ^ (2 : ℕ)) := by
          congr 1
          refine tsum_congr ?_
          intro n
          ring
    _ = x 0 ^ (2 : ℕ) +
          (∑' n : ℕ, (x n ^ (2 : ℕ) - (2 : ℝ) * (x n * x (n + 1))) +
            ∑' n : ℕ, x (n + 1) ^ (2 : ℕ)) := by
          rw [hsub.tsum_add htailSq]
    _ = x 0 ^ (2 : ℕ) +
          (((∑' n : ℕ, x n ^ (2 : ℕ)) - ∑' n : ℕ, (2 : ℝ) * (x n * x (n + 1))) +
            ∑' n : ℕ, x (n + 1) ^ (2 : ℕ)) := by
          rw [hxSq.tsum_sub hscaled]
    _ = x 0 ^ (2 : ℕ) +
          (((∑' n : ℕ, x n ^ (2 : ℕ)) - (2 : ℝ) * (∑' n : ℕ, x n * x (n + 1))) +
            ∑' n : ℕ, x (n + 1) ^ (2 : ℕ)) := by
          rw [tsum_mul_left]
    _ = 2 * (∑' n : ℕ, x n ^ (2 : ℕ)) - 2 * (∑' n : ℕ, x n * x (n + 1)) := by
          rw [htail]
          ring

/-- The quadratic form of the tridiagonal lower-bound operator is the textbook series
`x₀² + ∑ᵢ (xᵢ - xᵢ₊₁)²`. -/
-- Proof sketch: expand the inner product coordinatewise using the coordinate formulas for the
-- tridiagonal operator and regroup the resulting series terms.
theorem nesterovLowerBoundTridiagonalOperator_inner_eq_series (x : ℝ∞) :
    inner ℝ x (nesterovLowerBoundTridiagonalOperator x) =
      x 0 ^ (2 : ℕ) + ∑' i : ℕ, (x i - x (i + 1)) ^ (2 : ℕ) := by
  -- Reduce the continuous-linear operator to its coordinate realization and normalize both sides.
  change inner ℝ x (tridiagonalApply x) =
    x 0 ^ (2 : ℕ) + ∑' i : ℕ, (x i - x (i + 1)) ^ (2 : ℕ)
  calc
    inner ℝ x (tridiagonalApply x) =
        2 * (∑' n : ℕ, x n ^ (2 : ℕ)) - 2 * (∑' n : ℕ, x n * x (n + 1)) :=
      tridiagonal_inner_eq_normal_form x
    _ = x 0 ^ (2 : ℕ) + ∑' i : ℕ, (x i - x (i + 1)) ^ (2 : ℕ) :=
      (chain_series_eq_normal_form x).symm

/-- The hard-instance objective is exactly the displayed infinite-series formula from the text. -/
-- Proof sketch: unfold `nesterovLowerBoundOperatorObjective`, replace the quadratic term using
-- `nesterovLowerBoundTridiagonalOperator_inner_eq_series`, use `inner ℝ e1 x = x 0`, and collect
-- the scalar coefficients.
theorem nesterovLowerBoundOperatorObjective_eq_series (μ Q_f : ℝ) (x : ℝ∞) :
    nesterovLowerBoundOperatorObjective μ Q_f x =
      (μ * (Q_f - 1) / 8) *
          (x 0 ^ (2 : ℕ) + ∑' i : ℕ, (x i - x (i + 1)) ^ (2 : ℕ) - 2 * x 0) +
        (μ / 2) * ‖x‖ ^ (2 : ℕ) := by
  -- Replace the quadratic term by the chain series and the linear term by the first coordinate.
  have hsingle : inner ℝ e1 x = x 0 := by
    have h0 : inner ℝ e1 x = inner ℝ (1 : ℝ) (x 0) :=
      lp.inner_single_left (𝕜 := ℝ) 0 (1 : ℝ) x
    have h1 : inner ℝ (1 : ℝ) (x 0) = x 0 := by
      have hone :
          inner ℝ (1 : ℝ) (x 0) = x 0 * (starRingEnd ℝ) (1 : ℝ) :=
        RCLike.inner_apply (1 : ℝ) (x 0)
      simpa using hone
    exact h0.trans h1
  rw [nesterovLowerBoundOperatorObjective_apply]
  rw [nesterovLowerBoundTridiagonalOperator_inner_eq_series, hsingle]
  ring

/-! ### Lemma_2_18 (from Chap02) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Primary domain: finite max-type objectives built from real-Hilbert first-order models of
strongly convex and smooth components.

Sampled owner-style declarations:
* `StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt` in `Definition_2_14`;
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Mathlib`;
* `IsStrongConvexSmoothObjective` and `𝓢[μ, L]¹¹` in `Definition_2_17`;
* `maxTypeAffineApproximation` in `Definition_2_39`.

Best owner abstractions:
* `StrongConvexOn Set.univ μ` together with `ContDiff ℝ 1` for the lower tangent bound;
* `ContDiff ℝ 1` together with `LipschitzWith L (∇ ·)` for the upper tangent bound;
* `maxTypeObjective fi` and `maxTypeAffineApproximation fi xBar` from `Definition_2_39` for the
  max-type objective and its local affine model.

Primitive data:
* the nonempty finite component family `fi : ι → E → ℝ`;
* the component strong-convexity / `C¹` owner data for the lower estimate;
* the component `C¹` / Lipschitz-gradient owner data for the upper estimate.

Derived API:
* the owner max objective `maxTypeObjective fi`;
* component lower and upper tangent bounds recovered from the owner data;
* the textbook companion theorem with componentwise membership `fi i ∈ 𝓢[μ, L]¹¹`.

Source/core/bridge triage:
* source-facing: the paired quadratic bounds under the textbook componentwise hypothesis
  `fi i ∈ 𝓢[μ, L]¹¹`;
* core/canonical: `StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt`,
  `taylor_upper_bound_of_contDiffOne_withLipschitzGradient`, and
  `maxTypeAffineApproximation fi xBar`;
* bridge/view: passage from `fi i ∈ 𝓢[μ, L]¹¹` to the lower and upper owner data.

The public API below is kept at the owner-theorem level: the lower and upper inequalities are
exposed as separate canonical theorems with minimal hypotheses, while the textbook paired
statement remains as a thin source-facing companion. -/

section StrongConvexSmooth

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A finite max-type objective inherits the quadratic lower tangent bound from the corresponding
component-wise lower tangent bounds. -/
-- Proof sketch: apply the lower tangent bound for each component `fᵢ`, then take the finite
-- maximum over `i`; the common quadratic term is independent of `i` and factors out of the
-- resulting supremum.
private theorem maxTypeObjective_lower_tangent_quadratic_of_component_bounds
    (fi : ι → E → ℝ) (μ : ℝ)
    (hlower :
      ∀ i : ι, ∀ x xBar : E,
        fi i x ≥
          fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar) +
            (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ))
    (x xBar : E) :
    maxTypeObjective fi x ≥
      maxTypeAffineApproximation fi xBar x + (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  rw [maxTypeObjective_apply, maxTypeAffineApproximation_apply]
  have hsup :
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : ι ↦ fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar)) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ fi i x) -
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    rw [Finset.sup'_le_iff]
    intro i hi
    have hmax :
        fi i x ≤ Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ fi j x) := by
      exact Finset.le_sup' (fun j : ι ↦ fi j x) hi
    linarith [hlower i x xBar, hmax]
  linarith

/-- A finite max-type objective inherits the quadratic upper tangent bound from the corresponding
component-wise upper tangent bounds. -/
-- Proof sketch: apply the upper tangent bound for each component `fᵢ`, then take the finite
-- maximum over `i`; the common quadratic term is independent of `i` and factors out of the
-- resulting supremum.
private theorem maxTypeObjective_upper_tangent_quadratic_of_component_bounds
    (fi : ι → E → ℝ) (L : ℝ)
    (hupper :
      ∀ i : ι, ∀ x xBar : E,
        fi i x ≤
          fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar) +
            (L / 2) * ‖x - xBar‖ ^ (2 : ℕ))
    (x xBar : E) :
    maxTypeObjective fi x ≤
      maxTypeAffineApproximation fi xBar x + (L / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  rw [maxTypeObjective_apply, maxTypeAffineApproximation_apply, Finset.sup'_le_iff]
  intro i hi
  have hmodel :
      fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : ι ↦ fi j xBar + inner ℝ (∇ (fi j) xBar) (x - xBar)) := by
    exact
      Finset.le_sup'
        (fun j : ι ↦ fi j xBar + inner ℝ (∇ (fi j) xBar) (x - xBar)) hi
  linarith [hupper i x xBar, hmodel]

/-- If each component is `μ`-strongly convex on the whole space and `C¹`, then the finite
max-type objective satisfies the corresponding quadratic lower tangent bound relative to
`maxTypeAffineApproximation fi xBar`. -/
theorem maxTypeObjective_lower_tangent_quadratic_of_components
    (fi : ι → E → ℝ) (μ : ℝ)
    (hstrong : ∀ i : ι, StrongConvexOn Set.univ μ (fi i))
    (hcontDiff : ∀ i : ι, ContDiff ℝ 1 (fi i))
    (x xBar : E) :
    maxTypeObjective fi x ≥
      maxTypeAffineApproximation fi xBar x + (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
  maxTypeObjective_lower_tangent_quadratic_of_component_bounds fi μ
    (fun i x xBar ↦ by
      have hgrad : HasGradientAt (fi i) (∇ (fi i) xBar) xBar :=
        (hcontDiff i).differentiable_one xBar |>.hasGradientAt
      simpa using
        StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
          (hstrong i) (by simp) (by simp) hgrad)
    x xBar

/-- If each component is `C¹` and has `L`-Lipschitz gradient, then the finite max-type objective
satisfies the corresponding quadratic upper tangent bound relative to
`maxTypeAffineApproximation fi xBar`. -/
theorem maxTypeObjective_upper_tangent_quadratic_of_components
    (fi : ι → E → ℝ) (L : NNReal)
    (hcontDiff : ∀ i : ι, ContDiff ℝ 1 (fi i))
    (hgrad_lipschitz : ∀ i : ι, LipschitzWith L (∇ (fi i)))
    (x xBar : E) :
    maxTypeObjective fi x ≤
      maxTypeAffineApproximation fi xBar x + ((L : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
  maxTypeObjective_upper_tangent_quadratic_of_component_bounds fi (L : ℝ)
    (fun i x xBar ↦ by
      have hupper :=
        taylor_upper_bound_of_contDiffOne_withLipschitzGradient
          (hcontDiff i) (hgrad_lipschitz i) xBar x
      simpa [firstOrderTaylorModelAt_apply] using hupper)
    x xBar

/-- Lemma 2.18 in the chapter notation surface: if each component of a finite max-type objective
lies in `𝓢[μ, L]¹¹`, then the max-type function satisfies the corresponding lower and upper
quadratic bounds relative to its canonical affine approximation
`maxTypeAffineApproximation fi xBar`. -/
-- Proof sketch: pass from `fi i ∈ 𝓢[μ, L]¹¹` to the lower owner data
-- `StrongConvexOn Set.univ μ (fi i)` and `ContDiff ℝ 1 (fi i)`, and to the upper owner data
-- `ContDiff ℝ 1 (fi i)` and `LipschitzWith (Real.toNNReal L) (∇ (fi i))`; then apply the two
-- atomic owner theorems above and simplify the smoothness constant in the nontrivial ambient
-- case. The subsingleton case is tautological.
theorem maxTypeObjective_quadratic_bounds_of_components_mem
    (fi : ι → E → ℝ) (μ L : ℝ)
    (hfi : ∀ i : ι, fi i ∈ 𝓢[μ, L]¹¹)
    (x xBar : E) :
    maxTypeObjective fi x ≥
        maxTypeAffineApproximation fi xBar x + (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) ∧
      maxTypeObjective fi x ≤
        maxTypeAffineApproximation fi xBar x + (L / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  have hfi' : ∀ i : ι, IsStrongConvexSmoothObjective μ L (fi i) :=
    fun i ↦ mem_S11_iff.mp (hfi i)
  have hstrong : ∀ i : ι, StrongConvexOn Set.univ μ (fi i) :=
    fun i ↦ (hfi' i).strongConvexOn
  have hcontDiff : ∀ i : ι, ContDiff ℝ 1 (fi i) :=
    fun i ↦ (hfi' i).contDiff
  refine ⟨maxTypeObjective_lower_tangent_quadratic_of_components fi μ hstrong hcontDiff x xBar, ?_⟩
  by_cases hE : Subsingleton E
  · have hx : x = xBar := hE.elim x xBar
    subst hx
    simp [maxTypeObjective_apply, maxTypeAffineApproximation_apply]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let i0 : ι := Classical.choice ‹Nonempty ι›
    have hL : 0 ≤ L := le_trans (hfi' i0).mu_pos.le (hfi' i0).mu_le_L
    have hgrad_lipschitz : ∀ i : ι, LipschitzWith (Real.toNNReal L) (∇ (fi i)) := by
      intro i
      refine LipschitzWith.of_dist_le_mul ?_
      intro y z
      have hdist := (hfi' i).gradient_lipschitz y z
      have hL' : L ≤ (Real.toNNReal L : ℝ) := by
        simp [Real.toNNReal_of_nonneg hL]
      simpa [dist_eq_norm] using
        le_trans hdist (mul_le_mul_of_nonneg_right hL' (norm_nonneg _))
    simpa [Real.toNNReal_of_nonneg hL] using
      maxTypeObjective_upper_tangent_quadratic_of_components
        fi (Real.toNNReal L) hcontDiff hgrad_lipschitz x xBar

end StrongConvexSmooth

/-! ### Proposition_2_18 (from Chap02) -/
open Set

local notation "Q" => reciprocalEpigraphOnPositiveRay

/-!
Proposition 2.18 is source-facing in the convex-geometry domain of coordinate projections of the
owner epigraph `reciprocalEpigraphOnPositiveRay` in `ℝ²`.

Sampled owner-style declarations:
* `reciprocalEpigraphOnPositiveRay`
* `mem_reciprocalEpigraphOnPositiveRay_iff`
* `Prod.snd`
* `Set.mem_image`

Best owner abstraction:
* `reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)`

Primitive data:
* the owner set `Q = reciprocalEpigraphOnPositiveRay`

Derived API:
* the second-coordinate image `Prod.snd '' Q`
* its source-facing identification with the positive ray `Ioi (0 : ℝ)`

Source/core/bridge triage:
* source-facing: the textbook statement that the attainable second coordinates in `Q` are exactly
  the positive reals
* core/canonical: the owner set `Q = reciprocalEpigraphOnPositiveRay`
* bridge/view: `mem_reciprocalEpigraphOnPositiveRay_iff` and `Set.mem_image`

No parallel local “hyperbola region” set is introduced here; the proposition is phrased directly
as a statement about the owner set. -/

/-- Proposition 2.18: the second-coordinate projection of
`reciprocalEpigraphOnPositiveRay` is exactly the positive real half-line. The textbook region
`{(τ, x) | 0 < τ ∧ x ≥ 1 / τ}` is already represented by this owner set. -/
-- Proof sketch: if `(τ, x)` belongs to the epigraph, then `x ≥ 1 / τ > 0`. Conversely, for
-- `x > 0` the point `(1 / x, x)` lies in the epigraph and projects to `x`.
theorem snd_image_reciprocalEpigraphOnPositiveRay_eq_Ioi :
    Prod.snd '' Q = Ioi (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    -- Extract the positive first coordinate and the lower bound on the second coordinate.
    rcases (mem_reciprocalEpigraphOnPositiveRay_iff p).1 hp with ⟨hp₁, hp₂⟩
    exact lt_of_lt_of_le (one_div_pos.mpr hp₁) hp₂
  · intro hx
    have hmem : (1 / x, x) ∈ Q := by
      -- Choose `τ = 1 / x`, so the defining inequality becomes an equality.
      refine (mem_reciprocalEpigraphOnPositiveRay_iff (1 / x, x)).2 ?_
      constructor
      · exact one_div_pos.mpr hx
      · simp
    exact ⟨(1 / x, x), hmem, rfl⟩

/-! ### Theorem_2_18 (from Chap02) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: linear convergence of gradient descent on strongly convex smooth objectives over
real Hilbert spaces.

Owner-style declarations sampled for this refinement:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `gradientMethod` in `Algorithm_2_1`
* `gradientMethod_sqdist_le_geometric_rate` in `Theorem_2_17`

Best owner abstraction:
* the source-facing primitive objective data are `hf : f ∈ 𝓢[μ, L]¹¹`;
* the minimizer witness `hxStar : IsMinOn f Set.univ xStar` is separate primitive data;
* the canonical squared-distance contraction owner is
  `gradientMethod_sqdist_le_geometric_rate`;
* Theorem 2.18 is the optimal-step bridge/view obtained by specializing that owner theorem to
  `h = 2 / (μ + L)` and simplifying the scalar factor.

Accordingly, this file states Theorem 2.18 as the squared-distance reformulation of the canonical
optimal-step contraction theorem from `Theorem_2_17` on the intrinsic real-Hilbert-space owner
layer, rather than keeping a separate Euclidean-model statement or routing the proof through the
distance theorem and then squaring it again.
-/

section

variable {μ L : ℝ} {f : E → ℝ}

/-- Helper for Theorem 2.18: the optimal constant-step contraction factor from
`gradientMethod_sqdist_le_geometric_rate` is the square of the standard ratio
`(L - μ) / (L + μ)`. -/
private lemma optimal_step_factor_eq_ratio_sq (μ L : ℝ) (hden : 0 < μ + L) :
    1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) =
      ((L - μ) / (L + μ)) ^ (2 : ℕ) := by
  -- Clear the positive denominator and reduce to a polynomial identity.
  have hden_ne : μ + L ≠ 0 := ne_of_gt hden
  ring_nf
  field_simp [hden_ne]
  ring

/-- Theorem 2.18 on the intrinsic real-Hilbert-space owner layer: if `f : E → ℝ` lies in the
strongly convex smooth class `𝓢^{1,1}_{μ,L}` and `xStar` is a minimizer of `f`, then gradient
descent with step
size `2 / (μ + L)` contracts the squared distance to `xStar` by the factor
`((L - μ) / (L + μ))^(2k)` after `k` iterations. The textbook `ℝⁿ` statement is recovered by
specializing `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: specialize the owner squared-distance estimate
-- `gradientMethod_sqdist_le_geometric_rate` from `Theorem_2_17` to the optimal constant step size
-- `2 / (μ + L)`, then simplify the resulting contraction factor to
-- `((L - μ) / (L + μ))^(2k)`. In the nontrivial ambient case, `μ ≤ L` is derived from the owner
-- hypothesis; the subsingleton case is tautological.
theorem gradientMethod_sqdist_le_optimal_linear_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (((L - μ) / (L + μ)) ^ (2 * k)) * ‖(x0 - xStar)‖ ^ (2 : ℕ) := by
  -- Split off the degenerate ambient case, where all iterates and minimizers coincide.
  by_cases hE : Subsingleton E
  · have hx0 : x0 = xStar := hE.elim _ _
    subst hx0
    have hxk : gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k = x0 := hE.elim _ _
    simp [hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    -- The owner hypothesis gives the positivity needed to specialize the optimal step.
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 2 / (μ + L) := by
      positivity
    -- Specialize the geometric owner estimate at the optimal constant step size.
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate hf hxStar (2 / (μ + L)) hh0 le_rfl x0 k
    -- Rewrite the scalar rate into the textbook ratio and then combine exponents.
    calc
      ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
          (1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) :=
        hsq
      _ = (((L - μ) / (L + μ)) ^ (2 : ℕ)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        rw [optimal_step_factor_eq_ratio_sq μ L hden]
      _ = (((L - μ) / (L + μ)) ^ (2 * k)) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        rw [pow_mul]

end
