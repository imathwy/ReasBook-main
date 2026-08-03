import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction
open scoped InnerProductSpace
open Real

namespace ERealFunction

noncomputable section

-- Proof sketch: rewrite the real inner product as multiplication and convert the indexed supremum
-- from `conjugate_apply` into `sSup` over the range.
/-- On `ℝ`, evaluating `conjugate f` at `u` gives the scalar supremum formula
`sup_x (ux - f(x))`. -/
@[simp] theorem conjugate_apply_real (f : ℝ → EReal) (u : ℝ) :
    f∗ u = sSup (Set.range fun x : ℝ ↦ ((u * x : ℝ) : EReal) - f x) := by
  -- Rewrite the indexed supremum from `conjugate_apply` as an `sSup` over its range.
  rw [conjugate_apply, ← sSup_range]
  -- On `ℝ`, the inner product is ordinary multiplication.
  congr with x

/-- Helper for Example 13 2: a weighted sum of logarithms is nonpositive when the corresponding
affine-error terms already sum to a nonpositive quantity. -/
theorem weighted_log_le_of_affine_cancel
    {α β r s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hr : 0 < r) (hs : 0 < s)
    (hcancel : α * (r - 1) + β * (s - 1) ≤ 0) :
    α * Real.log r + β * Real.log s ≤ 0 := by
  -- Bound each logarithm by its affine tangent error and then add the two estimates.
  have hrlog : α * Real.log r ≤ α * (r - 1) := by
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr) hα
  have hslog : β * Real.log s ≤ β * (s - 1) := by
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hs) hβ
  linarith

/-- Helper for Example 13 2: an `sSup` equals `a` once every value is bounded above by `a` and
every strict lower bound of `a` is exceeded somewhere along the range. -/
theorem supremum_eq_of_pointwise_le_and_dense_lower_bounds
    (g : ℝ → EReal) (a : EReal) (h_upper : ∀ x, g x ≤ a)
    (h_lower : ∀ z, z < a → ∃ x, z < g x) :
    sSup (Set.range g) = a := by
  -- Apply the standard complete-lattice introduction rule for `sSup`.
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact h_upper x
  · intro z hz
    rcases h_lower z hz with ⟨x, hx⟩
    exact ⟨g x, ⟨x, rfl⟩, hx⟩

/-- The function `x ↦ 1 / x` on `(0,+∞)` and `+∞` on `(-∞,0]`. -/
noncomputable def reciprocalBarrier : ℝ → EReal :=
  fun x ↦ if 0 < x then ((1 / x : ℝ) : EReal) else ⊤

/-- The negative Burg entropy `x ↦ -log x` on `(0,+∞)` and `+∞` on `(-∞,0]`. -/
noncomputable def negativeBurgEntropy : ℝ → EReal :=
  fun x ↦ if 0 < x then ((-Real.log x : ℝ) : EReal) else ⊤

/-- The negative Fermi--Dirac entropy on `ℝ`, finite on `[0,1]` and `+∞` outside. -/
noncomputable def negativeFermiDiracEntropy : ℝ → EReal :=
  fun x ↦
    if 0 < x ∧ x < 1 then
      ((x * Real.log x + (1 - x) * Real.log (1 - x) : ℝ) : EReal)
    else if x = 0 ∨ x = 1 then
      0
    else
      ⊤

/-- The Bose--Einstein entropy on `ℝ`, finite on `[0,+∞)` and `+∞` on `(-∞,0)`. -/
noncomputable def boseEinsteinEntropy : ℝ → EReal :=
  fun x ↦
    if 0 < x then
      ((x * Real.log x - (x + 1) * Real.log (x + 1) : ℝ) : EReal)
    else if x = 0 then
      0
    else
      ⊤

/-- The negative Boltzmann--Shannon entropy, appearing as the conjugate of `exp`. -/
noncomputable def negativeBoltzmannShannonEntropy : ℝ → EReal :=
  fun u ↦
    if 0 < u then
      ((u * Real.log u - u : ℝ) : EReal)
    else if u = 0 then
      0
    else
      ⊤

/-- The logistic loss function, written as an `EReal`-valued map on `ℝ`. -/
noncomputable def logisticLoss : ℝ → EReal :=
  (fun u : ℝ ↦ Real.log (1 + Real.exp (-u))).toEReal.asEReal

/-- Helper for Example 13 2: the standard logarithmic defect `log y - y + 1` is nonpositive on
`(0, ∞)`. -/
theorem log_defect_nonpos {y : ℝ} (hy : 0 < y) :
    Real.log y - y + 1 ≤ 0 := by
  -- Rewrite the target as the tangent-line bound for `log`.
  linarith [Real.log_le_sub_one_of_pos hy]

/-- Helper for Example 13 2: the Young-extremizing point
`sign(u) * |u|^(Real.conjExponent p - 1)` attains the value `|u|^(Real.conjExponent p) /
Real.conjExponent p`. -/
theorem power_conjugate_maximizer_value
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    let q := Real.conjExponent p
    let x0 := Real.sign u * |u| ^ (q - 1)
    u * x0 - |x0| ^ p / p = |u| ^ q / q := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  have hp_ne : p ≠ 0 := hpq.ne_zero
  have hq_ne : q ≠ 0 := hpq.symm.ne_zero
  have hcoeff : 1 - 1 / p = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hqp : (q - 1) * p = q := by
    calc
      (q - 1) * p = (q / p) * p := by rw [hpq.symm.div_conj_eq_sub_one]
      _ = q := by field_simp [hp_ne]
  rcases eq_or_ne u 0 with rfl | hu0
  · have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hpq.symm.sub_one_pos
    -- At the origin, both the extremizing point and the optimal value vanish.
    simp [q, hp_ne, hq_ne, hq_sub_ne]
  · have hu_abs_pos : 0 < |u| := abs_pos.mpr hu0
    have hu_abs_nonneg : 0 ≤ |u| := abs_nonneg u
    have husign : u * Real.sign u = |u| := by
      rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
      · simp [Real.sign_of_neg hu_neg, abs_of_neg hu_neg]
      · simp [Real.sign_of_pos hu_pos, abs_of_pos hu_pos]
    have hsign_abs : |Real.sign u| = 1 := by
      rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
      · simp [Real.sign_of_neg hu_neg]
      · simp [Real.sign_of_pos hu_pos]
    have hx0_abs : |x0| = |u| ^ (q - 1) := by
      -- The sign contributes only an absolute value of `1`.
      simp [x0, abs_mul, hsign_abs, abs_of_nonneg (Real.rpow_nonneg hu_abs_nonneg _)]
    have hux0 : u * x0 = |u| ^ q := by
      -- First recover `|u|` from the sign, then combine the powers additively.
      calc
        u * x0 = (u * Real.sign u) * |u| ^ (q - 1) := by simp [x0, mul_assoc]
        _ = |u| * |u| ^ (q - 1) := by rw [husign]
        _ = |u| ^ (1 : ℝ) * |u| ^ (q - 1) := by simp
        _ = |u| ^ ((1 : ℝ) + (q - 1)) := by
          symm
          exact Real.rpow_add hu_abs_pos 1 (q - 1)
        _ = |u| ^ q := by congr 1; ring
    have hx0_pow : |x0| ^ p = |u| ^ q := by
      -- The Hölder-conjugate identity turns `(q - 1) * p` into `q`.
      rw [hx0_abs, ← Real.rpow_mul hu_abs_nonneg (q - 1) p, hqp]
    -- Substitute the maximizing value and simplify `1 - 1 / p = 1 / q`.
    calc
      u * x0 - |x0| ^ p / p = |u| ^ q - |u| ^ q / p := by rw [hux0, hx0_pow]
      _ = |u| ^ q * (1 - 1 / p) := by ring
      _ = |u| ^ q * (1 / q) := by rw [hcoeff]
      _ = |u| ^ q / q := by ring

-- Proof sketch: optimize the scalar function `x ↦ ux - |x|^p / p`; the maximizer satisfies the
-- usual Hölder-conjugate relation, yielding the closed form with exponent
-- `Real.conjExponent p`.
/-- Example 13 2: clause (i). For `p ∈ ]1,+∞[`, the conjugate of `x ↦ |x|^p / p` is
`u ↦ |u|^{p*} / p*`, where `p* = Real.conjExponent p = p / (p - 1)`. -/
theorem conjugate_absRpowDivided
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    ((fun x : ℝ ↦ (|x| ^ p) / p).toEReal.asEReal)∗ u =
      ((fun x : ℝ ↦ (|x| ^ Real.conjExponent p) / Real.conjExponent p).toEReal.asEReal) u := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  rw [conjugate_apply_real]
  simp only [Function.asEReal_apply, Function.toEReal_apply]
  -- Bound the scalar affine defect by Young's inequality and then realize equality at `x0`.
  refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
      (fun x : ℝ ↦ ((u * x : ℝ) : EReal) - ((|x| ^ p / p : ℝ) : EReal))
      ((|u| ^ q / q : ℝ) : EReal) ?_ ?_
  · intro x
    have hmul : u * x ≤ |x| * |u| := by
      calc
        u * x ≤ |u * x| := le_abs_self (u * x)
        _ = |u| * |x| := by rw [abs_mul]
        _ = |x| * |u| := by ring
    have hyoung :
        |x| * |u| ≤ |x| ^ p / p + |u| ^ q / q := by
      simpa [q, abs_abs] using Real.young_inequality_of_nonneg (abs_nonneg x) (abs_nonneg u) hpq
    have hreal : u * x - |x| ^ p / p ≤ |u| ^ q / q := by
      linarith
    have hEReal :
        ((u * x - |x| ^ p / p : ℝ) : EReal) ≤ ((|u| ^ q / q : ℝ) : EReal) :=
      EReal.coe_le_coe hreal
    simpa [sub_eq_add_neg, ← EReal.coe_sub] using hEReal
  · intro z hz
    have hvalue_real : u * x0 - |x0| ^ p / p = |u| ^ q / q := by
      simpa [q, x0] using power_conjugate_maximizer_value p hp u
    have hvalue :
        (((u * x0 : ℝ) : EReal) - ((|x0| ^ p / p : ℝ) : EReal)) =
          ((|u| ^ q / q : ℝ) : EReal) := by
      simpa [sub_eq_add_neg, ← EReal.coe_sub] using
        congrArg (fun t : ℝ ↦ (t : EReal)) hvalue_real
    exact ⟨x0, hz.trans_eq hvalue.symm⟩

/-- Helper for Example 13 2: on the positive branch of the reciprocal barrier, the scalar defect
is the claimed closed form plus a square correction. -/
theorem reciprocal_barrier_branch_eval
    (u x : ℝ) (hx : 0 < x) :
    (((u * x : ℝ) : EReal) - reciprocalBarrier x) = (((u * x - 1 / x : ℝ) : EReal)) := by
  -- On the positive branch, subtracting the finite reciprocal value is ordinary real subtraction.
  rw [reciprocalBarrier, if_pos hx]
  simpa [sub_eq_add_neg, ← EReal.coe_sub]

/-- Helper for Example 13 2: on the positive branch of the reciprocal barrier, the scalar defect
is the claimed closed form plus a square correction. -/
theorem reciprocal_barrier_defect_eq_closed_form_add_error
    {u x : ℝ} (hu : u < 0) (hx : 0 < x) :
    (((u * x : ℝ) : EReal) - reciprocalBarrier x) =
      (((-2 * Real.sqrt (-u) - (Real.sqrt (-u) * x - 1) ^ 2 / x : ℝ)) : EReal) := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hsq : Real.sqrt (-u) * Real.sqrt (-u) = -u := by
    -- The negative branch makes `-u` nonnegative, so its square root squares back to `-u`.
    simpa [pow_two] using Real.sq_sqrt (show 0 ≤ -u by linarith)
  have hreal :
      u * x - 1 / x =
        -2 * Real.sqrt (-u) - (Real.sqrt (-u) * x - 1) ^ 2 / x := by
    -- Expanding the square collapses the defect to the advertised closed form.
    field_simp [hx_ne]
    nlinarith [hsq]
  simpa [reciprocalBarrier, hx, sub_eq_add_neg, ← EReal.coe_sub] using
    congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Example 13 2: on the negative branch of the Burg entropy, the scalar defect is the
claimed closed form plus the standard logarithmic defect. -/
theorem negative_burg_branch_eval
    (u x : ℝ) (hx : 0 < x) :
    (((u * x : ℝ) : EReal) - negativeBurgEntropy x) =
      (((u * x + Real.log x : ℝ) : EReal)) := by
  -- On the positive branch, subtracting `-log x` is again ordinary real subtraction.
  rw [negativeBurgEntropy, if_pos hx]
  simpa [sub_eq_add_neg, ← EReal.coe_sub]

/-- Helper for Example 13 2: on the negative branch of the Burg entropy, the scalar defect is the
claimed closed form plus the standard logarithmic defect. -/
theorem negative_burg_defect_eq_closed_form_add_error
    {u x : ℝ} (hu : u < 0) (hx : 0 < x) :
    (((u * x : ℝ) : EReal) - negativeBurgEntropy x) =
      (((-Real.log (-u) - 1 + (Real.log ((-u) * x) - (-u) * x + 1) : ℝ)) : EReal) := by
  have hu_pos : 0 < -u := by linarith
  have hlog :
      Real.log ((-u) * x) = Real.log (-u) + Real.log x := by
    -- The finite branch stays on `(0, ∞)`, so the logarithm splits multiplicatively.
    rw [Real.log_mul hu_pos.ne' hx.ne']
  have hreal :
      u * x + Real.log x =
        -Real.log (-u) - 1 + (Real.log ((-u) * x) - (-u) * x + 1) := by
    -- After splitting the logarithm, the affine terms cancel to the original defect.
    rw [hlog]
    ring
  simpa [negativeBurgEntropy, hx, sub_eq_add_neg, ← EReal.coe_sub, add_assoc, add_left_comm,
    add_comm] using congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Example 13 2: on the positive branch of `exp`, the scalar defect is the closed
form plus the standard logarithmic defect in the normalized variable `exp x / u`. -/
theorem exp_defect_eq_closed_form_add_error
    {u x : ℝ} (hu : 0 < u) :
    (((u * x - Real.exp x : ℝ) : EReal)) =
      (((u * Real.log u - u + u * (Real.log (Real.exp x / u) - Real.exp x / u + 1) : ℝ)) :
        EReal) := by
  have hlog : Real.log (Real.exp x / u) = x - Real.log u := by
    -- Normalize the logarithm by dividing `exp x` by the positive parameter `u`.
    rw [Real.log_div (Real.exp_ne_zero x) hu.ne']
    simp
  have hreal :
      u * x - Real.exp x =
        u * Real.log u - u + u * (Real.log (Real.exp x / u) - Real.exp x / u + 1) := by
    -- Substituting the normalized logarithm reduces the identity to ring arithmetic.
    rw [hlog]
    field_simp [hu.ne']
    ring
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Example 13 2: subtracting the finite exponential branch is just ordinary real
subtraction inside `EReal`. -/
theorem exp_branch_eval (u x : ℝ) :
    (((u * x : ℝ) : EReal) - (exp.toEReal.asEReal x)) = (((u * x - Real.exp x : ℝ) : EReal)) := by
  -- The exponential branch is finite everywhere, so the `EReal` subtraction is just real
  -- subtraction after coercion.
  simp [Function.asEReal_apply, Function.toEReal_apply, sub_eq_add_neg]

/-- Helper for Example 13 2: on the negative Burg branch, the source maximizer
`x0 = (-u)⁻¹` attains the closed-form value. -/
theorem negative_burg_maximizer_value
    {u : ℝ} (hu : u < 0) :
    let x0 := (-u)⁻¹
    (((u * x0 : ℝ) : EReal) - negativeBurgEntropy x0) =
      (((-Real.log (-u) - 1 : ℝ)) : EReal) := by
  dsimp
  have hu_pos : 0 < -u := by linarith
  have hx0 : 0 < (-u)⁻¹ := by
    -- The explicit maximizer stays in the finite branch of the entropy.
    simpa [one_div] using inv_pos.mpr hu_pos
  have hu_ne : -u ≠ 0 := by linarith
  have hmul : u * (-u)⁻¹ = -1 := by
    -- Multiplying by the reciprocal of `-u` gives the expected sign-normalized value.
    calc
      u * (-u)⁻¹ = -((-u) * (-u)⁻¹) := by ring
      _ = -1 := by rw [mul_inv_cancel₀ hu_ne]
  have hlog_inv : Real.log ((-u)⁻¹) = -Real.log (-u) := by
    rw [Real.log_inv]
  have hreal :
      u * (-u)⁻¹ - (-Real.log ((-u)⁻¹)) = -Real.log (-u) - 1 := by
    rw [hlog_inv, hmul]
    ring
  rw [negativeBurgEntropy, if_pos hx0]
  simpa [sub_eq_add_neg, ← EReal.coe_sub] using congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Example 13 2: on the negative reciprocal branch, the source maximizer
`x0 = 1 / sqrt(-u)` attains the closed-form value. -/
theorem reciprocal_barrier_maximizer_value
    {u : ℝ} (hu : u < 0) :
    let x0 := 1 / Real.sqrt (-u)
    (((u * x0 : ℝ) : EReal) - reciprocalBarrier x0) =
      (((-2 * Real.sqrt (-u) : ℝ)) : EReal) := by
  dsimp
  have hu_pos : 0 < -u := by linarith
  have hsqrt_pos : 0 < Real.sqrt (-u) := Real.sqrt_pos.mpr hu_pos
  have hx0 : 0 < 1 / Real.sqrt (-u) := by
    -- The reciprocal maximizer also stays on the positive branch.
    exact one_div_pos.mpr hsqrt_pos
  have hinv : 1 / (1 / Real.sqrt (-u)) = Real.sqrt (-u) := by
    field_simp [hsqrt_pos.ne']
  have hsq : Real.sqrt (-u) ^ 2 = -u := by
    simpa [pow_two] using Real.sq_sqrt (show 0 ≤ -u by linarith)
  have hmul : u * (1 / Real.sqrt (-u)) = -Real.sqrt (-u) := by
    field_simp [hsqrt_pos.ne']
    nlinarith [hsq]
  have hreal :
      u * (1 / Real.sqrt (-u)) - (1 / (1 / Real.sqrt (-u))) =
        -2 * Real.sqrt (-u) := by
    rw [hinv, hmul]
    ring
  rw [reciprocalBarrier, if_pos hx0]
  simpa [hinv, sub_eq_add_neg, ← EReal.coe_sub] using congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Example 13 2: every negative real number lies below `-1 / x` for some positive
`x`. -/
theorem exists_pos_lt_neg_inv
    (r : ℝ) (hr : r < 0) :
    ∃ x > 0, r < -(1 / x) := by
  refine ⟨-2 / r, ?_, ?_⟩
  · -- Scaling a negative number by `-2` produces a positive witness.
    exact div_pos_of_neg_of_neg (by norm_num) hr
  · -- This choice yields the larger negative value `r / 2`.
    have hr_ne : r ≠ 0 := ne_of_lt hr
    field_simp [hr_ne]
    linarith

/-- Helper for Example 13 2: on the positive reciprocal branch, the affine term eventually
dominates the reciprocal tail. -/
theorem exists_pos_affine_minus_inv_gt
    (u r : ℝ) (hu : 0 < u) :
    ∃ x > 0, r < u * x - 1 / x := by
  let x : ℝ := (|r| + 2) / u + 1
  have hx_pos : 0 < x := by
    -- The explicit witness is positive because both summands are positive.
    dsimp [x]
    positivity
  have hx_one : 1 < x := by
    -- The positive quotient keeps the witness strictly above `1`.
    have hq_pos : 0 < (|r| + 2) / u := by
      have hnum_pos : 0 < |r| + 2 := by nlinarith [abs_nonneg r]
      exact div_pos hnum_pos hu
    dsimp [x]
    linarith
  have hmul : u * x = |r| + 2 + u := by
    -- Multiplying back by `u` removes the quotient exactly.
    dsimp [x]
    field_simp [hu.ne']
  have hinv : 1 / x < 1 := by
    -- Since `x > 1`, its reciprocal is strictly below `1`.
    simpa [one_div] using inv_lt_one_of_one_lt₀ hx_one
  refine ⟨x, hx_pos, ?_⟩
  -- Combine the large affine term with the small reciprocal tail.
  have hbig : r < u * x - 1 := by
    rw [hmul]
    have hr_abs : r ≤ |r| := le_abs_self r
    linarith
  have htail : u * x - 1 < u * x - 1 / x := by
    linarith
  exact lt_trans hbig htail

/-- Helper for Example 13 2: on the nonnegative Burg branch, the path `x = exp t` sends
`u * x + log x` above every finite level. -/
theorem exists_pos_affine_add_log_gt
    (u r : ℝ) (hu : 0 ≤ u) :
    ∃ x > 0, r < u * x + Real.log x := by
  refine ⟨Real.exp (r + 1), Real.exp_pos _, ?_⟩
  -- Choosing `x = exp (r + 1)` realizes the logarithmic part exactly.
  have hux_nonneg : 0 ≤ u * Real.exp (r + 1) := mul_nonneg hu (le_of_lt (Real.exp_pos _))
  have hlog : Real.log (Real.exp (r + 1)) = r + 1 := Real.log_exp (r + 1)
  linarith

/-- Helper for Example 13 2: on the negative exponential branch, the path `x → -∞` makes the
linear term dominate `exp x`. -/
theorem exists_affine_minus_exp_gt
    (u r : ℝ) (hu : u < 0) :
    ∃ x : ℝ, r < u * x - Real.exp x := by
  refine ⟨(|r| + 2) / u, ?_⟩
  have hx_neg : (|r| + 2) / u < 0 := by
    -- Dividing a positive numerator by the negative parameter sends the witness to `(-∞, 0)`.
    have hnum_pos : 0 < |r| + 2 := by nlinarith [abs_nonneg r]
    exact div_neg_of_pos_of_neg hnum_pos hu
  have hmul : u * ((|r| + 2) / u) = |r| + 2 := by
    calc
      u * ((|r| + 2) / u) = u * ((|r| + 2) * u⁻¹) := by rw [div_eq_mul_inv]
      _ = (u * u⁻¹) * (|r| + 2) := by ring
      _ = |r| + 2 := by rw [mul_inv_cancel₀ (ne_of_lt hu), one_mul]
  have hexp : Real.exp ((|r| + 2) / u) < 1 := by
    exact Real.exp_lt_one_iff.mpr hx_neg
  have hr_abs : r ≤ |r| := le_abs_self r
  -- The affine term is `|r| + 2`, while the exponential tail stays below `1`.
  linarith

/-- Helper for Example 13 2: on the positive exponential branch, the source maximizer
`x0 = log u` attains the closed-form value. -/
theorem exp_maximizer_value
    {u : ℝ} (hu : 0 < u) :
    let x0 := Real.log u
    (((u * x0 - Real.exp x0 : ℝ) : EReal)) =
      (((u * Real.log u - u : ℝ) : EReal)) := by
  dsimp
  -- The positive-branch maximizer is exactly `x0 = log u`.
  rw [Real.exp_log hu]

/-- Helper for Example 13 2: a finite real lower witness for `u * x - exp x` upgrades to an
`EReal` lower witness in the same range. -/
theorem exists_lt_exp_range_of_real_lower
    {u : ℝ} {z : EReal} (hz_top : z ≠ ⊤) (hz_bot : z ≠ ⊥)
    (h : ∃ x : ℝ, z.toReal < u * x - Real.exp x) :
    ∃ x : ℝ, z < (((u * x - Real.exp x : ℝ) : EReal)) := by
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Finite `EReal` bounds can be compared after rewriting them by `toReal`.
  rw [← EReal.coe_toReal hz_top hz_bot]
  exact EReal.coe_lt_coe_iff.mpr hx

/-- Helper for Example 13 2: every negative real number lies below `-exp x` for some `x`. -/
theorem exists_lt_neg_exp_of_real_lower
    (r : ℝ) (hr : r < 0) :
    ∃ x : ℝ, r < -Real.exp x := by
  have hhalf_pos : 0 < -r / 2 := by linarith
  refine ⟨Real.log (-r / 2), ?_⟩
  -- Choosing `x = log (-r / 2)` turns the exponential term into `-r / 2`.
  rw [Real.exp_log hhalf_pos]
  linarith

-- Proof sketch: maximize `ux - 1 / x` over `x > 0`; the optimizer is `x = 1 / √(-u)` when
-- `u ≤ 0`, and for `u > 0` the supremum is `+∞`.
/-- Example 13.2 (2): clause (ii). The conjugate of `x ↦ 1/x` on `(0,+∞)` is
`u ↦ -2√(-u)` on `(-∞,0]` and `+∞` on `(0,+∞)`. -/
theorem conjugate_reciprocalBarrier (u : ℝ) :
    reciprocalBarrier∗ u =
      if u ≤ 0 then ((-2 * Real.sqrt (-u) : ℝ) : EReal) else ⊤ := by
  rw [conjugate_apply_real]
  by_cases hu_nonpos : u ≤ 0
  · rw [if_pos hu_nonpos]
    by_cases hu_neg : u < 0
    · refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
          (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - reciprocalBarrier x))
          (((-2 * Real.sqrt (-u) : ℝ) : EReal)) ?_ ?_
      · intro x
        by_cases hx : 0 < x
        · -- On the finite branch, the closed-form defect identity leaves only a nonpositive square
          -- correction to control.
          change (((u * x : ℝ) : EReal) - reciprocalBarrier x) ≤
              (((-2 * Real.sqrt (-u) : ℝ) : EReal))
          rw [reciprocal_barrier_defect_eq_closed_form_add_error (u := u) (x := x) hu_neg hx]
          refine EReal.coe_le_coe ?_
          have hsq_nonneg : 0 ≤ (Real.sqrt (-u) * x - 1) ^ 2 / x := by
            positivity
          linarith
        · -- Outside `(0, ∞)`, the barrier is `⊤`, so the defect is `⊥`.
          simpa [hx, reciprocalBarrier]
      · intro z hz
        refine ⟨1 / Real.sqrt (-u), ?_⟩
        -- The explicit maximizer from the source proof attains the finite supremum exactly.
        change z < (((u * (1 / Real.sqrt (-u)) : ℝ) : EReal) -
            reciprocalBarrier (1 / Real.sqrt (-u)))
        have hvalue :
            (((u * (1 / Real.sqrt (-u)) : ℝ) : EReal) -
                reciprocalBarrier (1 / Real.sqrt (-u))) =
              (((-2 * Real.sqrt (-u) : ℝ) : EReal)) := by
          simpa using reciprocal_barrier_maximizer_value (u := u) hu_neg
        exact hz.trans_eq hvalue.symm
    · have hu_zero : u = 0 := le_antisymm hu_nonpos (le_of_not_gt hu_neg)
      have hsup : sSup (Set.range fun x : ℝ ↦ (((u * x : ℝ) : EReal) - reciprocalBarrier x)) = 0 := by
        refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
            (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - reciprocalBarrier x)) 0 ?_ ?_
        · intro x
          by_cases hx : 0 < x
          · -- At `u = 0`, the finite branch is just `-1 / x`, which is nonpositive.
            change (((u * x : ℝ) : EReal) - reciprocalBarrier x) ≤ 0
            rw [reciprocal_barrier_branch_eval (u := u) (x := x) hx]
            refine EReal.coe_le_coe ?_
            calc
              u * x - 1 / x = -(1 / x) := by simp [hu_zero]
              _ ≤ 0 := by
                have hdiv_nonneg : 0 ≤ 1 / x := by positivity
                linarith
          · -- Outside `(0, ∞)`, the barrier again forces the defect to `⊥`.
            simpa [hx, reciprocalBarrier]
        · intro z hz
          by_cases hz_bot : z = ⊥
          · refine ⟨1, ?_⟩
            rw [hz_bot]
            change ⊥ < (((u * (1 : ℝ) : ℝ) : EReal) - reciprocalBarrier (1 : ℝ))
            have hvalue :
                (((u * (1 : ℝ) : ℝ) : EReal) - reciprocalBarrier (1 : ℝ)) =
                  (((-1 : ℝ) : EReal)) := by
              simpa [hu_zero] using
                reciprocal_barrier_branch_eval (u := u) (x := (1 : ℝ))
                  (by norm_num : 0 < (1 : ℝ))
            rw [hvalue]
            exact EReal.bot_lt_coe (-1 : ℝ)
          · have hz_top : z ≠ ⊤ := by
              intro hz_eq_top
              simpa [hz_eq_top] using hz
            have hz_real : z.toReal < 0 := EReal.toReal_neg hz hz_bot
            rcases exists_pos_lt_neg_inv z.toReal hz_real with ⟨x, hx, hxlt⟩
            refine ⟨x, ?_⟩
            change z < (((u * x : ℝ) : EReal) - reciprocalBarrier x)
            rw [← EReal.coe_toReal hz_top hz_bot]
            rw [reciprocal_barrier_branch_eval (u := u) (x := x) hx]
            simpa [hu_zero] using (EReal.coe_lt_coe_iff.mpr hxlt)
      simpa [hu_zero] using hsup
  · have hu_pos : 0 < u := lt_of_not_ge hu_nonpos
    rw [if_neg hu_nonpos]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - reciprocalBarrier x)) ⊤ ?_ ?_
    · intro x
      exact le_top
    · intro z hz
      by_cases hz_bot : z = ⊥
      · refine ⟨1, ?_⟩
        rw [hz_bot]
        change ⊥ < (((u * (1 : ℝ) : ℝ) : EReal) - reciprocalBarrier (1 : ℝ))
        have hvalue :
            (((u * (1 : ℝ) : ℝ) : EReal) - reciprocalBarrier (1 : ℝ)) =
              (((u - 1 : ℝ) : EReal)) := by
          simpa using
            reciprocal_barrier_branch_eval (u := u) (x := (1 : ℝ)) (by norm_num : 0 < (1 : ℝ))
        rw [hvalue]
        exact EReal.bot_lt_coe (u - 1 : ℝ)
      · have hz_top : z ≠ ⊤ := lt_top_iff_ne_top.mp hz
        rcases exists_pos_affine_minus_inv_gt u z.toReal hu_pos with ⟨x, hx, hxlt⟩
        refine ⟨x, ?_⟩
        change z < (((u * x : ℝ) : EReal) - reciprocalBarrier x)
        rw [← EReal.coe_toReal hz_top hz_bot]
        rw [reciprocal_barrier_branch_eval (u := u) (x := x) hx]
        exact EReal.coe_lt_coe_iff.mpr hxlt

-- Proof sketch: maximize `ux + log x` over `x > 0`; the critical point occurs at `x = -1 / u`
-- for `u < 0`, while `u ≥ 0` forces the supremum to be `+∞`.
/-- Example 13.2 (3): clause (iii). The conjugate of the negative Burg entropy is
`u ↦ -log(-u) - 1` on `(-∞,0)` and `+∞` on `[0,+∞)`. -/
theorem conjugate_negativeBurgEntropy (u : ℝ) :
    negativeBurgEntropy∗ u =
      if u < 0 then ((-Real.log (-u) - 1 : ℝ) : EReal) else ⊤ := by
  rw [conjugate_apply_real]
  by_cases hu_neg : u < 0
  · rw [if_pos hu_neg]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - negativeBurgEntropy x))
        (((-Real.log (-u) - 1 : ℝ) : EReal)) ?_ ?_
    · intro x
      by_cases hx : 0 < x
      · -- On the finite branch, the remaining logarithmic defect is always nonpositive.
        change (((u * x : ℝ) : EReal) - negativeBurgEntropy x) ≤
            (((-Real.log (-u) - 1 : ℝ) : EReal))
        rw [negative_burg_defect_eq_closed_form_add_error (u := u) (x := x) hu_neg hx]
        refine EReal.coe_le_coe ?_
        have hu_pos : 0 < -u := by linarith
        have hy : 0 < (-u) * x := mul_pos hu_pos hx
        have hdefect : Real.log ((-u) * x) - (-u) * x + 1 ≤ 0 := log_defect_nonpos hy
        linarith
      · -- The entropy is `⊤` off the positive branch, so the defect collapses to `⊥`.
        simpa [hx, negativeBurgEntropy]
    · intro z hz
      refine ⟨(-u)⁻¹, ?_⟩
      -- The explicit maximizer `(-u)⁻¹` realizes the closed-form value.
      change z < (((u * (-u)⁻¹ : ℝ) : EReal) - negativeBurgEntropy (-u)⁻¹)
      have hvalue :
          (((u * (-u)⁻¹ : ℝ) : EReal) - negativeBurgEntropy (-u)⁻¹) =
            (((-Real.log (-u) - 1 : ℝ) : EReal)) := by
        simpa using negative_burg_maximizer_value (u := u) hu_neg
      exact hz.trans_eq hvalue.symm
  · have hu_nonneg : 0 ≤ u := le_of_not_gt hu_neg
    rw [if_neg hu_neg]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - negativeBurgEntropy x)) ⊤ ?_ ?_
    · intro x
      exact le_top
    · intro z hz
      by_cases hz_bot : z = ⊥
      · refine ⟨1, ?_⟩
        rw [hz_bot]
        change ⊥ < (((u * (1 : ℝ) : ℝ) : EReal) - negativeBurgEntropy (1 : ℝ))
        have hvalue :
            (((u * (1 : ℝ) : ℝ) : EReal) - negativeBurgEntropy (1 : ℝ)) = (((u : ℝ) : EReal)) := by
          simpa using
            negative_burg_branch_eval (u := u) (x := (1 : ℝ)) (by norm_num : 0 < (1 : ℝ))
        rw [hvalue]
        exact EReal.bot_lt_coe u
      · have hz_top : z ≠ ⊤ := lt_top_iff_ne_top.mp hz
        rcases exists_pos_affine_add_log_gt u z.toReal hu_nonneg with ⟨x, hx, hxlt⟩
        refine ⟨x, ?_⟩
        change z < (((u * x : ℝ) : EReal) - negativeBurgEntropy x)
        rw [← EReal.coe_toReal hz_top hz_bot]
        rw [negative_burg_branch_eval (u := u) (x := x) hx]
        exact EReal.coe_lt_coe_iff.mpr hxlt

-- The `cosh` proof first isolates the weighted logarithmic defects into a separate affine/exponential
-- identity before substituting the hyperbolic identities at `arsinh u`.
/-- Helper for Example 13 2: the two weighted logarithmic defects in the `cosh` computation split
into an affine `(x - arsinh u)` term plus the difference of the corresponding `cosh` exponentials.
-/
theorem cosh_defect_split_affine_terms (u x : ℝ) :
    let a := Real.arsinh u
    (Real.exp a / 2) *
        (Real.log (Real.exp x / Real.exp a) - Real.exp x / Real.exp a + 1) +
      (Real.exp (-a) / 2) *
        (Real.log (Real.exp (-x) / Real.exp (-a)) - Real.exp (-x) / Real.exp (-a) + 1) =
      (Real.exp a / 2 - Real.exp (-a) / 2) * (x - a) +
        ((Real.exp a / 2 + Real.exp (-a) / 2) - (Real.exp x / 2 + Real.exp (-x) / 2)) := by
  -- Expand the two logarithms of exponential quotients before collecting the affine terms.
  dsimp
  rw [Real.log_div (Real.exp_ne_zero x) (Real.exp_ne_zero (Real.arsinh u)),
    Real.log_div (Real.exp_ne_zero (-x)) (Real.exp_ne_zero (-Real.arsinh u))]
  simp only [Real.log_exp]
  field_simp
  ring

/-- Helper for Example 13 2: on the finite branch of the negative Fermi--Dirac entropy,
subtracting the entropy is ordinary real subtraction inside `EReal`. -/
theorem negative_fermi_dirac_branch_eval
    (u x : ℝ) (hx : 0 < x ∧ x < 1) :
    (((u * x : ℝ) : EReal) - negativeFermiDiracEntropy x) =
      (((u * x - (x * Real.log x + (1 - x) * Real.log (1 - x)) : ℝ)) : EReal) := by
  -- The interior branch of the entropy is finite, so `EReal` subtraction reduces to real
  -- subtraction after coercion.
  rw [negativeFermiDiracEntropy, if_pos hx]
  rw [sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add]
  rfl

/-- Helper for Example 13 2: on the positive branch of the Bose--Einstein entropy, subtracting
the entropy is ordinary real subtraction inside `EReal`. -/
theorem bose_einstein_branch_eval
    (u x : ℝ) (hx : 0 < x) :
    (((u * x : ℝ) : EReal) - boseEinsteinEntropy x) =
      (((u * x - (x * Real.log x - (x + 1) * Real.log (x + 1)) : ℝ)) : EReal) := by
  -- The positive branch is finite as well, so the defect is just the coerced real expression.
  rw [boseEinsteinEntropy, if_pos hx]
  rw [sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add]
  rfl

/-- Helper for Example 13 2: the `cosh` defect can be rewritten as the claimed closed form plus
two logarithmic defects centered at the source maximizer `arsinh u`. -/
theorem cosh_defect_eq_closed_form_add_log_defects (u x : ℝ) :
    let a := Real.arsinh u
    u * x - Real.cosh x =
      (u * a - Real.sqrt (1 + u ^ 2)) +
        (Real.exp a / 2) *
        (Real.log (Real.exp x / Real.exp a) - Real.exp x / Real.exp a + 1) +
        (Real.exp (-a) / 2) *
          (Real.log (Real.exp (-x) / Real.exp (-a)) - Real.exp (-x) / Real.exp (-a) + 1) := by
  -- Normalize the logarithmic defect terms first, then identify the affine coefficients with
  -- `sinh (arsinh u)` and `cosh (arsinh u)`.
  let a := Real.arsinh u
  have hsinh_eq : Real.exp a / 2 - Real.exp (-a) / 2 = u := by
    have hsinh' : (Real.exp a - Real.exp (-a)) / 2 = u := by
      have hsinh0 : Real.sinh a = u := by
        simpa [a] using Real.sinh_arsinh u
      rw [Real.sinh_eq] at hsinh0
      exact hsinh0
    linarith
  have hcosh_eq : Real.exp a / 2 + Real.exp (-a) / 2 = Real.sqrt (1 + u ^ 2) := by
    have hcosh' : (Real.exp a + Real.exp (-a)) / 2 = Real.sqrt (1 + u ^ 2) := by
      have hcosh0 : Real.cosh a = Real.sqrt (1 + u ^ 2) := by
        simpa [a] using Real.cosh_arsinh u
      rw [Real.cosh_eq] at hcosh0
      exact hcosh0
    linarith
  have hcosh_x : Real.exp x / 2 + Real.exp (-x) / 2 = Real.cosh x := by
    have hcosh_x' : (Real.exp x + Real.exp (-x)) / 2 = Real.cosh x := by
      simpa using (Real.cosh_eq x).symm
    linarith
  have hsplit :
      (Real.exp a / 2) *
          (Real.log (Real.exp x / Real.exp a) - Real.exp x / Real.exp a + 1) +
        (Real.exp (-a) / 2) *
          (Real.log (Real.exp (-x) / Real.exp (-a)) - Real.exp (-x) / Real.exp (-a) + 1) =
      u * (x - a) + (Real.sqrt (1 + u ^ 2) - Real.cosh x) := by
    -- The split lemma isolates exactly the affine and `cosh` pieces needed for the final
    -- substitution.
    calc
      (Real.exp a / 2) *
          (Real.log (Real.exp x / Real.exp a) - Real.exp x / Real.exp a + 1) +
        (Real.exp (-a) / 2) *
          (Real.log (Real.exp (-x) / Real.exp (-a)) - Real.exp (-x) / Real.exp (-a) + 1) =
          (Real.exp a / 2 - Real.exp (-a) / 2) * (x - a) +
            ((Real.exp a / 2 + Real.exp (-a) / 2) - (Real.exp x / 2 + Real.exp (-x) / 2)) := by
            simpa [a] using cosh_defect_split_affine_terms u x
      _ = u * (x - a) + (Real.sqrt (1 + u ^ 2) - Real.cosh x) := by
        rw [hsinh_eq, hcosh_eq, hcosh_x]
  -- Substituting the split identity collapses the right-hand side back to `u * x - cosh x`.
  linarith

-- Proof sketch: solve the optimality equation for `ux - cosh x` using the inverse hyperbolic
-- sine, then substitute the maximizer back into the objective.
/-- Example 13.2 (4): clause (iv). The conjugate of `cosh` is
`u ↦ u arsinh(u) - √(u^2 + 1)`. -/
theorem conjugate_cosh (u : ℝ) :
    (cosh.toEReal.asEReal)∗ u =
      ((u * Real.arsinh u - Real.sqrt (u ^ 2 + 1) : ℝ) : EReal) := by
  rw [conjugate_apply_real]
  have hsqrt_comm : Real.sqrt (1 + u ^ 2) = Real.sqrt (u ^ 2 + 1) := by
    rw [add_comm]
  refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
      (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - (cosh.toEReal.asEReal x)))
      (((u * Real.arsinh u - Real.sqrt (u ^ 2 + 1) : ℝ) : EReal)) ?_ ?_
  · intro x
    have hy₁ : 0 < Real.exp x / Real.exp (Real.arsinh u) := by
      exact div_pos (Real.exp_pos x) (Real.exp_pos _)
    have hy₂ : 0 < Real.exp (-x) / Real.exp (-Real.arsinh u) := by
      exact div_pos (Real.exp_pos (-x)) (Real.exp_pos _)
    change (((u * x : ℝ) : EReal) - (cosh.toEReal.asEReal x)) ≤
        (((u * Real.arsinh u - Real.sqrt (u ^ 2 + 1) : ℝ) : EReal))
    rw [show ((cosh.toEReal.asEReal x) : EReal) = ((Real.cosh x : ℝ) : EReal) by
      simp [Function.asEReal_apply, Function.toEReal_apply]]
    rw [show (((u * x : ℝ) : EReal) - ((Real.cosh x : ℝ) : EReal)) =
        (((u * x - Real.cosh x : ℝ) : EReal)) by
        simp [sub_eq_add_neg, ← EReal.coe_sub]]
    rw [cosh_defect_eq_closed_form_add_log_defects (u := u) (x := x)]
    rw [hsqrt_comm]
    refine EReal.coe_le_coe ?_
    have hdefect₁ :
        (Real.exp (Real.arsinh u) / 2) *
            (Real.log (Real.exp x / Real.exp (Real.arsinh u)) -
              Real.exp x / Real.exp (Real.arsinh u) + 1) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (log_defect_nonpos hy₁)
    have hdefect₂ :
        (Real.exp (-Real.arsinh u) / 2) *
            (Real.log (Real.exp (-x) / Real.exp (-Real.arsinh u)) -
              Real.exp (-x) / Real.exp (-Real.arsinh u) + 1) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (log_defect_nonpos hy₂)
    linarith
  · intro z hz
    refine ⟨Real.arsinh u, ?_⟩
    change z < (((u * Real.arsinh u : ℝ) : EReal) - (cosh.toEReal.asEReal (Real.arsinh u)))
    rw [show ((cosh.toEReal.asEReal (Real.arsinh u)) : EReal) =
        ((Real.cosh (Real.arsinh u) : ℝ) : EReal) by
        simp [Function.asEReal_apply, Function.toEReal_apply]]
    have hvalue :
        (((u * Real.arsinh u : ℝ) : EReal) -
            ((Real.cosh (Real.arsinh u) : ℝ) : EReal)) =
          (((u * Real.arsinh u - Real.sqrt (u ^ 2 + 1) : ℝ) : EReal)) := by
      -- Evaluating the source maximizer `x = arsinh u` makes both normalized logarithmic defects
      -- vanish.
      have hreal :
          u * Real.arsinh u - Real.cosh (Real.arsinh u) =
            u * Real.arsinh u - Real.sqrt (u ^ 2 + 1) := by
        simpa [add_comm] using congrArg (fun t : ℝ ↦ u * Real.arsinh u - t) (Real.cosh_arsinh u)
      simpa [sub_eq_add_neg, ← EReal.coe_sub] using
        congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    exact hz.trans_eq hvalue.symm

-- Proof sketch: maximize `ux - e^x`; for `u > 0` the optimizer is `x = log u`, while `u = 0`
-- gives value `0` in the extended-real convention and `u < 0` yields `+∞`.
/-- Example 13.2 (5): clause (v). The conjugate of `exp` is the negative
Boltzmann--Shannon entropy. -/
theorem conjugate_exp (u : ℝ) :
    (exp.toEReal.asEReal)∗ u = negativeBoltzmannShannonEntropy u := by
  rw [conjugate_apply_real]
  by_cases hu : 0 < u
  · -- On the positive branch, the normalized log defect gives the sharp finite upper bound.
    rw [negativeBoltzmannShannonEntropy, if_pos hu]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - (exp.toEReal.asEReal x)))
        (((u * Real.log u - u : ℝ) : EReal)) ?_ ?_
    · intro x
      have hy : 0 < Real.exp x / u := by
        exact div_pos (Real.exp_pos x) hu
      change (((u * x : ℝ) : EReal) - (exp.toEReal.asEReal x)) ≤
          (((u * Real.log u - u : ℝ) : EReal))
      rw [exp_branch_eval, exp_defect_eq_closed_form_add_error (u := u) (x := x) hu]
      -- The normalized defect is nonpositive, so only the closed form remains.
      have hdefect : u * (Real.log (Real.exp x / u) - Real.exp x / u + 1) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu) (log_defect_nonpos hy)
      exact EReal.coe_le_coe (by linarith)
    · intro z hz
      refine ⟨Real.log u, ?_⟩
      -- The source maximizer `x0 = log u` attains the closed form exactly.
      have hvalue :
          (((u * Real.log u : ℝ) : EReal) - (exp.toEReal.asEReal (Real.log u))) =
            (((u * Real.log u - u : ℝ) : EReal)) := by
        simpa [exp_branch_eval] using exp_maximizer_value hu
      exact hz.trans_eq hvalue.symm
  · by_cases h0 : u = 0
    · -- At the origin, the defect is `-exp x`, whose supremum is `0` via the path `x → -∞`.
      rw [negativeBoltzmannShannonEntropy, if_neg hu, if_pos h0]
      refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
          (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - (exp.toEReal.asEReal x))) 0 ?_ ?_
      · intro x
        have hupper0 : (((0 * x - Real.exp x : ℝ) : EReal)) ≤ 0 := by
          exact EReal.coe_le_coe (by nlinarith [Real.exp_pos x])
        simpa [h0, exp_branch_eval] using hupper0
      · intro z hz
        by_cases hz_bot : z = ⊥
        · refine ⟨0, ?_⟩
          rw [hz_bot]
          simpa using (EReal.bot_lt_coe (-1 : ℝ))
        · have hz_top : z ≠ ⊤ := by
            exact fun h => by simpa [h] using hz
          have hz_real : z.toReal < 0 := EReal.toReal_neg hz hz_bot
          rcases exists_lt_neg_exp_of_real_lower z.toReal hz_real with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          rw [← EReal.coe_toReal hz_top hz_bot]
          simpa [h0, exp_branch_eval] using (EReal.coe_lt_coe_iff.mpr hx)
    · have hu_neg : u < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hu) h0
      -- On the negative branch, the affine term dominates along a path to `-∞`, so the supremum
      -- is `⊤`.
      rw [negativeBoltzmannShannonEntropy, if_neg hu, if_neg h0]
      refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
          (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - (exp.toEReal.asEReal x))) ⊤ ?_ ?_
      · intro x
        exact le_top
      · intro z hz
        by_cases hz_bot : z = ⊥
        · refine ⟨0, ?_⟩
          rw [hz_bot]
          simpa using (EReal.bot_lt_coe (u * 0 - 1 : ℝ))
        · have hz_top : z ≠ ⊤ := lt_top_iff_ne_top.mp hz
          rcases exists_lt_exp_range_of_real_lower hz_top hz_bot
              (exists_affine_minus_exp_gt u z.toReal hu_neg) with ⟨x, hx⟩
          exact ⟨x, by simpa [exp_branch_eval] using hx⟩

-- Proof sketch: optimize `ux - f(x)` on `[0,1]`; the stationarity equation produces the logistic
-- parametrization and the resulting supremum equals `log(1 + e^u)`.
/-- Helper for Example 13 2: on the interior branch `0 < x < 1`, the Fermi--Dirac defect
rewrites as the logistic closed form plus two weighted logarithmic errors. -/
theorem negative_fermi_dirac_defect_eq_closed_form_add_errors
    {u x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    let q := Real.exp u / (1 + Real.exp u)
    u * x - (x * Real.log x + (1 - x) * Real.log (1 - x)) =
      Real.log (1 + Real.exp u) +
        x * Real.log (q / x) +
        (1 - x) * Real.log ((1 - q) / (1 - x)) := by
  let q := Real.exp u / (1 + Real.exp u)
  have hden_pos : 0 < 1 + Real.exp u := by
    positivity
  have hq_pos : 0 < q := by
    -- The logistic maximizer lies strictly inside `(0, 1)`.
    exact div_pos (Real.exp_pos u) hden_pos
  have h1x_pos : 0 < 1 - x := by
    linarith
  have h1q_eq : 1 - q = 1 / (1 + Real.exp u) := by
    -- The complementary weight has the expected reciprocal form.
    dsimp [q]
    field_simp [hden_pos.ne']
    ring
  have h1q_pos : 0 < 1 - q := by
    rw [h1q_eq]
    exact one_div_pos.mpr hden_pos
  have hlog_q : Real.log q = u - Real.log (1 + Real.exp u) := by
    -- Split the logarithm of the logistic weight into `u` minus the partition function.
    dsimp [q]
    rw [Real.log_div (Real.exp_ne_zero u) hden_pos.ne']
    simp
  have hlog_one_sub_q : Real.log (1 - q) = -Real.log (1 + Real.exp u) := by
    -- The complementary logarithm is the negated partition-function logarithm.
    rw [h1q_eq, Real.log_div one_ne_zero hden_pos.ne', Real.log_one]
    ring
  -- Expanding both logarithmic quotients reduces the identity to elementary ring arithmetic.
  dsimp [q]
  rw [Real.log_div hq_pos.ne' hx0.ne', Real.log_div h1q_pos.ne' h1x_pos.ne',
    hlog_q, hlog_one_sub_q]
  ring

/-- Example 13.2 (6): clause (vi), first part. The conjugate of the negative Fermi--Dirac entropy
is `u ↦ log(1 + e^u)`. -/
theorem conjugate_negativeFermiDiracEntropy (u : ℝ) :
    negativeFermiDiracEntropy∗ u = (Real.log (1 + Real.exp u) : EReal) := by
  let q := Real.exp u / (1 + Real.exp u)
  have hden_pos : 0 < 1 + Real.exp u := by
    positivity
  have hq_pos : 0 < q := by
    exact div_pos (Real.exp_pos u) hden_pos
  have hq_lt_one : q < 1 := by
    dsimp [q]
    have hexp_pos : 0 < Real.exp u := Real.exp_pos u
    field_simp [hden_pos.ne']
    linarith
  have h_one_sub_q_pos : 0 < 1 - q := by
    linarith
  rw [conjugate_apply_real]
  refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
      (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - negativeFermiDiracEntropy x))
      ((Real.log (1 + Real.exp u) : ℝ) : EReal) ?_ ?_
  · intro x
    by_cases hx : 0 < x ∧ x < 1
    · have hx0 : 0 < x := hx.1
      have hx1 : x < 1 := hx.2
      have h1x_pos : 0 < 1 - x := by
        linarith
      have hr_pos : 0 < q / x := div_pos hq_pos hx0
      have hs_pos : 0 < (1 - q) / (1 - x) := div_pos h_one_sub_q_pos h1x_pos
      have hcancel_eq :
          x * (q / x - 1) + (1 - x) * ((1 - q) / (1 - x) - 1) = 0 := by
        field_simp [hx0.ne', h1x_pos.ne']
        ring
      have herrors_nonpos :
          x * Real.log (q / x) + (1 - x) * Real.log ((1 - q) / (1 - x)) ≤ 0 := by
        exact weighted_log_le_of_affine_cancel
          (le_of_lt hx0) (le_of_lt h1x_pos) hr_pos hs_pos (by simpa [hcancel_eq])
      change (((u * x : ℝ) : EReal) - negativeFermiDiracEntropy x) ≤
          (((Real.log (1 + Real.exp u) : ℝ) : EReal))
      rw [negative_fermi_dirac_branch_eval (u := u) (x := x) hx]
      rw [negative_fermi_dirac_defect_eq_closed_form_add_errors (u := u) (x := x) hx0 hx1]
      dsimp [q] at herrors_nonpos ⊢
      exact EReal.coe_le_coe (by linarith)
    · by_cases hx01 : x = 0 ∨ x = 1
      · rcases hx01 with rfl | rfl
        · -- The endpoint `x = 0` contributes the value `0`, which is below the partition term.
          change (((u * (0 : ℝ) : ℝ) : EReal) - negativeFermiDiracEntropy (0 : ℝ)) ≤
              (((Real.log (1 + Real.exp u) : ℝ) : EReal))
          have hlog_nonneg : 0 ≤ Real.log (1 + Real.exp u) := by
            have hexp_pos : 0 < Real.exp u := Real.exp_pos u
            have hle_one : (1 : ℝ) ≤ 1 + Real.exp u := by
              linarith
            exact Real.log_nonneg hle_one
          simpa [negativeFermiDiracEntropy] using (EReal.coe_le_coe hlog_nonneg)
        · -- The endpoint `x = 1` contributes the affine value `u`, which is still below
          -- `log (1 + exp u)`.
          change (((u * (1 : ℝ) : ℝ) : EReal) - negativeFermiDiracEntropy (1 : ℝ)) ≤
              (((Real.log (1 + Real.exp u) : ℝ) : EReal))
          have hle : u ≤ Real.log (1 + Real.exp u) := by
            rw [Real.le_log_iff_exp_le hden_pos]
            have : Real.exp u ≤ 1 + Real.exp u := by
              linarith [Real.exp_pos u]
            simpa using this
          simpa [negativeFermiDiracEntropy] using (EReal.coe_le_coe hle)
      · -- Outside `[0, 1]`, the entropy is `⊤`, so the defect is `⊥`.
        simpa [negativeFermiDiracEntropy, hx, hx01]
  · intro z hz
    refine ⟨q, ?_⟩
    have hq_mem : 0 < q ∧ q < 1 := ⟨hq_pos, hq_lt_one⟩
    change z < (((u * q : ℝ) : EReal) - negativeFermiDiracEntropy q)
    have hratio₁ : q / q = 1 := by
      field_simp [hq_pos.ne']
    have hratio₂ : (1 - q) / (1 - q) = 1 := by
      field_simp [h_one_sub_q_pos.ne']
    have hreal :
        u * q - (q * Real.log q + (1 - q) * Real.log (1 - q)) =
          Real.log (1 + Real.exp u) := by
      -- At the logistic maximizer, both normalized logarithmic errors are exactly zero.
      simpa [q, hratio₁, hratio₂, Real.log_one] using
        negative_fermi_dirac_defect_eq_closed_form_add_errors (u := u) (x := q) hq_pos hq_lt_one
    have hvalue :
        (((u * q : ℝ) : EReal) - negativeFermiDiracEntropy q) =
          (((Real.log (1 + Real.exp u) : ℝ) : EReal)) := by
      rw [negative_fermi_dirac_branch_eval (u := u) (x := q) hq_mem]
      simpa [sub_eq_add_neg, ← EReal.coe_sub] using
        congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    exact hz.trans_eq hvalue.symm

-- Proof sketch: reflect the explicit formula from the previous clause by sending `u` to `-u`;
-- the resulting expression is exactly the logistic loss.
/-- Example 13.2 (7): clause (vi), second part. The reflected conjugate `f^{*∨}` of the negative
Fermi--Dirac entropy is the logistic loss. -/
theorem conjugate_negativeFermiDiracEntropy_reflection :
    (negativeFermiDiracEntropy∗)ᵛ = logisticLoss := by
  -- Evaluate the reflection pointwise and insert the explicit conjugate formula from clause (vi).
  funext u
  rw [ERealFunction.reverse_apply, conjugate_negativeFermiDiracEntropy]
  -- The reflected closed form is exactly the definition of `logisticLoss`.
  simp [logisticLoss]

-- Proof sketch: maximize `ux - [x log x - (x + 1) log (x + 1)]` on `[0,+∞)`; the optimizer
-- satisfies `e^u = x / (x + 1)`, which is possible exactly for `u < 0`.
/-- Helper for Example 13 2: on the positive branch of the Bose--Einstein entropy, the scalar
defect rewrites as the closed form plus a weighted logarithmic error pair. -/
theorem bose_einstein_defect_eq_closed_form_add_errors
    {u x : ℝ} (hu : u < 0) (hx : 0 < x) :
    let q := Real.exp u
    u * x - (x * Real.log x - (x + 1) * Real.log (x + 1)) =
      -Real.log (1 - q) + x * Real.log (q * (x + 1) / x) + Real.log ((1 - q) * (x + 1)) := by
  let q := Real.exp u
  have hq_pos : 0 < q := by
    simpa [q] using Real.exp_pos u
  have hq_lt_one : q < 1 := by
    simpa [q] using Real.exp_lt_one_iff.mpr hu
  have h1q_pos : 0 < 1 - q := by
    linarith
  have hx1_pos : 0 < x + 1 := by
    linarith
  have hlog_q : Real.log q = u := by
    simpa [q] using Real.log_exp u
  -- Expand the logarithms of the normalized factors and collect the affine terms.
  dsimp [q]
  rw [Real.log_div (mul_ne_zero hq_pos.ne' (show x + 1 ≠ 0 by linarith)) hx.ne',
    Real.log_mul hq_pos.ne' (show x + 1 ≠ 0 by linarith),
    Real.log_mul h1q_pos.ne' (show x + 1 ≠ 0 by linarith), hlog_q]
  ring

/-- Example 13.2 (8): clause (vii). The conjugate of the Bose--Einstein entropy is
`u ↦ -log(1 - e^u)` on `(-∞,0)` and `+∞` on `[0,+∞)`. -/
theorem conjugate_boseEinsteinEntropy (u : ℝ) :
    boseEinsteinEntropy∗ u =
      if u < 0 then ((-Real.log (1 - Real.exp u) : ℝ) : EReal) else ⊤ := by
  by_cases hu : u < 0
  · let q := Real.exp u
    have hq_pos : 0 < q := by
      simpa [q] using Real.exp_pos u
    have hq_lt_one : q < 1 := by
      simpa [q] using Real.exp_lt_one_iff.mpr hu
    have h1q_pos : 0 < 1 - q := by
      linarith
    rw [conjugate_apply_real, if_pos hu]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - boseEinsteinEntropy x))
        (((-Real.log (1 - Real.exp u) : ℝ) : EReal)) ?_ ?_
    · intro x
      by_cases hx : 0 < x
      · have hx1_pos : 0 < x + 1 := by
          linarith
        have hr_pos : 0 < q * (x + 1) / x := by
          exact div_pos (mul_pos hq_pos hx1_pos) hx
        have hs_pos : 0 < (1 - q) * (x + 1) := by
          exact mul_pos h1q_pos hx1_pos
        have hcancel_eq :
            x * (q * (x + 1) / x - 1) + 1 * ((1 - q) * (x + 1) - 1) = 0 := by
          field_simp [hx.ne']
          ring
        have hcancel_le :
            x * (q * (x + 1) / x - 1) + 1 * ((1 - q) * (x + 1) - 1) ≤ 0 := by
          rw [hcancel_eq]
        have herrors_nonpos :
            x * Real.log (q * (x + 1) / x) + Real.log ((1 - q) * (x + 1)) ≤ 0 := by
          simpa using weighted_log_le_of_affine_cancel
            (le_of_lt hx) zero_le_one hr_pos hs_pos hcancel_le
        change (((u * x : ℝ) : EReal) - boseEinsteinEntropy x) ≤
            (((-Real.log (1 - Real.exp u) : ℝ) : EReal))
        rw [bose_einstein_branch_eval (u := u) (x := x) hx]
        rw [bose_einstein_defect_eq_closed_form_add_errors (u := u) (x := x) hu hx]
        exact EReal.coe_le_coe (by
          dsimp [q] at herrors_nonpos
          linarith)
      · by_cases hx0 : x = 0
        · -- The endpoint `x = 0` yields `0`, which is bounded by the finite closed form because
          -- `0 < 1 - exp u ≤ 1`.
          subst hx0
          change (((u * (0 : ℝ) : ℝ) : EReal) - boseEinsteinEntropy (0 : ℝ)) ≤
              (((-Real.log (1 - Real.exp u) : ℝ) : EReal))
          have h1q_le_one : 1 - Real.exp u ≤ 1 := by
            have : 0 ≤ Real.exp u := le_of_lt (Real.exp_pos u)
            linarith
          have hlog_nonpos : Real.log (1 - Real.exp u) ≤ 0 := by
            exact Real.log_nonpos h1q_pos.le h1q_le_one
          have hnonneg : (0 : ℝ) ≤ -Real.log (1 - Real.exp u) := by
            linarith
          simpa [boseEinsteinEntropy] using (EReal.coe_le_coe hnonneg)
        · -- On `(-∞, 0)`, the entropy is `⊤`, so the defect is `⊥`.
          have hxneg : ¬0 < x := hx
          have hx_lt : x < 0 := lt_of_le_of_ne (le_of_not_gt hxneg) hx0
          simpa [boseEinsteinEntropy, hxneg, hx0, hx_lt.ne]
    · intro z hz
      let x0 : ℝ := q / (1 - q)
      have hx0_pos : 0 < x0 := by
        exact div_pos hq_pos h1q_pos
      refine ⟨x0, ?_⟩
      change z < (((u * x0 : ℝ) : EReal) - boseEinsteinEntropy x0)
      have hratio : q * (x0 + 1) / x0 = 1 := by
        dsimp [x0]
        field_simp [hq_pos.ne', h1q_pos.ne']
        ring
      have hprod : (1 - q) * (x0 + 1) = 1 := by
        dsimp [x0]
        field_simp [h1q_pos.ne']
        ring
      have hreal :
          u * x0 - (x0 * Real.log x0 - (x0 + 1) * Real.log (x0 + 1)) =
            -Real.log (1 - Real.exp u) := by
        -- At the source maximizer `q / (1 - q)`, both normalized logarithmic errors vanish.
        simpa [q, hratio, hprod, Real.log_one] using
          bose_einstein_defect_eq_closed_form_add_errors (u := u) (x := x0) hu hx0_pos
      have hvalue :
          (((u * x0 : ℝ) : EReal) - boseEinsteinEntropy x0) =
            (((-Real.log (1 - Real.exp u) : ℝ) : EReal)) := by
        rw [bose_einstein_branch_eval (u := u) (x := x0) hx0_pos]
        simpa [sub_eq_add_neg, ← EReal.coe_sub] using
          congrArg (fun t : ℝ ↦ (t : EReal)) hreal
      exact hz.trans_eq hvalue.symm
  · have hu_nonneg : 0 ≤ u := le_of_not_gt hu
    rw [conjugate_apply_real, if_neg hu]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦ (((u * x : ℝ) : EReal) - boseEinsteinEntropy x)) ⊤ ?_ ?_
    · intro x
      exact le_top
    · intro z hz
      by_cases hz_bot : z = ⊥
      · refine ⟨1, ?_⟩
        rw [hz_bot]
        change ⊥ < (((u * (1 : ℝ) : ℝ) : EReal) - boseEinsteinEntropy (1 : ℝ))
        have hvalue :
            (((u * (1 : ℝ) : ℝ) : EReal) - boseEinsteinEntropy (1 : ℝ)) =
              (((u - (1 * Real.log 1 - (1 + 1) * Real.log (1 + 1)) : ℝ) : EReal)) := by
          simpa using bose_einstein_branch_eval (u := u) (x := (1 : ℝ)) (by norm_num : 0 < (1 : ℝ))
        rw [hvalue]
        exact EReal.bot_lt_coe _
      · have hz_top : z ≠ ⊤ := lt_top_iff_ne_top.mp hz
        have hreal_lower :
            ∃ x > 0, z.toReal < u * x - (x * Real.log x - (x + 1) * Real.log (x + 1)) := by
          let x : ℝ := Real.exp (z.toReal + 1)
          have hx_pos : 0 < x := by
            dsimp [x]
            exact Real.exp_pos _
          refine ⟨x, hx_pos, ?_⟩
          have hlog_mono : Real.log x ≤ Real.log (x + 1) := by
            exact Real.log_le_log hx_pos (by linarith)
          have hux_nonneg : 0 ≤ u * x := mul_nonneg hu_nonneg (le_of_lt hx_pos)
          have hcore :
              Real.log (x + 1) ≤ u * x - (x * Real.log x - (x + 1) * Real.log (x + 1)) := by
            have hxlog : x * Real.log x ≤ x * Real.log (x + 1) := by
              exact mul_le_mul_of_nonneg_left hlog_mono (le_of_lt hx_pos)
            linarith
          have hlog_gt : z.toReal < Real.log (x + 1) := by
            have hx_lt : x < x + 1 := by linarith
            have htmp : z.toReal + 1 < Real.log (x + 1) := by
              exact (Real.lt_log_iff_exp_lt (by positivity)).2 (by simpa [x] using hx_lt)
            linarith
          exact lt_of_lt_of_le hlog_gt hcore
        rcases hreal_lower with ⟨x, hx, hxlt⟩
        refine ⟨x, ?_⟩
        rw [← EReal.coe_toReal hz_top hz_bot]
        change (((z.toReal : ℝ) : EReal)) < (((u * x : ℝ) : EReal) - boseEinsteinEntropy x)
        rw [bose_einstein_branch_eval (u := u) (x := x) hx]
        exact EReal.coe_lt_coe_iff.mpr hxlt

-- Proof sketch: maximize `ux - √(1 + x^2)`; the optimizer exists exactly for `|u| ≤ 1`, and
-- substituting it gives `-√(1 - u^2)`, while `|u| > 1` leads to `+∞`.
/-- Helper for Example 13 2: moving from the signed affine term `u x` to the absolute-value form
`|u| |x|` is a monotone transport step that preserves the radius term unchanged. -/
theorem sqrt_affine_radius_transport (u x : ℝ) :
    u * x + Real.sqrt (1 - u ^ 2) ≤ |u| * |x| + Real.sqrt (1 - u ^ 2) := by
  -- Replace `u * x` by its absolute value and then identify `|u * x|` with `|u| * |x|`.
  calc
    u * x + Real.sqrt (1 - u ^ 2) ≤ |u * x| + Real.sqrt (1 - u ^ 2) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (le_abs_self (u * x)) (Real.sqrt (1 - u ^ 2))
    _ = |u| * |x| + Real.sqrt (1 - u ^ 2) := by
      rw [abs_mul]

/-- Helper for Example 13 2: once `|u| ≤ 1`, the transported affine-radius expression is bounded
by `√(1 + x^2)` via a single square comparison. -/
theorem abs_mul_add_sqrt_le_sqrt_one_add_sq
    {u x : ℝ} (hu : |u| ≤ 1) :
    |u| * |x| + Real.sqrt (1 - u ^ 2) ≤ Real.sqrt (1 + x ^ 2) := by
  let s := Real.sqrt (1 - u ^ 2)
  have hu_sq_le : u ^ 2 ≤ 1 := by
    have hsqabs : |u| ^ 2 ≤ (1 : ℝ) ^ 2 := by
      exact (sq_le_sq₀ (abs_nonneg u) zero_le_one).2 hu
    simpa [sq_abs] using hsqabs
  have hrad_nonneg : 0 ≤ 1 - u ^ 2 := by
    linarith
  have hs_sq : s ^ 2 = 1 - u ^ 2 := by
    -- The radius term squares back to its radicand under `|u| ≤ 1`.
    dsimp [s]
    rw [Real.sq_sqrt hrad_nonneg]
  have hsq_le : (|u| * |x| + s) ^ 2 ≤ 1 + x ^ 2 := by
    have hcross_nonneg : 0 ≤ (s * |x| - |u|) ^ 2 := sq_nonneg (s * |x| - |u|)
    -- The gap between the two squares is exactly the nonnegative cross-term square.
    nlinarith [hcross_nonneg, hs_sq, sq_abs u, sq_abs x]
  -- The right-hand side is the nonnegative square root of the squared bound above.
  dsimp [s] at hsq_le ⊢
  exact Real.le_sqrt_of_sq_le hsq_le

/-- Helper for Example 13 2: under the source-side constraint `|u| ≤ 1`, the scalar defect of
`x ↦ √(1 + x^2)` is globally bounded by the closed form `-√(1 - u^2)`. -/
theorem sqrt_one_add_sq_defect_le_closed_form
    {u x : ℝ} (hu : |u| ≤ 1) :
    u * x - Real.sqrt (1 + x ^ 2) ≤ -Real.sqrt (1 - u ^ 2) := by
  -- Route correction: split the original mixed transport/square argument into the source-faithful
  -- transport step `u x ≤ |u||x|` and the separate square comparison against `√(1 + x^2)`.
  have htransport :
      u * x + Real.sqrt (1 - u ^ 2) ≤ |u| * |x| + Real.sqrt (1 - u ^ 2) := by
    exact sqrt_affine_radius_transport u x
  have hsquare :
      |u| * |x| + Real.sqrt (1 - u ^ 2) ≤ Real.sqrt (1 + x ^ 2) := by
    exact abs_mul_add_sqrt_le_sqrt_one_add_sq (u := u) (x := x) hu
  have hbound :
      u * x + Real.sqrt (1 - u ^ 2) ≤ Real.sqrt (1 + x ^ 2) := by
    exact htransport.trans hsquare
  -- Rearranging the transported bound recovers the desired defect inequality.
  linarith

/-- Helper for Example 13 2: when `|u| < 1`, the stationary point
`u / sqrt (1 - u^2)` attains the closed-form value for the `sqrt (1 + x^2)` defect. -/
theorem sqrt_one_add_sq_stationary_value
    {u : ℝ} (hu : |u| < 1) :
    let x0 := u / Real.sqrt (1 - u ^ 2)
    u * x0 - Real.sqrt (1 + x0 ^ 2) = -Real.sqrt (1 - u ^ 2) := by
  let x0 := u / Real.sqrt (1 - u ^ 2)
  have hu_sq_lt_abs : |u| ^ 2 < 1 := by
    nlinarith [abs_nonneg u, hu]
  have hu_sq_lt : u ^ 2 < 1 := by
    simpa [sq_abs] using hu_sq_lt_abs
  have hrad_pos : 0 < 1 - u ^ 2 := by
    linarith
  have hsqrt_pos : 0 < Real.sqrt (1 - u ^ 2) := by
    exact Real.sqrt_pos.mpr hrad_pos
  have hsqrt_sq : (Real.sqrt (1 - u ^ 2)) ^ 2 = 1 - u ^ 2 := by
    exact Real.sq_sqrt hrad_pos.le
  have hx0_norm :
      1 + x0 ^ 2 = (1 / Real.sqrt (1 - u ^ 2)) ^ 2 := by
    -- Squaring the stationary parametrization reduces the radicand to a perfect square.
    dsimp [x0]
    field_simp [hsqrt_pos.ne']
    rw [hsqrt_sq]
    ring
  have hsqrt_x0 : Real.sqrt (1 + x0 ^ 2) = 1 / Real.sqrt (1 - u ^ 2) := by
    -- The positive square root of that perfect square is the positive reciprocal.
    rw [hx0_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  -- Substitute the explicit stationary point and simplify the resulting rational expression.
  dsimp [x0]
  rw [hsqrt_x0]
  field_simp [hsqrt_pos.ne']
  rw [hsqrt_sq]
  ring

/-- Helper for Example 13 2: every strict negative lower bound lies below some boundary-path value
`t - sqrt (1 + t^2)` with `t > 0`. -/
theorem exists_sqrt_one_add_sq_boundary_lower
    (r : ℝ) (hr : r < 0) :
    ∃ t > 0, r < t - Real.sqrt (1 + t ^ 2) := by
  by_cases hr_le : r ≤ -1
  · refine ⟨1, by norm_num, ?_⟩
    -- For `r ≤ -1`, the fixed boundary value `1 - sqrt 2` already dominates `r`.
    have hsqrt_two_lt_two : Real.sqrt (2 : ℝ) < 2 := by
      have hsq : (Real.sqrt (2 : ℝ)) ^ 2 < (2 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]
        norm_num
      have hsqrt_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg 2
      nlinarith
    have hbound : (-1 : ℝ) < 1 - Real.sqrt (2 : ℝ) := by
      linarith
    have hr_lt : r < 1 - Real.sqrt (2 : ℝ) := lt_of_le_of_lt hr_le hbound
    have hsqrt_two : (1 - Real.sqrt (2 : ℝ)) = 1 - Real.sqrt (1 + (1 : ℝ) ^ 2) := by
      norm_num
    rw [← hsqrt_two]
    exact hr_lt
  · let y := r / 2
    have hy_neg : y < 0 := by
      dsimp [y]
      linarith
    have hy_gt : -1 < y := by
      dsimp [y]
      linarith
    let t := (1 - y ^ 2) / (-2 * y)
    have hy_ne : y ≠ 0 := ne_of_lt hy_neg
    have hden_pos : 0 < -2 * y := by
      linarith
    have ht_pos : 0 < t := by
      -- The explicit boundary witness is positive because `y ∈ (-1, 0)`.
      have hnum_pos : 0 < 1 - y ^ 2 := by
        nlinarith
      dsimp [t]
      exact div_pos hnum_pos hden_pos
    refine ⟨t, ht_pos, ?_⟩
    have hroot_nonneg : 0 ≤ (1 + y ^ 2) / (-2 * y) := by
      have hnum_pos : 0 < 1 + y ^ 2 := by
        nlinarith [sq_nonneg y]
      exact le_of_lt (div_pos hnum_pos hden_pos)
    have hsquare :
        1 + t ^ 2 = ((1 + y ^ 2) / (-2 * y)) ^ 2 := by
      -- Squaring the explicit parametrization produces a perfect square.
      dsimp [t]
      field_simp [hy_ne]
      ring
    have hsqrt :
        Real.sqrt (1 + t ^ 2) = (1 + y ^ 2) / (-2 * y) := by
      rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hroot_nonneg]
    have hvalue : t - Real.sqrt (1 + t ^ 2) = y := by
      -- The boundary parametrization realizes the value `y`.
      rw [hsqrt]
      dsimp [t]
      field_simp [hy_ne]
      ring
    have hry : r < y := by
      dsimp [y]
      linarith
    exact lt_of_lt_of_eq hry hvalue.symm

/-- Helper for Example 13 2: on the boundary case `|u| = 1`, the signed path
`x = sign(u) * t` turns the scalar defect into the simpler boundary expression
`t - sqrt (1 + t^2)`. -/
theorem signed_boundary_defect_eq_scalar
    (u t : ℝ) (hu : |u| = 1) (ht : 0 < t) :
    u * (Real.sign u * t) - Real.sqrt (1 + (Real.sign u * t) ^ 2) =
      t - Real.sqrt (1 + t ^ 2) := by
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, abs_zero] at hu
    norm_num at hu
  have hsign_mul_eq : u * Real.sign u = |u| := by
    rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
    · simp [Real.sign_of_neg hu_neg, abs_of_neg hu_neg]
    · simp [Real.sign_of_pos hu_pos, abs_of_pos hu_pos]
  have hmul : u * Real.sign u = 1 := by
    calc
      u * Real.sign u = |u| := hsign_mul_eq
      _ = 1 := hu
  have hsign_sq : (Real.sign u) ^ 2 = 1 := by
    obtain hsign | hsign := Real.sign_apply_eq_of_ne_zero u hu0
    · rw [hsign]
      norm_num
    · rw [hsign]
      norm_num
  -- The sign absorbs the sign of `u` in the affine term and squares away in the radius term.
  have hsquare : (Real.sign u * t) ^ 2 = t ^ 2 := by
    calc
      (Real.sign u * t) ^ 2 = (Real.sign u) ^ 2 * t ^ 2 := by ring
      _ = t ^ 2 := by rw [hsign_sq, one_mul]
  calc
    u * (Real.sign u * t) - Real.sqrt (1 + (Real.sign u * t) ^ 2) =
        (u * Real.sign u) * t - Real.sqrt (1 + (Real.sign u * t) ^ 2) := by ring
    _ = t - Real.sqrt (1 + (Real.sign u * t) ^ 2) := by rw [hmul, one_mul]
    _ = t - Real.sqrt (1 + t ^ 2) := by rw [hsquare]

/-- Helper for Example 13 2: when `|u| > 1`, following the signed ray `sign(u) * t` makes
`u x - sqrt (1 + x^2)` exceed every prescribed real level. -/
theorem exists_sqrt_one_add_sq_escape_gt
    (u r : ℝ) (hu : 1 < |u|) :
    ∃ x : ℝ, r < u * x - Real.sqrt (1 + x ^ 2) := by
  let t : ℝ := (|r| + 2) / (|u| - 1)
  have hgap_pos : 0 < |u| - 1 := by
    linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    have hnum_pos : 0 < |r| + 2 := by
      nlinarith [abs_nonneg r]
    exact div_pos hnum_pos hgap_pos
  refine ⟨Real.sign u * t, ?_⟩
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, abs_zero] at hu
    norm_num at hu
  have hsign_mul_eq : u * Real.sign u = |u| := by
    rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
    · simp [Real.sign_of_neg hu_neg, abs_of_neg hu_neg]
    · simp [Real.sign_of_pos hu_pos, abs_of_pos hu_pos]
  have hmul_sign : u * (Real.sign u * t) = |u| * t := by
    calc
      u * (Real.sign u * t) = (u * Real.sign u) * t := by ring
      _ = |u| * t := by rw [hsign_mul_eq]
  have hsign_sq : (Real.sign u) ^ 2 = 1 := by
    obtain hsign | hsign := Real.sign_apply_eq_of_ne_zero u hu0
    · rw [hsign]
      norm_num
    · rw [hsign]
      norm_num
  have hsquare : (Real.sign u * t) ^ 2 = t ^ 2 := by
    calc
      (Real.sign u * t) ^ 2 = (Real.sign u) ^ 2 * t ^ 2 := by ring
      _ = t ^ 2 := by rw [hsign_sq, one_mul]
  have hsqrt_le : Real.sqrt (1 + t ^ 2) ≤ t + 1 := by
    -- A single square comparison bounds the radius term by the affine growth along the ray.
    refine Real.sqrt_le_iff.mpr ?_
    constructor
    · linarith
    · nlinarith [sq_nonneg t]
  have hlower :
      (|u| - 1) * t - 1 ≤ u * (Real.sign u * t) - Real.sqrt (1 + (Real.sign u * t) ^ 2) := by
    rw [hmul_sign, hsquare]
    linarith
  have htarget : (|u| - 1) * t - 1 = |r| + 1 := by
    dsimp [t]
    field_simp [hgap_pos.ne']
    ring
  have hr_lt : r < |r| + 1 := by
    nlinarith [le_abs_self r]
  -- The explicit ray point dominates the chosen affine lower bound.
  have hlower' : |r| + 1 ≤ u * (Real.sign u * t) - Real.sqrt (1 + (Real.sign u * t) ^ 2) := by
    simpa [htarget] using hlower
  exact lt_of_lt_of_le hr_lt hlower'

/-- Example 13.2 (9): clause (viii). The conjugate of `x ↦ √(1 + x^2)` is
`u ↦ -√(1 - u^2)` on `[-1,1]` and `+∞` outside that interval. -/
theorem conjugate_sqrtOneAddSq (u : ℝ) :
    ((fun x : ℝ ↦ Real.sqrt (1 + x ^ 2)).toEReal.asEReal)∗ u =
      if |u| ≤ 1 then ((-Real.sqrt (1 - u ^ 2) : ℝ) : EReal) else ⊤ := by
  rw [conjugate_apply_real]
  by_cases hu : |u| ≤ 1
  · rw [if_pos hu]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦
          (((u * x : ℝ) : EReal) -
            (((Real.sqrt (1 + x ^ 2) : ℝ) : EReal))))
        (((-Real.sqrt (1 - u ^ 2) : ℝ) : EReal)) ?_ ?_
    · intro x
      -- The source-side estimate `|u| ≤ 1` gives the global upper bound on every defect value.
      have hreal : u * x - Real.sqrt (1 + x ^ 2) ≤ -Real.sqrt (1 - u ^ 2) := by
        exact sqrt_one_add_sq_defect_le_closed_form (u := u) (x := x) hu
      simpa [sub_eq_add_neg, ← EReal.coe_sub] using (EReal.coe_le_coe hreal)
    · intro z hz
      by_cases hu_strict : |u| < 1
      · let x0 : ℝ := u / Real.sqrt (1 - u ^ 2)
        refine ⟨x0, ?_⟩
        have hreal :
            u * x0 - Real.sqrt (1 + x0 ^ 2) = -Real.sqrt (1 - u ^ 2) := by
          simpa [x0] using sqrt_one_add_sq_stationary_value (u := u) hu_strict
        have hvalue :
            (((u * x0 : ℝ) : EReal) - (((Real.sqrt (1 + x0 ^ 2) : ℝ) : EReal))) =
              (((-Real.sqrt (1 - u ^ 2) : ℝ) : EReal)) := by
          simpa [sub_eq_add_neg, ← EReal.coe_sub] using
            congrArg (fun t : ℝ ↦ (t : EReal)) hreal
        exact hz.trans_eq hvalue.symm
      · have hu_eq : |u| = 1 := le_antisymm hu (le_of_not_gt hu_strict)
        have hrad_zero : 1 - u ^ 2 = 0 := by
          nlinarith [sq_abs u, hu_eq]
        have htarget_zero :
            (((-Real.sqrt (1 - u ^ 2) : ℝ) : EReal)) = 0 := by
          simp [hrad_zero]
        rw [htarget_zero] at hz
        by_cases hz_bot : z = ⊥
        · refine ⟨0, ?_⟩
          rw [hz_bot]
          simpa using (EReal.bot_lt_coe (-1 : ℝ))
        · have hz_top : z ≠ ⊤ := by
            intro hz_top
            simpa [hz_top] using hz
          have hz_real : z.toReal < 0 := EReal.toReal_neg hz hz_bot
          rcases exists_sqrt_one_add_sq_boundary_lower z.toReal hz_real with ⟨t, ht, hlt⟩
          refine ⟨Real.sign u * t, ?_⟩
          rw [← EReal.coe_toReal hz_top hz_bot]
          have hreal :
              u * (Real.sign u * t) - Real.sqrt (1 + (Real.sign u * t) ^ 2) =
                t - Real.sqrt (1 + t ^ 2) := by
            exact signed_boundary_defect_eq_scalar u t hu_eq ht
          simpa [sub_eq_add_neg, ← EReal.coe_sub] using
            (EReal.coe_lt_coe_iff.mpr (lt_of_lt_of_eq hlt hreal.symm))
  · rw [if_neg hu]
    refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
        (fun x : ℝ ↦
          (((u * x : ℝ) : EReal) -
            (((Real.sqrt (1 + x ^ 2) : ℝ) : EReal)))) ⊤ ?_ ?_
    · intro x
      exact le_top
    · intro z hz
      by_cases hz_bot : z = ⊥
      · refine ⟨0, ?_⟩
        rw [hz_bot]
        simpa using (EReal.bot_lt_coe (-1 : ℝ))
      · have hz_top : z ≠ ⊤ := lt_top_iff_ne_top.mp hz
        have hu_gt : 1 < |u| := lt_of_not_ge hu
        rcases exists_sqrt_one_add_sq_escape_gt u z.toReal hu_gt with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [← EReal.coe_toReal hz_top hz_bot]
        simpa [sub_eq_add_neg, ← EReal.coe_sub] using (EReal.coe_lt_coe_iff.mpr hx)

end

end ERealFunction
