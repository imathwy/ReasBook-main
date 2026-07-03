

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_42 (from Chap07) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace

universe u v

/-
Definition 7.42 lies in the chapter's finite max-inner / log-sum-exp smoothing domain.

Sampled owner-style declarations:
- `η` and `eta_apply` in `Chap06/Proposition_6_23` / `Definition_6_27`, the chapter owner for the
  positive-parameter log-sum-exp potential on a finite score family;
- `logSumExpAbsoluteValueSmoothing` in `Chap06/Definition_6_22`, the nearby chapter owner pattern
  for nonempty finite-family log-sum-exp smoothings;
- `ConvexBody.supportFunctionReal` in `Chap07/Definition_7_24`, an intrinsic Chapter 7 owner that
  replaces a concrete `ℝⁿ` model by a real inner-product space parameter;
- `smoothMaxInnerApproximation_hessian_quadratic_form_le` in `Chap07/Proposition_7_21`, the
  direct downstream theorem using the owner introduced here.

Best owner abstraction:
- source-facing: `smoothMaxInnerApproximation`, since Definition 7.42 introduces the smoothing of
  `x ↦ max_i ⟪a_i, x⟫`;
- core/canonical: the Chapter 6 positive-parameter log-sum-exp owner `η`;
- bridge/view: the score vector `WithLp.toLp 2 (fun i ↦ ⟪a i, x⟫)`.

Primitive data:
- a nonempty finite index type `ι`;
- a family `a : ι → E`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the source-facing smoothing function itself;
- the bridge theorem `smoothMaxInnerApproximation_apply`, obtained by evaluating `η` on the score
  vector `i ↦ ⟪a i, x⟫`.

Source/core/bridge triage:
- source-facing: Definition 7.42's smoothing of the finite max-inner objective;
- core/canonical: `η`;
- bridge/view: the evaluation of `η` on the inner-product score vector.

This file stays at the source-facing layer. The previous version hard-coded the concrete ambient
model `EuclideanSpace ℝ (Fin n)` and the family index `Fin m`; the refined owner keeps the same
mathematical formula but moves to the intrinsic real inner-product / finite-family layer and
exposes Definition 7.42 as a thin specialization of the Chapter 6 owner `η`.
-/

variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 7.42: for vectors `aᵢ ∈ E` in a real inner-product space `E` and a positive
parameter `μ`, the smooth approximation of `x ↦ max_i ⟪aᵢ, x⟫` is the Chapter 6 log-sum-exp owner
`η` applied to the score vector `i ↦ ⟪aᵢ, x⟫`, i.e.
`x ↦ μ log (∑ i, exp (⟪aᵢ, x⟫ / μ))`, for a nonempty finite family indexed by `ι`. -/
def smoothMaxInnerApproximation (a : ι → E) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  fun x ↦ η μ (WithLp.toLp 2 fun i ↦ ⟪a i, x⟫)

-- Proof sketch: unfold `smoothMaxInnerApproximation`; this is the defining specialization of the
-- Chapter 6 owner `η` to the score family `i ↦ ⟪a i, x⟫`.
/-- Unfolding `smoothMaxInnerApproximation` gives the Chapter 6 log-sum-exp owner `η` applied to
the score family `i ↦ ⟪a i, x⟫`. -/
@[simp] theorem smoothMaxInnerApproximation_def
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) :
    smoothMaxInnerApproximation a μ =
      fun x ↦ η μ (WithLp.toLp 2 fun i ↦ ⟪a i, x⟫) := sorry

omit [Nonempty ι] in
-- Proof sketch: evaluate `smoothMaxInnerApproximation_def` at `x`, then rewrite the resulting
-- `η` term with `eta_apply`.
/-- Evaluating `smoothMaxInnerApproximation a μ` at `x` gives the defining log-sum-exp formula
`μ log (∑ i exp (⟪aᵢ, x⟫ / μ))`. -/
@[simp] theorem smoothMaxInnerApproximation_apply
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    smoothMaxInnerApproximation a μ x =
      (μ : ℝ) * Real.log (∑ i : ι, Real.exp (⟪a i, x⟫ / (μ : ℝ))) := sorry

-- Proof sketch: apply function extensionality and use
-- `smoothMaxInnerApproximation_apply` pointwise.
/-- The smoothing map `smoothMaxInnerApproximation a μ` is exactly the textbook log-sum-exp
function `x ↦ μ log (∑ i exp (⟪aᵢ, x⟫ / μ))`. -/
theorem smoothMaxInnerApproximation_eq_logSumExp
    (a : ι → E) (μ : {μ : ℝ // 0 < μ}) :
    smoothMaxInnerApproximation a μ =
      fun x ↦ (μ : ℝ) * Real.log (∑ i : ι, Real.exp (⟪a i, x⟫ / (μ : ℝ))) := sorry

end

/-! ### Proposition_7_42 (from Chap07) -/
noncomputable section

/- Proposition 7.42 lies in Chapter 7's absolute-accuracy / scalar iteration-bound domain.

Mandatory domain-style sampling before refinement:
- `quasi_newton_absolute_accuracy_iteration_bound` and
  `quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form` in `Proposition_7_41`, the
  upstream owner and closed-form bridge for the finite-dimensional threshold `T_n(ε)`;
- `relativeScaleIterationBound`, `relativeScaleUniformIterationBound`, and
  `relativeScaleIterationBound_lt_uniformBound` in `Proposition_7_40`, the sibling owner pattern
  for a logarithmic finite-dimensional bound and its dimension-free comparison;
- `mixedAccuracyIterationCountBound`, `mixedAccuracyUniformIterationCountBound`, and
  `mixedAccuracyIterationCountBound_lt_uniformUpperBound` in `Proposition_7_38`, the same Chapter
  7 comparison pattern in the mixed-accuracy lane.

Best owner abstraction:
- source-facing: Proposition 7.42's strict comparison between the finite-dimensional absolute-
  accuracy threshold `T_n(ε)` and its dimension-free comparison bound;
- core/canonical: the upstream owner `quasi_newton_absolute_accuracy_iteration_bound`;
- bridge/view: the closed-form expansion
  `quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form`.

Primitive data:
- the positive dimension `n : ℕ+`;
- the constants `L`, `R`, and `ε`.

Derived API:
- the new dimension-free comparison owner below;
- its expansion theorem;
- the strict comparison theorem obtained from `log (1 + x) < x`.

This refinement deletes the duplicate local finite-dimensional closed-form owner. The finite side
of Proposition 7.42 now reuses the Chapter 7 owner from `Proposition_7_41`, while this file owns
only the genuinely new dimension-free comparison quantity and the strict inequality relating the
two bounds.
-/

/-- The dimension-free comparison bound
`T_∞(ε) = (1 / 2) (1 + 2 L R / ε)^2` for the absolute-accuracy iteration threshold. -/
abbrev quasi_newton_absolute_accuracy_uniform_iteration_bound
    (L R ε : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + 2 * L * R / ε) ^ 2

-- Proof sketch: unfold `quasi_newton_absolute_accuracy_uniform_iteration_bound`.
/-- Expanding `quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε` recovers the formula
`(1 / 2) (1 + 2 L R / ε)^2`. -/
theorem quasi_newton_absolute_accuracy_uniform_iteration_bound_def
    (L R ε : ℝ) :
    quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε =
      (1 / 2 : ℝ) * (1 + 2 * L * R / ε) ^ 2 := rfl

-- Proof sketch: split on `L * R = 0`. In the degenerate case the finite-dimensional threshold
-- collapses to `0`, while the dimension-free comparison bound is `1 / 2`. Otherwise use the
-- closed-form bridge from `Proposition_7_41`, write `T_n(ε) = n a log (1 + x)` with
-- `a = 1 + 2 L R / ε` and `x = (ε + 2 L R) / (2 n ε) = a / (2 n)`, apply
-- `log (1 + x) < x`, and simplify `n a x = (1 / 2) a²`.
/-- Proposition 7.42: if `ε > 0` and the logarithmic parameter `1 + 2 L R / ε` is positive,
equivalently `ε + 2 L R > 0`, then the finite-dimensional absolute-accuracy iteration threshold
`T_n(ε)` is strictly smaller than the dimension-free comparison bound
`T_∞(ε) = (1 / 2) (1 + 2 L R / ε)^2`. -/
theorem quasi_newton_absolute_accuracy_iteration_bound_lt_uniform_bound
    (n : ℕ+) (L R ε : ℝ)
    (hε : 0 < ε) (hsum : 0 < ε + 2 * L * R) :
    quasi_newton_absolute_accuracy_iteration_bound n ε L R <
      quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε := by
  let a : ℝ := 1 + 2 * L * R / ε
  let x : ℝ := (ε + 2 * L * R) / (2 * (n : ℝ) * ε)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have ha_eq : a = (ε + 2 * L * R) / ε := by
    dsimp [a]
    field_simp [hε.ne']
  have ha : 0 < a := by
    rw [ha_eq]
    exact div_pos hsum hε
  have hx : 0 < x := by
    dsimp [x]
    positivity
  by_cases hLR : L * R = 0
  · have hsum_eq : ε + 2 * L * R = ε := by
      nlinarith
    have hfinite_zero : quasi_newton_absolute_accuracy_iteration_bound n ε L R = 0 := by
      rw [quasi_newton_absolute_accuracy_iteration_bound_def]
      rw [quasi_newton_absolute_accuracy_delta_def]
      simp [hsum_eq, hLR, hε.ne']
    have huniform_half :
        quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε = (1 / 2 : ℝ) := by
      rw [quasi_newton_absolute_accuracy_uniform_iteration_bound_def]
      have htwoLR : 2 * L * R = 0 := by
        nlinarith
      simp [htwoLR]
    rw [hfinite_zero, huniform_half]
    norm_num
  · have hLR_ne : L * R ≠ 0 := hLR
    have hlog : Real.log (1 + x) < x := by
      have hpos : 0 < 1 + x := by linarith
      have hne : 1 + x ≠ (1 : ℝ) := by linarith
      simpa [sub_eq_add_neg] using Real.log_lt_sub_one_of_pos hpos hne
    have hmul :
        (n : ℝ) * a * Real.log (1 + x) <
          (n : ℝ) * a * x := by
      exact mul_lt_mul_of_pos_left hlog (mul_pos hn ha)
    have hx_eq : x = a / (2 * (n : ℝ)) := by
      dsimp [x, a]
      field_simp [hε.ne', hn.ne']
    calc
      quasi_newton_absolute_accuracy_iteration_bound n ε L R
          = (n : ℝ) * a * Real.log (1 + x) := by
              simpa [a, x] using
                quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form n hε hsum hLR_ne
      _ < (n : ℝ) * a * x := hmul
      _ = (n : ℝ) * a * (a / (2 * (n : ℝ))) := by rw [hx_eq]
      _ = (1 / 2 : ℝ) * a ^ 2 := by
            field_simp [hn.ne']
      _ = quasi_newton_absolute_accuracy_uniform_iteration_bound L R ε := by
            simp [quasi_newton_absolute_accuracy_uniform_iteration_bound, a]

end
