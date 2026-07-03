import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_24 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 2.24 lies in the quadratic-regularization domain for unconstrained minimization.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical owner of the
  regularized objective `x ↦ f x + (δ / 2) ‖x - x₀‖²`;
* `quadraticallyRegularizedObjective_apply`, the evaluation formula for that owner;
* `IsMinOn`, the canonical whole-space minimizer predicate;
* `isMinOn_univ_iff`, the bridge from whole-space minimization to the textbook pointwise
  inequality.

Best owner abstraction:
* source-facing/core: `quadraticallyRegularizedObjective f δ x₀`;
* bridge/view: `quadraticallyRegularizedObjective_apply`;
* bridge/view: `IsMinOn (quadraticallyRegularizedObjective f δ x₀) Set.univ xδStar`.

Primitive data:
* the objective `f : E → ℝ`;
* the regularization parameter `δ : ℝ`;
* the center `x₀ : E`.

Derived API:
* the explicit evaluation formula for the regularized objective;
* for a named point `xδStar`, the whole-space minimizing predicate for the regularized objective;
* the equivalent textbook inequality formulation on `Set.univ`.

This item is therefore a recall-style use of the existing owner declarations, not a new local
wrapper around regularized objectives or optimal points. The source-facing entry is the
regularized objective itself; minimizer statements are only companion views once a candidate point
has been specified. -/

section

variable (f : E → ℝ) (δ : ℝ) (x0 : E)

/- Definition 2.24: the regularized function
`f_δ(x) = f(x) + (δ / 2) ‖x - x₀‖²` is the canonical quadratic-regularization owner
`quadraticallyRegularizedObjective f δ x₀`. -/
recall quadraticallyRegularizedObjective

set_option linter.hashCommand false in
#check quadraticallyRegularizedObjective f δ x0

recall quadraticallyRegularizedObjective_apply

example (x : E) :
    quadraticallyRegularizedObjective f δ x0 x =
      f x + (δ / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
  quadraticallyRegularizedObjective_apply f δ x0 x

end

section

variable (f : E → ℝ) (δ : ℝ) (x0 xDeltaStar : E)

recall IsMinOn
recall isMinOn_univ_iff

/- The whole-space optimality statement for the regularized objective is exactly the canonical
`IsMinOn` owner specialized to `Set.univ`. -/
example :
    IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xDeltaStar ↔
      ∀ x : E,
        quadraticallyRegularizedObjective f δ x0 xDeltaStar ≤
          quadraticallyRegularizedObjective f δ x0 x :=
  isMinOn_univ_iff

end

/-! ### Lemma_2_24 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

open scoped RegularizedModelValueRootNotation

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)

local notation "parametricProblem" => problem.toParametricSmoothMinimaxProblem

local notation "modelValue" =>
  problem.regularizedModelValue

local notation "parametricOptimalValue" =>
  fun t ↦ sInf ((parametricProblem t) '' problem.ambientSet)

/-
Primary domain: Chapter 2 parameter updates for the constrained max-type value function and the
associated quadratically regularized local-model values.

Owner abstractions sampled before refining:
- `SmoothFunctionalConstraintsMinimizationProblem` from `Definition_2_44.lean`;
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`;
- `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue` from
  `Definition_2_47.lean`;
- `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValueRoot` from
  `Definition_2_48.lean`;
- the constrained optimal-value bridge theorems in `Remark_2_47_1.lean`;
- the owner secant estimate pattern `ConvexOn.secant_lower_bound_left_shift` from
  `Proposition_2_26.lean`.

Source/core/bridge triage:
- source-facing: the two Lemma 2.24 comparison statements;
- core/canonical:
  the fixed-`t` owner `problem.toParametricSmoothMinimaxProblem t : SmoothMinimaxProblem ...`;
- bridge/view: the explicit `toLagrangianProblem` / component-family presentation.

The best owner abstraction here is therefore `parametricProblem t`, together with its derived
regularized affine-model value. The local notation `modelValue` therefore recalls the owner
declaration `problem.regularizedModelValue`, and the local notation `parametricOptimalValue`
follows the bridge surface already used in `Remark_2_47_1` rather than rebuilding separate
objective/feasible-set wrappers.
Primitive data are only `problem`, the owner update `(xBar, t) ↦ t★[problem; xBar](t)`, and the
scalar comparison hypotheses not already owned upstream. The `μ`- and `L`-model values and the
constrained optimal-value function
`t ↦ sInf ((parametricProblem t) '' problem.ambientSet)` remain derived API, so this file states
the lemma directly in those owner terms instead of keeping a parallel scalar-function parameter or
a wrapper root package.
-/

variable {xBar : E} {tBar κ : ℝ}

/-- Lemma 2.24 (1): if the owner `μ`-model value at `(tBar, xBar)` dominates `(1 - κ)` times the
owner `L`-model value, if the owner constrained value at `tBar` is positive, and if
`τ ↦ modelValue τ xBar μ` is convex and has a root not smaller than `tBar`, then the selected
owner least root lies strictly above the reference parameter `tBar`. -/
-- Proof sketch: use
-- `problem.parametricProblemOptimalValue_le_upperRegularizedModelValue tBar xBar` together with
-- positivity of `parametricOptimalValue tBar` to get positivity of the owner `L`-model value.
-- Combine that with `hcomparison` and `κ < 1` to deduce positivity of the owner `μ`-model
-- value. Then apply `problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar` to see that the
-- selected update is an actual root above `tBar`; equality `t★[problem; xBar](tBar) = tBar`
-- would force `modelValue tBar xBar μ = 0`, contradicting the derived positivity.
theorem referenceParameter_lt_regularizedModelValueRoot
    (hκ : κ < 1)
    (hcomparison : modelValue tBar xBar μ ≥ (1 - κ) * modelValue tBar xBar L)
    (hvalue_pos : 0 < parametricOptimalValue tBar)
    (hmu_convex : ConvexOn ℝ Set.univ (fun τ ↦ modelValue τ xBar μ))
    (hmu_root : ∃ τ : ℝ, tBar ≤ τ ∧ modelValue τ xBar μ = 0) :
    tBar < t★[problem; xBar](tBar) := by
  have hparametric_upper :
      parametricOptimalValue tBar ≤ modelValue tBar xBar L := by
    let p := parametricProblem tBar
    have hupper_nonempty :
        ((quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar) ''
          problem.ambientSet).Nonempty := by
      rcases problem.ambient_nonempty with ⟨x, hx⟩
      exact ⟨_, ⟨x, hx, rfl⟩⟩
    refine le_csInf hupper_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    have hobj_le : sInf (p '' problem.ambientSet) ≤ p x := by
      exact csInf_le p.objective_image_bddBelow ⟨x, hx, rfl⟩
    have hupper :
        p x ≤ quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar x := by
      -- Use the canonical upper quadratic bound for the fixed-`t` max-type owner.
      simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
        SmoothMinimaxProblem.objective] using
        (maxTypeObjective_quadratic_bounds_of_components_mem
          p.components μ L p.components_mem x xBar).2
    simpa
      [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue,
        SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem_feasibleSet,
        p]
      using le_trans hobj_le hupper
  -- First compare the constrained value with the `L`-model value at the reference parameter.
  have hmodelValueL_pos : 0 < modelValue tBar xBar L := by
    exact lt_of_lt_of_le hvalue_pos hparametric_upper
  have hfactor_pos : 0 < 1 - κ := by
    linarith
  -- The source comparison then forces positivity of the `μ`-model value at the same point.
  have hreferenceModel_pos : 0 < modelValue tBar xBar μ := by
    have hscaled_pos : 0 < (1 - κ) * modelValue tBar xBar L := by
      exact mul_pos hfactor_pos hmodelValueL_pos
    exact lt_of_lt_of_le hscaled_pos hcomparison
  -- The selected update is a root above `tBar`; equality would contradict the derived positivity.
  have hroot_mem :=
    problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar hmu_convex hmu_root
  have hroot_ne : tBar ≠ t★[problem; xBar](tBar) := by
    intro hroot_eq
    have hzero_at_tBar : modelValue tBar xBar μ = 0 := by
      exact (congrArg (fun s ↦ modelValue s xBar μ) hroot_eq).trans hroot_mem.2
    exact (ne_of_gt hreferenceModel_pos) hzero_at_tBar
  exact lt_of_le_of_ne hroot_mem.1 hroot_ne

/-- Helper for Lemma 2.24: the quadratically regularized affine model of the fixed-`t` parametric
problem is bounded below on the ambient set when the regularization parameter is positive. -/
private theorem parametric_regularizedAffineApproximation_image_bddBelow
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    BddBelow
      ((quadraticallyRegularizedObjective
          ((parametricProblem t).affineApproximation xBar)
          γ
          xBar) '' problem.ambientSet) := by
  let p := parametricProblem t
  let i0 : Fin (m + 1) := 0
  let g0 : E := gradient (p.components i0) xBar
  let c : ℝ := p.components i0 xBar - ‖g0‖ ^ (2 : ℕ) / (2 * (γ : ℝ))
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hcomponent_le :
      firstOrderTaylorModelAt (p.components i0) xBar x ≤
        p.affineApproximation xBar x := by
    -- One Taylor component is bounded above by the finite maximum defining the affine model.
    rw
      [SmoothMinimaxProblem.affineApproximation,
        maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
    exact Finset.le_sup' (fun j : Fin (m + 1) ↦ firstOrderTaylorModelAt (p.components j) xBar x)
      (by simp)
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
        inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    exact SmoothMinimaxProblem.inner_add_quadratic_lower_bound (γ : ℝ) hγ g0 (x - xBar)
  have hbase_raw :
      p.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
        p.components i0 xBar +
          (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hquad (p.components i0 xBar)
  have hbase :
      c ≤
        p.components i0 xBar +
          inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    -- Normalize the completed-square lower bound before comparing with the affine model.
    calc
      c = p.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) := by
        dsimp [c]
        ring
      _ ≤
          p.components i0 xBar +
            (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := hbase_raw
      _ =
          p.components i0 xBar +
            inner ℝ g0 (x - xBar) +
              ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
                ring
  calc
    c ≤
        p.components i0 xBar +
          inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := hbase
    _ =
        firstOrderTaylorModelAt (p.components i0) xBar x +
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            simp [g0]
    _ ≤
        p.affineApproximation xBar x +
          ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right hcomponent_le (((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ))
    _ =
        quadraticallyRegularizedObjective (p.affineApproximation xBar) γ xBar x := by
          simp [quadraticallyRegularizedObjective_apply]

/-- Helper for Lemma 2.24: the constrained optimal value of the fixed-`t` parametric problem is
bounded above by the `L`-regularized affine model value at `xBar`. -/
private theorem parametricProblemOptimalValue_le_upperRegularizedModelValue
    (t : ℝ) (xBar : E) :
    parametricOptimalValue t ≤ modelValue t xBar L := by
  let p := parametricProblem t
  have hupper_nonempty :
      ((quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar) ''
        problem.ambientSet).Nonempty := by
    rcases problem.ambient_nonempty with ⟨x, hx⟩
    exact ⟨_, ⟨x, hx, rfl⟩⟩
  refine le_csInf hupper_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  have hobj_le : sInf (p '' problem.ambientSet) ≤ p x := by
    exact csInf_le p.objective_image_bddBelow ⟨x, hx, rfl⟩
  have hupper :
      p x ≤ quadraticallyRegularizedObjective (p.affineApproximation xBar) L xBar x := by
    -- Use the canonical upper quadratic bound for the fixed-`t` max-type owner.
    simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
      SmoothMinimaxProblem.objective] using
      (maxTypeObjective_quadratic_bounds_of_components_mem
        p.components μ L p.components_mem x xBar).2
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue,
    SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem_feasibleSet, p]
    using le_trans hobj_le hupper

/-- Helper for Lemma 2.24: the `μ`-regularized affine model value of the fixed-`t` parametric
problem is bounded above by its constrained optimal value. -/
private theorem lowerRegularizedModelValue_le_parametricProblemOptimalValue
    (t : ℝ) (xBar : E) :
    modelValue t xBar μ ≤ parametricOptimalValue t := by
  let p := parametricProblem t
  let i0 : Fin (m + 1) := 0
  have hμ_pos : 0 < μ := by
    exact (mem_S11_iff.mp (p.components_mem i0)).mu_pos
  let γμ : NNRealˣ :=
    Units.mk0 (Real.toNNReal μ) (ne_of_gt (by rwa [Real.toNNReal_pos]))
  have hγμ : (γμ : ℝ) = μ := by
    simp [γμ, Real.toNNReal_of_nonneg hμ_pos.le]
  have hobjective_nonempty : (p '' problem.ambientSet).Nonempty := by
    rcases problem.ambient_nonempty with ⟨x, hx⟩
    exact ⟨p x, ⟨x, hx, rfl⟩⟩
  have hmodel_bdd :
      BddBelow
        ((quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar) ''
          problem.ambientSet) := by
    simpa [hγμ] using
      parametric_regularizedAffineApproximation_image_bddBelow
        (problem := problem) t xBar γμ
  refine le_csInf hobjective_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  have hmodel_le :
      sInf ((quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar) ''
        problem.ambientSet) ≤
        quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar x := by
    exact csInf_le hmodel_bdd ⟨x, hx, rfl⟩
  have hlower :
      quadraticallyRegularizedObjective (p.affineApproximation xBar) μ xBar x ≤ p x := by
    -- Use the canonical lower quadratic bound for the fixed-`t` max-type owner.
    simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
      SmoothMinimaxProblem.objective, ge_iff_le] using
      (maxTypeObjective_quadratic_bounds_of_components_mem
        p.components μ L p.components_mem x xBar).1
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue,
    SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem_feasibleSet, p]
    using le_trans hmodel_le hlower

/-- Helper for Lemma 2.24: a convex scalar function lies above the secant line joining a point to
a later comparison point when evaluated to the left of that point. -/
private theorem convex_secant_lower_bound_left_shift
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {t0 t1 t2 : ℝ}
    (ht0t1 : t0 < t1) (ht1t2 : t1 < t2) :
    f t0 ≥ f t1 + ((t1 - t0) / (t2 - t1)) * (f t1 - f t2) := by
  let Δ : ℝ := t1 - t0
  have hΔ_pos : 0 < Δ := by
    dsimp [Δ]
    exact sub_pos.mpr ht0t1
  have hshift : t1 - Δ = t0 := by
    dsimp [Δ]
    ring
  -- Compare the left secant slope with the right secant slope through `ConvexOn.secant_mono`.
  have hslope :
      (f t1 - f (t1 - Δ)) / Δ ≤ (f t2 - f t1) / (t2 - t1) := by
    have hsecant :=
      hf.secant_mono
        (a := t1)
        (x := t1 - Δ)
        (y := t2)
        (by simp)
        (by simp [hshift])
        (by simp)
        (by linarith)
        ht1t2.ne'
        (by linarith)
    convert hsecant using 1
    ring_nf
  have hstep :
      f t1 - f (t1 - Δ) ≤ ((f t2 - f t1) / (t2 - t1)) * Δ := by
    exact (div_le_iff₀ hΔ_pos).1 hslope
  have hbound :
      f t1 - f (t1 - Δ) ≤ (Δ / (t2 - t1)) * (f t2 - f t1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  -- Rearranging the secant estimate gives the claimed lower bound.
  have hbound' :
      f t1 - f t0 ≤ ((t1 - t0) / (t2 - t1)) * (f t2 - f t1) := by
    simpa [Δ, hshift] using hbound
  linarith

/-- Helper for Lemma 2.24: convexity of the `μ`-model value before the selected root yields the
secant lower estimate used in the source proof, with the denominator weakened from
`t★[problem; xBar](tBar) - tBar` to `t★[problem; xBar](tBar) - t`. -/
private theorem modelValue_secant_lower_before_regularized_root
    {t : ℝ}
    (ht_lt_tBar : t < tBar)
    (hroot_gt : tBar < t★[problem; xBar](tBar))
    (hroot_zero : modelValue (t★[problem; xBar](tBar)) xBar μ = 0)
    (hreferenceModel_nonneg : 0 ≤ modelValue tBar xBar μ)
    (hmu_convex : ConvexOn ℝ Set.univ (fun τ ↦ modelValue τ xBar μ)) :
    modelValue t xBar μ ≥
      modelValue tBar xBar μ +
        ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ := by
  have hstrong_secant :
      modelValue t xBar μ ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) *
            (modelValue tBar xBar μ - modelValue (t★[problem; xBar](tBar)) xBar μ) := by
    simpa using
      convex_secant_lower_bound_left_shift
        (f := fun τ ↦ modelValue τ xBar μ)
        hmu_convex
        ht_lt_tBar
        hroot_gt
  have hsecant_at_zero :
      modelValue t xBar μ ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) * modelValue tBar xBar μ := by
    simpa [hroot_zero] using hstrong_secant
  have hroot_gap_pos : 0 < t★[problem; xBar](tBar) - tBar := by
    linarith
  have hroot_gap_le :
      t★[problem; xBar](tBar) - tBar ≤ t★[problem; xBar](tBar) - t := by
    linarith
  have hcoefficient_le :
      (tBar - t) / (t★[problem; xBar](tBar) - t) ≤
        (tBar - t) / (t★[problem; xBar](tBar) - tBar) := by
    exact div_le_div_of_nonneg_left
      (sub_nonneg.mpr ht_lt_tBar.le)
      hroot_gap_pos
      hroot_gap_le
  -- A larger secant coefficient preserves the bound because the reference value is nonnegative.
  have hscaled_le :
      ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ ≤
        ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) * modelValue tBar xBar μ := by
    exact mul_le_mul_of_nonneg_right hcoefficient_le hreferenceModel_nonneg
  have hweak_rhs_le :
      modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ ≤
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - tBar)) * modelValue tBar xBar μ := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hscaled_le (modelValue tBar xBar μ)
  exact le_trans hweak_rhs_le hsecant_at_zero

/-- Internal helper for Lemma 2.24 (2): once the owner value function satisfies the displayed
secant lower estimate at `t` and the reference `μ`-model value is nonnegative, the owner
`L`-model value at `(t, x)` is bounded below by the same square-root expression as in the source
statement. -/
-- Proof sketch: use
-- `problem.parametricProblemOptimalValue_le_upperRegularizedModelValue t x` to bound
-- `parametricOptimalValue t` above by the owner `L`-model value at `(t, x)`. Combine this with
-- the secant lower estimate for `parametricOptimalValue t`, factor the right-hand side as
-- `(1 + τ) * modelValue tBar xBar μ`, use the assumed nonnegativity of
-- `modelValue tBar xBar μ` together with the elementary inequality
-- `1 + τ ≥ 2 * sqrt τ` for `τ = (tBar - t) / (t★[problem; xBar](tBar) - t)`, and then apply
-- `hcomparison`.
private theorem local_value_lower_bound_of_secant_lower
    {x : E} {t : ℝ}
    (ht_lt_tBar : t < tBar)
    (hroot_gt : tBar < t★[problem; xBar](tBar))
    (hcomparison : modelValue tBar xBar μ ≥ (1 - κ) * modelValue tBar xBar L)
    (hreferenceModel_nonneg : 0 ≤ modelValue tBar xBar μ)
    (hsecant_lower :
      parametricOptimalValue t ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ) :
    modelValue t x L ≥
      2 * (1 - κ) * modelValue tBar xBar L *
        Real.sqrt ((tBar - t) / (t★[problem; xBar](tBar) - t)) := by
  let τ : ℝ := (tBar - t) / (t★[problem; xBar](tBar) - t)
  have hroot_gap_pos : 0 < t★[problem; xBar](tBar) - t := by
    linarith
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    exact div_nonneg (sub_nonneg.mpr ht_lt_tBar.le) hroot_gap_pos.le
  -- The secant estimate and the upper comparison bridge bound the `L`-model from below by
  -- `(1 + τ) * modelValue tBar xBar μ`.
  have hvalue_ge_factor :
      modelValue t x L ≥ (1 + τ) * modelValue tBar xBar μ := by
    calc
      modelValue t x L ≥ parametricOptimalValue t := by
        exact parametricProblemOptimalValue_le_upperRegularizedModelValue
          (problem := problem) t x
      _ ≥ modelValue tBar xBar μ + τ * modelValue tBar xBar μ := by
        simpa [τ] using hsecant_lower
      _ = (1 + τ) * modelValue tBar xBar μ := by
        ring
  -- Replace the factor `1 + τ` by the source lower bound `2 * sqrt τ`.
  have hsqrt_step : 2 * Real.sqrt τ ≤ 1 + τ := by
    have hsquare_nonneg : 0 ≤ (Real.sqrt τ - 1) ^ (2 : ℕ) := by
      exact sq_nonneg (Real.sqrt τ - 1)
    nlinarith [hsquare_nonneg, Real.sq_sqrt hτ_nonneg]
  have hsqrt_factor_le :
      (2 * Real.sqrt τ) * modelValue tBar xBar μ ≤
        (1 + τ) * modelValue tBar xBar μ := by
    exact mul_le_mul_of_nonneg_right hsqrt_step hreferenceModel_nonneg
  have hvalue_ge_sqrt_factor :
      modelValue t x L ≥ (2 * Real.sqrt τ) * modelValue tBar xBar μ := by
    exact le_trans hsqrt_factor_le hvalue_ge_factor
  have htwo_sqrt_nonneg : 0 ≤ 2 * Real.sqrt τ := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
    nlinarith
  -- Finally transport the reference-point comparison through the nonnegative factor `2 * sqrt τ`.
  have hcomparison_scaled :
      (2 * Real.sqrt τ) * ((1 - κ) * modelValue tBar xBar L) ≤
        (2 * Real.sqrt τ) * modelValue tBar xBar μ := by
    exact mul_le_mul_of_nonneg_left hcomparison htwo_sqrt_nonneg
  have hfinal :
      (2 * Real.sqrt τ) * ((1 - κ) * modelValue tBar xBar L) ≤
        modelValue t x L := by
    exact le_trans hcomparison_scaled hvalue_ge_sqrt_factor
  simpa [τ, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- Lemma 2.24 (2): if the owner `μ`-model value at `(tBar, xBar)` dominates `(1 - κ)` times the
owner `L`-model value, if the owner constrained value at `tBar` is positive, if
`τ ↦ modelValue τ xBar μ` is convex and has a root not smaller than `tBar`, and if `t < tBar`,
then for every base point `x ∈ E` the owner `L`-model value at `(t, x)` is bounded below by the
stated square-root expression involving the selected least root `t★[problem; xBar](tBar)`. The
textbook statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: first apply `referenceParameter_lt_regularizedModelValueRoot` to obtain
-- `tBar < t★[problem; xBar](tBar)` and then use
-- `problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar` to identify the secant endpoint
-- as an actual zero of `τ ↦ modelValue τ xBar μ`. The positivity of
-- `parametricOptimalValue tBar` together with
-- `problem.parametricProblemOptimalValue_le_upperRegularizedModelValue tBar xBar` implies
-- positivity of `modelValue tBar xBar L`, and then `hcomparison` yields positivity of
-- `modelValue tBar xBar μ`. Then use the local helper
-- `modelValue_secant_lower_before_regularized_root` to extract the source secant estimate for
-- `τ ↦ modelValue τ xBar μ` between `t`, `tBar`, and `t★[problem; xBar](tBar)`, bound the
-- left-hand side by `parametricOptimalValue t` via
-- `problem.lowerRegularizedModelValue_le_parametricProblemOptimalValue t xBar`, and conclude with
-- the internal secant-lower helper using the derived nonnegativity of `modelValue tBar xBar μ`.
theorem local_value_lower_bound_before_reference_parameter
    {x : E} {t : ℝ}
    (hκ : κ < 1)
    (hcomparison : modelValue tBar xBar μ ≥ (1 - κ) * modelValue tBar xBar L)
    (hvalue_pos : 0 < parametricOptimalValue tBar)
    (hmu_convex : ConvexOn ℝ Set.univ (fun τ ↦ modelValue τ xBar μ))
    (hmu_root : ∃ τ : ℝ, tBar ≤ τ ∧ modelValue τ xBar μ = 0)
    (ht_lt_tBar : t < tBar) :
    modelValue t x L ≥
      2 * (1 - κ) * modelValue tBar xBar L *
        Real.sqrt ((tBar - t) / (t★[problem; xBar](tBar) - t)) := by
  -- First show that the selected root lies strictly to the right of the reference parameter.
  have hroot_gt :=
    referenceParameter_lt_regularizedModelValueRoot
      (problem := problem)
      hκ
      hcomparison
      hvalue_pos
      hmu_convex
      hmu_root
  have hroot_mem :=
    problem.regularizedModelValueRoot_mem_of_convexOn xBar tBar hmu_convex hmu_root
  -- Positivity of the constrained value at `tBar` propagates to both local model values there.
  have hmodelValueL_pos : 0 < modelValue tBar xBar L := by
    exact lt_of_lt_of_le hvalue_pos
      (parametricProblemOptimalValue_le_upperRegularizedModelValue
        (problem := problem) tBar xBar)
  have hfactor_pos : 0 < 1 - κ := by
    linarith
  have hreferenceModel_pos : 0 < modelValue tBar xBar μ := by
    have hscaled_pos : 0 < (1 - κ) * modelValue tBar xBar L := by
      exact mul_pos hfactor_pos hmodelValueL_pos
    exact lt_of_lt_of_le hscaled_pos hcomparison
  -- Convexity of the `μ`-model value gives the secant lower bound before the selected root.
  have hmodel_secant :
      modelValue t xBar μ ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ := by
    exact modelValue_secant_lower_before_regularized_root
      (problem := problem)
      ht_lt_tBar
      hroot_gt
      hroot_mem.2
      hreferenceModel_pos.le
      hmu_convex
  have hparametric_secant :
      parametricOptimalValue t ≥
        modelValue tBar xBar μ +
          ((tBar - t) / (t★[problem; xBar](tBar) - t)) * modelValue tBar xBar μ := by
    exact le_trans hmodel_secant
      (lowerRegularizedModelValue_le_parametricProblemOptimalValue
        (problem := problem) t xBar)
  exact local_value_lower_bound_of_secant_lower
    (problem := problem)
    (x := x)
    ht_lt_tBar
    hroot_gt
    hcomparison
    hreferenceModel_pos.le
    hparametric_secant

end

/-! ### Proposition_2_24 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ)

/-
Primary domain: constrained max-type minimization on a complete real inner-product space for a
fixed parameter `t`.

Owner declarations sampled before refining:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44`, which owns the primitive
  ambient set `Q`, objective `f₀`, and constraint family `fᵢ`;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47`, the bridge to the fixed-`t` owner `SmoothMinimaxProblem`;
* `SmoothMinimaxProblem` in `Definition_2_38`, which owns the feasible set/objective pair for the
  max-type problem;
* `SmoothMinimaxProblem.existsUnique_isMinOn` in `Definition_2_38`, the owner unique-minimizer
  theorem for a fixed-parameter smooth minimax problem.

Best owner abstraction:
* `problem.toParametricSmoothMinimaxProblem t`.

Primitive data:
* the constrained problem `problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L`;
* the scalar parameter `t`.

Derived API:
* the fixed-`t` max-type objective as the coerced objective
  `problem.toParametricSmoothMinimaxProblem t`;
* the feasible set
  `(problem.toParametricSmoothMinimaxProblem t).feasibleSet = problem.ambientSet`;
* the unique-minimizer conclusion stated by `IsMinOn`.

Source/core/bridge triage:
* source-facing: Proposition 2.24's unique minimizer claim for
  `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}` on `Q`;
* core/canonical: the owner fixed-`t` problem `parametricProblem`;
* bridge/view: the explicit
  `problem.toLagrangianProblem.constrainedAuxiliaryObjective t` presentation, which remains a
  companion view but not the main public surface here.

This proposition is exact owner recall: the fixed-`t` textbook max-type problem is the canonical
owner `problem.toParametricSmoothMinimaxProblem t`, and
`toParametricSmoothMinimaxProblem_feasibleSet` identifies its feasible set with
`problem.ambientSet`. This file therefore adds no parallel unique-minimizer theorem shell.
-/

/- Proposition 2.24: for each `t`, the constrained max-type problem is the owner
`problem.toParametricSmoothMinimaxProblem t`, so existence and uniqueness of its feasible
minimizer are given directly by the canonical owner theorem
`SmoothMinimaxProblem.existsUnique_isMinOn`. -/
recall SmoothMinimaxProblem.existsUnique_isMinOn

set_option linter.hashCommand false in
#check (problem.toParametricSmoothMinimaxProblem t).existsUnique_isMinOn

end

/-! ### Theorem_2_24 (from Chap02) -/
open scoped Gradient SmoothConvex MinGradientNormAlongIterates

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

local instance theorem24FiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

/- Primary domain: explicit gradient-norm rates for smooth-convex gradient descent on
finite-dimensional real inner-product spaces.

Owner-style declarations sampled before refining this file:
* `gradientMethod` in `Algorithm_2_1`, the chapter recall of the canonical gradient-method
  trajectory;
* `minGradientNormAlongIterates` and `minGradientNormAlongIterates.exists_eq` in
  `Definition_2_23`, the owner `g_{k,T}` object and its attainment lemma;
* `gradient_step_value_descent_of_lipschitzGradient` in `Lemma_2_16`, the reciprocal-`L`
  one-step descent estimate used on tail windows.

Source/core/bridge triage:
* source-facing: Theorem 2.24's existence of an iterate `i ∈ {0, …, T}` with the explicit
  squared-gradient bound;
* core/canonical: the tail-window minimum
  `g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (x_k); 0, T - k | Nat.zero_le _]`;
* bridge/view: the Chapter 1 tail-window estimate `minGradientNormAlongIterates_le_sqrt`,
  combined with the Chapter 2 objective-gap decay from Theorem 2.15.

Primitive data:
* the smooth-convex owner hypothesis `hf`;
* a minimizer `xStar` with `IsMinOn f Set.univ xStar`;
* the initial point `x0`.

Derived API:
* the minimizer value as the exact infimum of `Set.range f`;
* the stage-`k` objective-gap estimate
  `f(x_k) - f(xStar) ≤ 2 L ‖x0 - xStar‖² / (k + 4)`;
* the tail-window bound for `g_{k,T}`;
* the midpoint-product lower bound used to reach the final constant.

Accordingly, this file keeps the iterate-existence statement as the main public theorem and
implements the source proof directly through the tail-window minimum `g_{k,T}`, rather than by
importing the later Theorem 2.25 bridge. -/

section

variable {L : NNReal} {f : E → ℝ}

namespace ConvexC1SeminormSmooth

/-- Helper for Theorem 2.24: restarting constant-step gradient descent from iterate `k`
reproduces the tail `k + j` of the original trajectory. -/
private theorem gradientMethod_restart_eq_tail
    (f : E → ℝ) (α : ℝ) (x0 : E) (k j : ℕ) :
    gradientMethod (fun _ ↦ α) f (gradientMethod (fun _ ↦ α) f x0 k) j =
      gradientMethod (fun _ ↦ α) f x0 (k + j) := by
  -- Rewrite both trajectories as iterates of the same gradient-step map.
  calc
    gradientMethod (fun _ ↦ α) f (gradientMethod (fun _ ↦ α) f x0 k) j =
        (fun x ↦ x - α • ∇ f x)^[j] (gradientMethod (fun _ ↦ α) f x0 k) := by
          simpa using
            (gradientMethod_const_eq_iterate f α (gradientMethod (fun _ ↦ α) f x0 k) j)
    _ = (fun x ↦ x - α • ∇ f x)^[j] ((fun x ↦ x - α • ∇ f x)^[k] x0) := by
          rw [gradientMethod_const_eq_iterate]
    _ = (fun x ↦ x - α • ∇ f x)^[k + j] x0 := by
          simpa [Nat.add_comm] using
            (Function.iterate_add_apply (fun x ↦ x - α • ∇ f x) j k x0).symm
    _ = gradientMethod (fun _ ↦ α) f x0 (k + j) := by
          symm
          simpa using (gradientMethod_const_eq_iterate f α x0 (k + j))

/-- Helper for Theorem 2.24: a whole-space minimizer realizes the exact infimum of the range of
`f`. -/
private theorem objective_value_isGLB_of_isMinOn
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    IsGLB (Set.range f) (f xStar) := by
  -- Repackage whole-space minimality as the exact infimum of the value set.
  refine ⟨?_, ?_⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact (isMinOn_univ_iff.mp hxStar) z
  · intro b hb
    exact hb ⟨xStar, rfl⟩

/-- Helper for Theorem 2.24: the initial objective gap is bounded by the quadratic tangent-error
upper model at the minimizer. -/
private theorem initial_objective_gap_le_half_lipschitz_sqdist
    (hf : f ∈ 𝓕[L, p]¹¹) (xStar x0 : E)
    (hxStar : IsMinOn f Set.univ xStar) :
    f x0 - f xStar ≤ ((L : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  have hgrad0 : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
  -- Apply the smooth tangent upper bound at the minimizer and remove the vanishing linear term.
  have hupper := (hf.tangentErrorBounds (x := xStar) (y := x0) (by simp) (by simp)).2
  simpa [hgrad0, norm_sub_rev] using hupper

/-- Helper for Theorem 2.24: every stage of gradient descent with stepsize `1 / L` satisfies the
textbook objective-gap estimate `f(x_k) - f(xStar) ≤ 2 L ‖x0 - xStar‖² / (k + 4)` when `L > 0`.
-/
private theorem gradientMethod_objective_gap_le_two_mul_L_sqdist_div_add_four
    (hf : f ∈ 𝓕[L, p]¹¹) (xStar x0 : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hL : 0 < (L : ℝ)) (k : ℕ) :
    f (gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0 k) - f xStar ≤
      (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  let Δ0 : ℝ := f x0 - f xStar
  let R2 : ℝ := ‖x0 - xStar‖ ^ (2 : ℕ)
  by_cases hx0 : x0 = xStar
  · subst x0
    have hgrad0 : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
    have htraj : ∀ n : ℕ, gradientMethod (fun _ ↦ 1 / (L : ℝ)) f xStar n = xStar := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n hn =>
          -- A trajectory started at a minimizer stays fixed because the gradient vanishes there.
          rw [gradientMethod_succ, hn, hgrad0]
          simp
    -- Collapse the stationary trajectory to turn both sides of the estimate into zero.
    have hgap_zero : f (traj k) - f xStar = 0 := by
      exact sub_eq_zero.mpr <| by simpa [traj] using congrArg f (htraj k)
    have hrhs_zero :
        (2 * (L : ℝ) * ‖xStar - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) = 0 := by
      simp
    rw [hgap_zero, hrhs_zero]
  · let A : ℝ := ((L : ℝ) / 2) * R2
    let c : ℝ := (k : ℝ) / (L : ℝ)
    have hΔ0_nonneg : 0 ≤ Δ0 := by
      dsimp [Δ0]
      exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) x0)
    have hR2_pos : 0 < R2 := by
      have hsub_ne : x0 - xStar ≠ 0 := sub_ne_zero.mpr hx0
      have hnorm_pos : 0 < ‖x0 - xStar‖ := norm_pos_iff.mpr hsub_ne
      dsimp [R2]
      positivity
    have hgap0_le : Δ0 ≤ A := by
      -- Source equation `(2.u386)` starts from the standard initial quadratic gap bound.
      simpa [Δ0, R2, A, mul_assoc, mul_left_comm, mul_comm] using
        initial_objective_gap_le_half_lipschitz_sqdist
          (hf := hf) (xStar := xStar) (x0 := x0) hxStar
    have hraw :=
      gradientMethod_objective_gap_le_explicit_rate_of_mem_F11
        (hf := hf) xStar hxStar
        (1 / (L : ℝ)) (by positivity)
        (by
          have htwo : (1 : ℝ) ≤ 2 := by norm_num
          exact div_le_div_of_nonneg_right htwo hL.le)
        x0 k
    have hraw' :
        f (traj k) - f xStar ≤
          (2 * Δ0 * R2) / (2 * R2 + c * Δ0) := by
      -- Specialize Theorem 2.15 to the reciprocal stepsize `h = 1 / L`.
      have hone : 2 - (L : ℝ) * (1 / (L : ℝ)) = 1 := by
        field_simp [ne_of_gt hL]
        norm_num
      have hraw0 := hraw
      rw [hone, mul_one] at hraw0
      simpa [traj, Δ0, R2, c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        add_assoc, add_left_comm, add_comm] using hraw0
    have hmono :
        (2 * Δ0 * R2) / (2 * R2 + c * Δ0) ≤
          (2 * A * R2) / (2 * R2 + c * A) := by
      have hden0_pos : 0 < 2 * R2 + c * Δ0 := by
        positivity
      have hdenA_pos : 0 < 2 * R2 + c * A := by
        positivity
      refine (div_le_div_iff₀ hden0_pos hdenA_pos).2 ?_
      have hgap0_le' : 2 * Δ0 ≤ (L : ℝ) * R2 := by
        dsimp [A] at hgap0_le
        nlinarith
      dsimp [A, c]
      ring_nf
      nlinarith [hgap0_le', hR2_pos.le, hL.le]
    have hA_eval :
        (2 * A * R2) / (2 * R2 + c * A) =
          (2 * (L : ℝ) * R2) / (k + 4 : ℝ) := by
      -- Evaluate the rational expression after inserting the initial-gap upper bound.
      dsimp [A, c]
      field_simp [ne_of_gt hL, ne_of_gt hR2_pos]
      ring_nf
    calc
      f (traj k) - f xStar ≤ (2 * Δ0 * R2) / (2 * R2 + c * Δ0) := hraw'
      _ ≤ (2 * A * R2) / (2 * R2 + c * A) := hmono
      _ = (2 * (L : ℝ) * R2) / (k + 4 : ℝ) := hA_eval
      _ = (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) := by
            simp [R2]

/-- Helper for Theorem 2.24: on every tail window `k, …, T`, the minimum gradient norm satisfies
the explicit source bound obtained by combining the tail sufficient-decrease estimate with the
stage-`k` objective-gap decay. -/
private theorem tail_window_min_gradient_sq_le_explicit_bound
    (hf : f ∈ 𝓕[L, p]¹¹) (xStar x0 : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (hL : 0 < (L : ℝ)) {k T : ℕ} (hkT : k ≤ T) :
    let traj := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
    let tail := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k)
    g[f; tail; 0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) ≤
      (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  let tail : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k)
  have hglb : IsGLB (Set.range f) (f xStar) :=
    objective_value_isGLB_of_isMinOn (f := f) hxStar
  have hdesc :
      ∀ j : ℕ,
        (((1 / 2 : ℝ) / (L : ℝ)) * ‖∇ f (tail j)‖ ^ (2 : ℕ)) ≤
          f (tail j) - f (tail (j + 1)) := by
    intro j
    have hdescent :
        f (tail (j + 1)) ≤
          f (tail j) -
            (1 / (2 * (L : ℝ))) * ‖∇ f (tail j)‖ ^ (2 : ℕ) := by
      -- Lemma 2.16 supplies the sufficient decrease on each tail iterate.
      simpa [tail, gradientMethod_succ] using
        gradient_step_value_descent_of_lipschitzGradient
          f hL
          (fun x ↦ (hf.hasGradientAt x).differentiableAt)
          (by simpa using hf.gradient_lipschitz)
          (tail j)
    have hcoeff :
        (((1 / 2 : ℝ) / (L : ℝ)) * ‖∇ f (tail j)‖ ^ (2 : ℕ)) =
          (1 / (2 * (L : ℝ))) * ‖∇ f (tail j)‖ ^ (2 : ℕ) := by
      field_simp [ne_of_gt hL]
    rw [hcoeff]
    linarith
  have htail_nonneg :
      0 ≤ g[f; tail; 0, T - k | Nat.zero_le (T - k)] := by
    -- The tail-window minimum is attained by a norm value.
    rcases minGradientNormAlongIterates.exists_eq f tail (Nat.zero_le (T - k)) with
      ⟨j, -, -, hj⟩
    rw [hj]
    exact norm_nonneg _
  have hroot :=
    minGradientNormAlongIterates_le_sqrt
      (stepSize := fun _ ↦ 1 / (L : ℝ))
      (x0 := traj k) (f := f) (L := (L : ℝ)) (ω := (1 / 2 : ℝ))
      hglb hL (by norm_num) hdesc (T - k)
  have hgapk_nonneg : 0 ≤ f (traj k) - f xStar := by
    exact sub_nonneg.mpr ((isMinOn_univ_iff.mp hxStar) (traj k))
  have hsq_gap :
      g[f; tail; 0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) ≤
        ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ))) := by
    have hroot' :
        g[f; tail; 0, T - k | Nat.zero_le (T - k)] ≤
          Real.sqrt
            (((L : ℝ) * (f (traj k) - f xStar)) /
              ((1 / 2 : ℝ) * (T - k + 1 : ℝ))) := by
      simpa [tail, Nat.cast_sub hkT] using hroot
    have hinside_nonneg :
        0 ≤ ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ))) := by
      have hden_nonneg : 0 ≤ ((1 / 2 : ℝ) * (T - k + 1 : ℝ)) := by
        have hkT' : (k : ℝ) ≤ T := by
          exact_mod_cast hkT
        nlinarith
      exact div_nonneg (mul_nonneg (by exact_mod_cast L.2) hgapk_nonneg) hden_nonneg
    -- Square the Chapter 1 root estimate to recover the tail-window source bound.
    exact (Real.le_sqrt htail_nonneg hinside_nonneg).1 hroot'
  have hgapk :
      f (traj k) - f xStar ≤
        (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ) :=
    gradientMethod_objective_gap_le_two_mul_L_sqdist_div_add_four
      (hf := hf) (xStar := xStar) (x0 := x0) hxStar hL k
  have hinside_le :
      ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ))) ≤
        (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
    have hden_nonneg : 0 ≤ (T - k + 1 : ℝ) := by
      have hkT' : (k : ℝ) ≤ T := by
        exact_mod_cast hkT
      nlinarith
    -- Insert the stage-`k` gap estimate into the Chapter 1 radicand.
    calc
      ((L : ℝ) * (f (traj k) - f xStar)) / (((1 / 2 : ℝ) * (T - k + 1 : ℝ)))
          = (2 * (L : ℝ) * (f (traj k) - f xStar)) / (T - k + 1 : ℝ) := by
            field_simp
      _ ≤ (2 * (L : ℝ) *
            ((2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / (k + 4 : ℝ))) /
            (T - k + 1 : ℝ) := by
            exact div_le_div_of_nonneg_right (by gcongr) hden_nonneg
      _ = (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
            field_simp
            ring_nf
  exact hsq_gap.trans hinside_le

/-- Helper for Theorem 2.24: the midpoint-like choice `k = (T - 3) / 2` makes the tail-window
product dominate a quarter of `(T + 4) (T + 6)`. -/
private theorem midpoint_window_product_ge_quarter_target
    {T : ℕ} (hT : 3 ≤ T) :
    let k := (T - 3) / 2
    ((T + 4 : ℝ) * (T + 6 : ℝ)) / 4 ≤ (k + 4 : ℝ) * (T - k + 1 : ℝ) := by
  let k : ℕ := (T - 3) / 2
  have hkT : k ≤ T := by
    dsimp [k]
    omega
  let r : ℕ := (T - 3) % 2
  have hr : r = 0 ∨ r = 1 := by
    have hr_lt : r < 2 := by
      dsimp [r]
      exact Nat.mod_lt _ (by decide)
    omega
  have hdecomp : T = 2 * k + r + 3 := by
    dsimp [k, r]
    have hmod := Nat.mod_add_div (T - 3) 2
    omega
  have hnat :
      (T + 4) * (T + 6) ≤ 4 * ((((T - 3) / 2 + 4) * (T - (T - 3) / 2 + 1)) : ℕ) := by
    -- Split on the parity of `T - 3` to evaluate the midpoint choice explicitly.
    rcases hr with hr | hr
    · have hT0 : T = 2 * k + 3 := by
        rw [hr] at hdecomp
        simpa using hdecomp
      rw [hT0]
      have hkdiv0 : (2 * k + 3 - 3) / 2 = k := by
        omega
      have hright0 : 2 * k + 3 - k + 1 = k + 4 := by
        omega
      rw [hkdiv0]
      rw [hright0]
      zify
      nlinarith
    · have hT1 : T = 2 * k + 4 := by
        rw [hr] at hdecomp
        simpa using hdecomp
      rw [hT1]
      have hkdiv1 : (2 * k + 4 - 3) / 2 = k := by
        omega
      have hright1 : 2 * k + 4 - k + 1 = k + 5 := by
        omega
      rw [hkdiv1]
      rw [hright1]
      zify
      nlinarith
  have hnat' :
      (T + 4) * (T + 6) ≤ 4 * ((k + 4) * (T - k + 1)) := by
    simpa [k] using hnat
  have hcast :
      ((T + 4 : ℝ) * (T + 6 : ℝ)) ≤
        4 * ((k + 4 : ℝ) * (((T - k + 1 : ℕ) : ℝ))) := by
    exact_mod_cast hnat'
  have hcast' :
      ((T + 4 : ℝ) * (T + 6 : ℝ)) ≤
        4 * ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
    simpa [Nat.cast_sub hkT] using hcast
  nlinarith [hcast']

/-- Theorem 2.24: on a finite-dimensional real inner-product space, for the constant-step
gradient-method trajectory with step `1 / L`, some iterate among `x₀, …, x_T` has squared
gradient norm at most `16 L² ‖x₀ - x^*‖² / ((T + 4) (T + 6))` whenever `T ≥ 3`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Route correction: the file now follows the source proof through the tail-window minimum
-- `g_{k,T}` instead of importing the later Theorem 2.25 bridge.
-- Proof sketch: treat the degenerate case `L = 0` separately, where the Lipschitz-gradient
-- hypothesis forces all gradients to vanish. For `L > 0`, choose the midpoint-like window start
-- `k = (T - 3) / 2`, bound the tail minimum `g_{k,T}` by the Chapter 1 finite-window estimate
-- plus the Chapter 2 stage-`k` objective-gap decay, and then use the attainment lemma for
-- `minGradientNormAlongIterates` to extract the desired iterate.
theorem gradientMethod_exists_iterate_with_small_gradient_sq
    (xStar : E) (x0 : E) {T : ℕ}
    (hf : f ∈ 𝓕[L, p]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hT : 3 ≤ T) :
    ∃ i ≤ T,
      ‖∇ f ((gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0) i)‖ ^ (2 : ℕ) ≤
        (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
          ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
  let traj : ℕ → E := gradientMethod (fun _ ↦ 1 / (L : ℝ)) f x0
  by_cases hL0 : (L : ℝ) = 0
  · have hgrad_zero : ∀ x : E, ∇ f x = 0 := by
      intro x
      have hgradStar : ∇ f xStar = 0 := hf.gradient_eq_zero_of_isMinOn hxStar
      have hdist := hf.gradient_lipschitz.dist_le_mul x xStar
      have hdist_eq :
          dist (∇ f x) (∇ f xStar) = 0 := by
        apply le_antisymm
        · simpa [hL0] using hdist
        · exact dist_nonneg
      have hsame : ∇ f x = ∇ f xStar := eq_of_dist_eq_zero hdist_eq
      simpa [hgradStar] using hsame
    -- When `L = 0`, every gradient vanishes, so the zeroth iterate already satisfies the claim.
    refine ⟨0, Nat.zero_le T, ?_⟩
    have hrhs_zero :
        (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((T + 4 : ℝ) * (T + 6 : ℝ)) = 0 := by
      simp [hL0]
    simp [hgrad_zero x0, hrhs_zero]
  · have hL : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
    let k : ℕ := (T - 3) / 2
    have hkT : k ≤ T := by
      dsimp [k]
      omega
    have hwindow :
        g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k);
          0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) ≤
          (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
      simpa [traj, k] using
        tail_window_min_gradient_sq_le_explicit_bound
          (hf := hf) (xStar := xStar) (x0 := x0) (hxStar := hxStar) hL hkT
    have hprod :
        ((T + 4 : ℝ) * (T + 6 : ℝ)) / 4 ≤ (k + 4 : ℝ) * (T - k + 1 : ℝ) := by
      simpa [k] using midpoint_window_product_ge_quarter_target (T := T) hT
    rcases minGradientNormAlongIterates.exists_eq
        f (gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k)) (Nat.zero_le (T - k)) with
      ⟨j, hj0, hjTk, hjEq⟩
    let i : ℕ := k + j
    have hiT : i ≤ T := by
      dsimp [i]
      omega
    have htail :
        gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k) j = traj i := by
      dsimp [i]
      simpa [traj, add_comm] using
        gradientMethod_restart_eq_tail (f := f) (α := 1 / (L : ℝ)) x0 k j
    have hmid :
        ‖∇ f (traj i)‖ ^ (2 : ℕ) ≤
          (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := by
      -- Evaluate the tail-window minimum at the attaining index `j`.
      calc
        ‖∇ f (traj i)‖ ^ (2 : ℕ)
            = ‖∇ f (gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k) j)‖ ^ (2 : ℕ) := by
              rw [htail]
        _ = g[f; gradientMethod (fun _ ↦ 1 / (L : ℝ)) f (traj k);
              0, T - k | Nat.zero_le (T - k)] ^ (2 : ℕ) := by
              rw [← hjEq]
        _ ≤ (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              ((k + 4 : ℝ) * (T - k + 1 : ℝ)) := hwindow
    have hfinal_window :
        (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ)) ≤
          (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
      have hrecip :
          1 / ((k + 4 : ℝ) * (T - k + 1 : ℝ)) ≤
            1 / (((T + 4 : ℝ) * (T + 6 : ℝ)) / 4) :=
        one_div_le_one_div_of_le (by positivity) hprod
      have hnum_nonneg : 0 ≤ 4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_left hrecip hnum_nonneg
      calc
        (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
            ((k + 4 : ℝ) * (T - k + 1 : ℝ))
            =
            (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) *
              (1 / ((k + 4 : ℝ) * (T - k + 1 : ℝ))) := by
              simp [div_eq_mul_inv]
        _ ≤ (4 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) *
              (1 / (((T + 4 : ℝ) * (T + 6 : ℝ)) / 4)) := hmul
        _ = (16 * (L : ℝ) ^ (2 : ℕ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
              ((T + 4 : ℝ) * (T + 6 : ℝ)) := by
              field_simp
              ring
    refine ⟨i, hiT, ?_⟩
    exact hmid.trans hfinal_window

end ConvexC1SeminormSmooth

end
