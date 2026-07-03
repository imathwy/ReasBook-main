import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_12 (from Chap06) -/
noncomputable section

open scoped StandardSimplex

variable {n m : ℕ+}

/-- Definition 6.12: [Simplex saddle-point problem and primal--dual nonsmooth forms] a simplex
saddle-point problem is determined by a matrix `A : ℝⁿ → ℝᵐ` and linear terms `c ∈ ℝⁿ` and
`b ∈ ℝᵐ`; the feasible sets are the standard simplices `Δ_n` and `Δ_m`, and the associated
saddle, primal nonsmooth, and dual nonsmooth objectives are the canonical derived declarations
defined below. -/
structure SimplexSaddlePointProblem (n m : ℕ+) where
  /-- The matrix `A : ℝⁿ → ℝᵐ` defining the bilinear coupling term. -/
  matrix : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ
  /-- The primal linear term `c ∈ ℝⁿ`. -/
  primalLinearTerm : EuclideanSpace ℝ (Fin (n : ℕ))
  /-- The dual linear term `b ∈ ℝᵐ`. -/
  dualLinearTerm : EuclideanSpace ℝ (Fin (m : ℕ))

namespace SimplexSaddlePointProblem

local notation "Eₙ" => EuclideanSpace ℝ (Fin (n : ℕ))
local notation "Eₘ" => EuclideanSpace ℝ (Fin (m : ℕ))

/-- The canonical Euclidean linear map induced by the matrix `A`. -/
abbrev linearMap (problem : SimplexSaddlePointProblem n m) : Eₙ →ₗ[ℝ] Eₘ :=
  problem.matrix.toEuclideanLin

/-- The simplex saddle-point problem as a Chapter 6 structured objective model. -/
def toStructuredObjectiveModel (problem : SimplexSaddlePointProblem n m) :
    StructuredObjectiveModel Eₙ Eₘ where
  primalSet := (EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n]
  primalSet_bounded := by
    sorry
  primalSet_closed := by
    sorry
  primalSet_convex := by
    sorry
  dualSet := (EuclideanSpace.equiv (Fin (m : ℕ)) ℝ) ⁻¹' Δ[m]
  dualSet_bounded := by
    sorry
  dualSet_closed := by
    sorry
  dualSet_convex := by
    sorry
  smoothPart := InnerProductSpace.toDual ℝ Eₙ problem.primalLinearTerm
  dualPenalty := -InnerProductSpace.toDual ℝ Eₘ problem.dualLinearTerm
  linearMap :=
    (InnerProductSpace.toDual ℝ Eₘ).toContinuousLinearMap.comp
      problem.linearMap.toContinuousLinearMap
  smoothPart_continuous := by
    sorry
  smoothPart_convex := by
    sorry
  dualPenalty_continuous := by
    sorry
  dualPenalty_convex := by
    sorry

/-- The simplex saddle-function
`(x, u) ↦ ⟪A x, u⟫ + ⟪c, x⟫ + ⟪b, u⟫` on `Δ_n × Δ_m`. -/
def saddleFunction (problem : SimplexSaddlePointProblem n m) :
    Δ[n] → Δ[m] → ℝ :=
  fun x u ↦
    dotProduct (problem.matrix.mulVec x.1) u.1 +
      dotProduct problem.primalLinearTerm x.1 +
      dotProduct problem.dualLinearTerm u.1

/-- A simplex saddle-point problem can be evaluated as its canonical saddle function on
`Δ_n × Δ_m`. -/
instance : CoeFun (SimplexSaddlePointProblem n m) (fun _ ↦
    Δ[n] → Δ[m] → ℝ) where
  coe problem := problem.saddleFunction

/-- The primal nonsmooth objective
`x ↦ ⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}` on `Δ_n`. -/
def primalObjective (problem : SimplexSaddlePointProblem n m) :
    Δ[n] → ℝ :=
  fun x ↦
    dotProduct problem.primalLinearTerm x.1 +
      Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ dotProduct (problem.matrix j) x.1 + problem.dualLinearTerm j)

/-- The dual nonsmooth objective
`u ↦ ⟪b, u⟫ + min_i {⟪\hat a_i, u⟫ + c^(i)}` on `Δ_m`. -/
def dualObjective (problem : SimplexSaddlePointProblem n m) :
    Δ[m] → ℝ :=
  fun u ↦
    dotProduct problem.dualLinearTerm u.1 +
      Finset.univ.inf' Finset.univ_nonempty
        (fun i : Fin (n : ℕ) ↦
          dotProduct (problem.matrix.transpose i) u.1 + problem.primalLinearTerm i)

/-- Evaluating the simplex saddle function gives the bilinear term `⟪A x, u⟫` together with the
linear contributions `⟪c, x⟫` and `⟪b, u⟫`. -/
theorem saddleFunction_apply (problem : SimplexSaddlePointProblem n m)
    (x : Δ[n]) (u : Δ[m]) :
    problem.saddleFunction x u =
      dotProduct (problem.matrix.mulVec x.1) u.1 +
        dotProduct problem.primalLinearTerm x.1 +
        dotProduct problem.dualLinearTerm u.1 :=
  rfl

/-- The primal nonsmooth objective equals the row-wise maximum
`⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}`, where `a_j` is the `j`-th row of `A`. -/
theorem primalObjective_eq_max_rows (problem : SimplexSaddlePointProblem n m)
    (x : Δ[n]) :
    problem.primalObjective x =
      dotProduct problem.primalLinearTerm x.1 +
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m : ℕ) ↦
            dotProduct (problem.matrix j) x.1 + problem.dualLinearTerm j) :=
  rfl

/-- The dual nonsmooth objective equals the column-wise minimum
`⟪b, u⟫ + min_i {⟪\hat a_i, u⟫ + c^(i)}`, where `\hat a_i` is the `i`-th column of `A`. -/
theorem dualObjective_eq_min_columns (problem : SimplexSaddlePointProblem n m)
    (u : Δ[m]) :
    problem.dualObjective u =
      dotProduct problem.dualLinearTerm u.1 +
        Finset.univ.inf' Finset.univ_nonempty
          (fun i : Fin (n : ℕ) ↦
            dotProduct (problem.matrix.transpose i) u.1 + problem.primalLinearTerm i) :=
  rfl

end SimplexSaddlePointProblem

end

/-! ### Lemma_6_12 (from Chap06) -/
universe u v

-- Proof sketch: the inequalities `φ uBar ≤ fμ₂ xBar ≤ f xBar` give the lower bound
-- `0 ≤ f xBar - φ uBar`. The local estimate for `fμ₂` at `xBar` bounds the smoothing defect
-- `f xBar - fμ₂ xBar` by `μ₂ * D₂`; adding the assumed residual smoothed gap bound
-- `fμ₂ xBar - φ uBar ≤ r` gives the upper bound
-- `f xBar - φ uBar ≤ μ₂ * D₂ + r`.
/-- Lemma 6.12: if `fμ₂` satisfies the local lower smoothing bound
`f xBar - μ₂ D₂ ≤ fμ₂ xBar`, if
`φ uBar ≤ fμ₂ xBar ≤ f xBar`, and if the residual smoothed gap `fμ₂ xBar - φ uBar` is bounded
above by `r`, then the raw primal-dual gap at `(xBar, uBar)` lies in the interval
`[0, μ₂ D₂ + r]`. -/
theorem primal_dual_gap_bound_of_smoothed_lower_approximation
    {Q₁ : Type u} {Q₂ : Type v}
    {f fμ₂ : Q₁ → ℝ} {φ : Q₂ → ℝ} {μ₂ D₂ r : ℝ}
    {xBar : Q₁} {uBar : Q₂}
    (happrox : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφ_le : φ uBar ≤ fμ₂ xBar) (hresidual : fμ₂ xBar - φ uBar ≤ r)
    (hsmoothed_le : fμ₂ xBar ≤ f xBar) :
    f xBar - φ uBar ∈ Set.Icc 0 (μ₂ * D₂ + r) := by
  have hsmoothing_defect : f xBar - fμ₂ xBar ≤ μ₂ * D₂ := by
    linarith
  refine Set.mem_Icc.mpr ⟨sub_nonneg.mpr (le_trans hφ_le hsmoothed_le), ?_⟩
  linarith

/-! ### Proposition_6_12 (from Chap06) -/
noncomputable section

universe u

namespace LagrangianProblem

/- Proposition 6.12 lies in the Chapter 6 Lagrangian-duality domain.

Primary domain:
- no-duality-gap consequences for the Chapter 1 owner `LagrangianProblem`

Sampled owner-style declarations:
- `LagrangianProblem.primalOptimalValue` and `LagrangianProblem.dualOptimalValue` in
  `Chap01/Definition_1_10_2`
- `LagrangianProblem.dualOptimalValue_le_primalOptimalValue` in `Chap01/Proposition_1_10_8`
- the scalar antisymmetry pattern in `Chap06/Remark_6_1_2`

Best owner abstraction:
- `problem : LagrangianProblem Q m`

Primitive data:
- the owner `problem`

Derived API:
- `problem.primalOptimalValue`
- `problem.dualOptimalValue`
- weak duality `problem.dualOptimalValue_le_primalOptimalValue`

Source/core/bridge triage:
- source-facing: the no-gap conclusion from the reverse inequality `f* ≤ f_*`
- core/canonical: the Chapter 1 owner theorem `problem.dualOptimalValue_le_primalOptimalValue`
- bridge/view: this file packages antisymmetry with the assumed reverse inequality

There is no new mathematical owner here. The statement is a thin bridge from the assumed reverse
bound to equality, so the proof should reuse the Chapter 1 weak-duality owner theorem directly
instead of keeping any parallel local duality API.
-/

/-- Proposition 6.12: if the primal optimal value of a Lagrangian problem is bounded above by its
dual optimal value, then there is no duality gap, so the primal and dual optimal values are
equal. -/
-- Proof sketch: combine the assumed inequality `f* ≤ f_*` with weak duality
-- `f_* ≤ f*` for Lagrangian problems, and conclude by antisymmetry.
theorem noDualityGap_of_primalOptimalValue_le_dualOptimalValue
    {Q : Type u} {m : ℕ} (problem : LagrangianProblem Q m)
    (h : problem.primalOptimalValue ≤ problem.dualOptimalValue) :
    problem.primalOptimalValue = problem.dualOptimalValue := by
  exact le_antisymm h problem.dualOptimalValue_le_primalOptimalValue

end LagrangianProblem

/-! ### Theorem_6_12 (from Chap06) -/
noncomputable section

open scoped BigOperators WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.12 lies in the Chapter 6 conditional-gradient / weighted upper-bound domain.

Sampled owner-style declarations:
- `initialLinearizationGap` in `Definition_6_54`, the source-facing owner of the initial quantity
  `V₀`;
- `linearOptimizationOracleErrorBound` in `Definition_6_54`, the Chapter 6 owner of the
  cumulative error term `B_{ν,t}`;
- `LinearOracleCompositeMethod` in `Algorithm_6_4`, the chapter owner of the iterate and
  oracle-point data for method `(6.4.12)`;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the ambient
  extended-valued bridge/view owner that `Definition_6_54` specializes away from on this theorem
  surface.

Best owner abstraction:
- source-facing: the weighted composite upper bound with
  `initialLinearizationGap Q f Ψ (method 0)` as the initial quantity;
- core/canonical: `LinearOracleCompositeMethod` together with
  `linearOptimizationOracleErrorBound`;
- bridge/view: the ambient extended-regularizer gap value, which should not appear in the theorem
  statement.

Primitive data:
- the feasible set `Q`, objective `f`, subtype regularizer `Ψ`, and method data;
- convexity of the canonical ambient extension `Function.extend Subtype.val Ψ 0` on `Q`, the
  owner abstraction that expresses convexity of the subtype regularizer along feasible segments;
- the weight sequence `a`, Hölder data `ν`, `Gν`, `D`, and the Chapter 6 hypotheses on `a`,
  `τ_t`, and the `(6.4.3)`-style error term.

Derived API:
- the weighted affine-linearization upper bound at time `t`;
- the canonical Chapter 6 error term
  `linearOptimizationOracleErrorBound (initialLinearizationGap Q f Ψ (method 0)) a Gν D ν t`.

Source/core/bridge triage:
- source-facing: this weighted estimate for the composite conditional-gradient method;
- core/canonical: the Chapter 6 owners `initialLinearizationGap` and
  `linearOptimizationOracleErrorBound`;
- bridge/view: `ConditionalGradientContraction.linearizedCompositeGap`, used upstream only to
  justify `initialLinearizationGap` and intentionally absent from the theorem surface.
-/

-- Proof sketch: argue by induction on `t`. For the induction step, combine convexity of `f`
-- on `Q` and convexity of the ambient extension `Function.extend Subtype.val Ψ 0` on `Q` with
-- the update
-- `x_{t+1} = (1 - τ_t) x_t + τ_t v_t`, use the oracle minimization property at `v_t`, and then
-- insert the assumed `(6.4.3)`-style Hölder error bound to absorb the residual term into the
-- Chapter 6 owner `linearOptimizationOracleErrorBound`, initialized by the source-facing
-- constrained linearization-gap owner `initialLinearizationGap` at the primitive starting point
-- `x₀ = method.x0`.
/-- Theorem 6.12: along method `(6.4.12)`, if `f` is convex on `Q`, the canonical ambient
extension of the regularizer `Ψ` is convex on `Q`, the coefficients satisfy
`A_t = ∑_{k=0}^t a_k` and `τ_t = a_{t+1} / A_{t+1}`, and the `(6.4.3)` Hölder-gradient error term
is bounded by `G_ν D^(1 + ν)`, then for every iteration `t` and feasible point `x` the weighted
composite objective at `x_t` is bounded by the sum of the affine linearizations at `x` plus the
Chapter 6 error term `linearOptimizationOracleErrorBound V₀ a G_ν D ν t`, where
`V₀ = initialLinearizationGap Q f Ψ x₀` and `x₀ = method.x0`. -/
theorem weighted_objective_upper_bound_of_linear_oracle_composite_method
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (hΨ_convex : ConvexOn ℝ Q (Function.extend Subtype.val Ψ 0))
    (method : LinearOracleCompositeMethod Q f Ψ)
    (a : ℕ → ℝ) (ν Gν D : ℝ)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ, ∀ x : Q,
        inner ℝ
            (gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t))
            ((x : E) - method.oraclePoint t) ≥
          -((Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)))
    (t : ℕ) (x : Q) :
    A[a](t) * (f (method t) + Ψ (method t)) ≤
      (Finset.sum (Finset.range (t + 1)) fun k ↦
        a k *
          (f (method k) +
            inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
            Ψ x)) +
        linearOptimizationOracleErrorBound
          (initialLinearizationGap Q f Ψ method.x0) a Gν D ν t := sorry
