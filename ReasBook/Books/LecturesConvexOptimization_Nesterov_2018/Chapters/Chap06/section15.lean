import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_15 (from Chap06) -/
open scoped BigOperators

noncomputable section

/- Definition 6.15 lies in the continuous-location / constrained-minimization domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem`, the Chapter 1 owner of a feasible set together with a
  real-valued objective;
- `ContinuousLocationWeights`, the chapter owner of the positive masses `m_j`;
- `Metric.closedBall`, the canonical owner of the Euclidean constraint `‖x‖ ≤ r̄`;
- `mem_closedBall_zero_iff`, the canonical bridge from origin-centered closed-ball membership to
  a norm bound.

Best owner abstraction:
- source-facing: the weighted Euclidean location objective together with the radius-constrained
  minimization problem;
- core/canonical: `SetConstrainedMinimizationProblem` and `Metric.closedBall`;
- bridge/view: the objective expansion and the closed-ball membership rewrite
  `‖x‖ ≤ r̄`.

Primitive data:
- the number `p` of demand points and the dimension `n`;
- positive weights `m_j`, packaged as `ContinuousLocationWeights (Fin p)`;
- centers `c_j : ℝ^n`;
- a radius bound `r̄ : ℝ≥0`.

Derived API:
- the source-facing objective `x ↦ ∑ j, m_j ‖x - c_j‖`;
- the constrained minimization problem on the closed Euclidean ball;
- the feasible-set membership view `‖x‖ ≤ r̄`.
-/

section

variable {p n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The weighted Euclidean objective `f(x) = ∑_{j=1}^p m_j ‖x - c_j‖` of the continuous location
problem. -/
def continuousLocationObjective
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) :
    E → ℝ :=
  fun x ↦ ∑ j, (weights j : ℝ) * ‖x - centers j‖

-- Proof sketch: unfold `continuousLocationObjective`.
/-- Evaluating `continuousLocationObjective` recovers the weighted sum
`∑_{j=1}^p m_j ‖x - c_j‖`. -/
@[simp] theorem continuousLocationObjective_apply
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (x : E) :
    continuousLocationObjective weights centers x =
      ∑ j, (weights j : ℝ) * ‖x - centers j‖ := sorry

/-- Definition 6.15 [Chapter6_2.json:39]: the constrained location problem is the constrained
minimization problem with objective `f(x) = ∑_{j=1}^p m_j ‖x - c_j‖` over the Euclidean closed
ball `‖x‖ ≤ r̄`. -/
def continuousLocationProblem
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    SetConstrainedMinimizationProblem E :=
  { feasibleSet := Metric.closedBall (0 : E) (rBar : ℝ)
    objective := continuousLocationObjective weights centers }

/-- The feasible set of `continuousLocationProblem` is the closed Euclidean ball of radius `r̄`
centered at the origin. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_feasibleSet
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    (continuousLocationProblem weights centers rBar).feasibleSet =
      Metric.closedBall (0 : E) (rBar : ℝ) := sorry

/-- The objective field of `continuousLocationProblem` is the weighted sum-of-distances objective
`continuousLocationObjective`. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_objective
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    (continuousLocationProblem weights centers rBar).objective =
      continuousLocationObjective weights centers := sorry

/-- Unfolding `continuousLocationProblem` recovers the closed Euclidean ball together with the
continuous-location objective. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_def
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    continuousLocationProblem weights centers rBar =
      { feasibleSet := Metric.closedBall (0 : E) (rBar : ℝ)
        objective := continuousLocationObjective weights centers } := sorry

/-- Coercing `continuousLocationProblem` to a function recovers the weighted sum-of-distances
objective `continuousLocationObjective`. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_coe
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    ⇑(continuousLocationProblem weights centers rBar) =
      continuousLocationObjective weights centers := sorry

/-- Evaluating `continuousLocationProblem` at a point `x` recovers the source-facing continuous-
location objective `continuousLocationObjective weights centers x`. -/
-- Proof sketch: apply `continuousLocationProblem_objective`.
@[simp] theorem continuousLocationProblem_spec
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E)
    (rBar : NNReal) (x : E) :
    continuousLocationProblem weights centers rBar x =
      continuousLocationObjective weights centers x := sorry

/-- Evaluating `continuousLocationProblem` recovers the formula
`∑_{j=1}^p m_j ‖x - c_j‖`. -/
-- Proof sketch: combine `continuousLocationProblem_objective` with
-- `continuousLocationObjective_apply`.
@[simp] theorem continuousLocationProblem_apply
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) (x : E) :
    continuousLocationProblem weights centers rBar x =
      ∑ j, (weights j : ℝ) * ‖x - centers j‖ := sorry

/-- A point is feasible for `continuousLocationProblem` exactly when its Euclidean norm is at most
`r̄`. -/
-- Proof sketch: rewrite the feasible set using `continuousLocationProblem_feasibleSet`, then
-- apply `mem_closedBall_zero_iff`.
@[simp] theorem continuousLocationProblem_mem_feasibleSet_iff
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E)
    (rBar : NNReal) (x : E) :
    x ∈ (continuousLocationProblem weights centers rBar).feasibleSet ↔ ‖x‖ ≤ (rBar : ℝ) := sorry

end

end

/-! ### Lemma_6_15 (from Chap06) -/
noncomputable section

open MeasureTheory
open scoped BigOperators

/-
Lemma 6.15 lies in the one-dimensional interval-integral / convex-sampling domain.

Sampled owner-style declarations:
- `AntitoneOn.integral_le_sum` and `AntitoneOn.sum_le_integral` in
  `Mathlib/Analysis/SumIntegralComparisons`, the canonical left/right endpoint comparison lemmas
  for monotone samples against interval integrals;
- `intervalIntegral.sum_integral_adjacent_intervals`, the canonical owner for decomposing an
  interval integral into unit cells;
- `ConvexOn.map_sum_le` in `Mathlib/Analysis/Convex/Jensen`, the canonical finite Jensen owner for
  midpoint estimates of convex functions.

Best owner abstraction:
- source-facing: the textbook sandwich estimate for the integer samples of a decreasing convex
  function;
- core/canonical: `AntitoneOn`, `ConvexOn`, `intervalIntegral`, and Jensen-style midpoint bounds;
- bridge/view: the centered unit intervals `[k - 1 / 2, k + 1 / 2]`, whose midpoint is the sample
  point `k`.

Primitive data:
- `ξ : ℝ → ℝ`;
- integer endpoints `a ≤ b`.

Derived API:
- the sample sum `∑ k ∈ Finset.Icc a b, ξ k`;
- the two canonical interval integrals bounding that sum.

This item does not define a new owner. The refinement keeps the source-facing theorem, places its
conclusion on the canonical `Set.Icc` surface, and keeps the monotonicity and convexity hypotheses
on the separate minimal intervals actually used by the lower and upper bounds.
-/

/-- Lemma 6.15: if a real function is decreasing on `[a, b + 1]` and convex on
`[a - 1 / 2, b + 1 / 2]`, then the sum of its integer samples from `a` to `b` lies between the
integral over `[a, b + 1]` and the centered integral over `[a - 1 / 2, b + 1 / 2]`. -/
-- Proof sketch: the lower bound comes from applying monotonicity on each unit interval
-- `[k, k + 1]`, while the upper bound comes from convexity on each centered interval
-- `[k - 1 / 2, k + 1 / 2]` and summing the resulting midpoint estimates.
theorem sum_integer_samples_between_intervalIntegrals_of_antitoneOn_convexOn
    (ξ : ℝ → ℝ) (a b : ℤ) (hab : a ≤ b)
    (hantitone : AntitoneOn ξ (Set.Icc (a : ℝ) ((b : ℝ) + 1)))
    (hconvex :
      ConvexOn ℝ (Set.Icc ((a : ℝ) - (1 / 2 : ℝ)) ((b : ℝ) + (1 / 2 : ℝ))) ξ) :
    (∑ k ∈ Finset.Icc a b, ξ (k : ℝ)) ∈
      Set.Icc
        (∫ x in (a : ℝ)..((b : ℝ) + 1), ξ x)
        (∫ x in ((a : ℝ) - (1 / 2 : ℝ))..((b : ℝ) + (1 / 2 : ℝ)), ξ x) := by
  sorry

/-! ### Proposition_6_15 (from Chap06) -/
noncomputable section

open InnerProductSpace
open scoped BigOperators SeminormOperatorNorm

/- Proposition 6.15 lies in the finite-dimensional `ℓ₁`/`ℓ∞` matrix-game norm domain.

Sampled owner declarations:
* `Seminorm.primalDualOperatorNorm`, the chapter owner for induced norms between separated source
  and target seminorm geometries;
* `EuclideanSpace.l1Seminorm`, the project owner for the coordinate `ℓ₁` seminorm on `ℝⁿ`;
* `Matrix.toEuclideanLin`, the canonical Euclidean realization of a matrix action;
* `dotProduct`, the source-facing row-pairing expression for matrix rows.

Best owner abstraction:
* source-facing: the supremum of the maximal absolute row pairing over the `ℓ₁` unit ball;
* core/canonical: `Seminorm.primalDualOperatorNorm` applied to
  `((InnerProductSpace.toDual ℝ _).toLinearMap.comp A.toEuclideanLin)`;
* bridge/view: the passage from the canonical operator norm to the entrywise maximum
  `max_{i,j} |A^{(i,j)}|`.

Primitive data:
* the real matrix `A`.

Derived API:
* the row-pairing supremum formula;
* the evaluation of the canonical `ℓ₁ → ℓ∞` operator norm by the maximal absolute entry;
* the entropy-distance rewrite of the primal-dual gap estimate from the norm form to the
  max-entry form.
-/

universe u v

variable {m n : ℕ+}

local notation "EN" => EuclideanSpace ℝ (Fin (n : ℕ))
local notation "EM" => EuclideanSpace ℝ (Fin (m : ℕ))

/-- The supremum of the maximal absolute row pairing over the `ℓ₁` unit ball equals the largest
absolute entry of the matrix. -/
-- Proof sketch: for any `x` in the `ℓ₁` unit ball, each row pairing `dotProduct (A j) x` is
-- bounded by the maximal absolute entry of `A`. For the reverse inequality, use a signed
-- standard basis vector supported at a column where `A` attains that maximal absolute entry.
theorem matrix_l1_rowPairing_sSup_eq_max_abs_entry
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) :
    sSup ((fun x : EN ↦
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        Real.nnabs (dotProduct (A j) x))) ''
      {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := sorry

/-- The canonical `ℓ₁ → ℓ∞` operator norm of a real matrix is the largest absolute value of its
entries. -/
-- Proof sketch: rewrite the canonical operator norm as the source-facing supremum of the maximal
-- absolute row pairing over the `ℓ₁` unit ball, then apply
-- `matrix_l1_rowPairing_sSup_eq_max_abs_entry`.
theorem matrix_l1_to_linfty_operatorNorm_eq_max_abs_entry
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) :
    ‖(toDual ℝ EM).toLinearMap.comp A.toEuclideanLin‖[EuclideanSpace.l1Seminorm (n : ℕ) ⇀
        EuclideanSpace.l1Seminorm (m : ℕ),*] =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := sorry

/-- Proposition 6.15 [Chapter6_1.json:39]: if the entropy-distance matrix-game gap estimate is
written with the canonical `ℓ₁ → ℓ∞` operator norm of `A`, then the same estimate can be written
with the largest absolute matrix entry `max_{i,j} |A^{(i,j)}|`. -/
-- Proof sketch: keep the lower endpoint `0` unchanged and rewrite only the operator-norm factor
-- in the assumed upper bound using `matrix_l1_to_linfty_operatorNorm_eq_max_abs_entry`.
theorem matrix_game_entropy_gap_mem_Icc_max_abs_entry_bound
    {X : Type u} {U : Type v}
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ)
    (f : X → ℝ) (φ : U → ℝ) (xHat : X) (uHat : U) (N : ℕ+)
    (hnonneg : 0 ≤ f xHat - φ uHat)
    (hgap_le :
      f xHat - φ uHat ≤
        ((4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ))) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ‖(toDual ℝ EM).toLinearMap.comp A.toEuclideanLin‖[EuclideanSpace.l1Seminorm (n : ℕ) ⇀
            EuclideanSpace.l1Seminorm (m : ℕ),*]) :
    f xHat - φ uHat ∈
      Set.Icc 0
        (((4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ))) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
            (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i))) := sorry

end

/-! ### Theorem_6_15 (from Chap06) -/
noncomputable section

open scoped BigOperators StrongConvex WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.15 lies in the Chapter 6 strong-convex conditional-gradient domain.

Mandatory domain-style sampling:
- `initialLinearizationGap` in `Definition_6_54`, the chapter source-facing owner of the initial
  quantity `V₀`;
- `Ψ ∈ 𝒮^0_σΨ(Q)` / `mem_S0On_iff` in `Definition_6_65`, the chapter owner for positive
  fixed-parameter strong convexity on the feasible set;
- `stronglyConvexCompositeErrorBound` in `Definition_6_66`, the chapter owner for the textbook
  error term `\hat B_{v,t}`;
- `LinearOracleCompositeMethod` in `Algorithm_6_4`, the chapter owner of the iterate/oracle data
  for method `(6.4.12)`.

Best owner abstraction:
- source-facing: the weighted upper bound for method `(6.4.12)` under the chapter strong-convexity
  owner, with initial quantity
  `initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0` and textbook error term
  `\hat B_{v,t}`;
- core/canonical: `LinearOracleCompositeMethod`, `Ψ ∈ 𝒮^0_σΨ(Q)`,
  `initialLinearizationGap`, and `stronglyConvexCompositeErrorBound`;
- bridge/view: `mem_S0On_iff`, used only to recover `0 < σΨ` and `StrongConvexOn Q σΨ Ψ`
  internally.

Primitive data:
- the feasible set `Q`, objective `f`, ambient regularizer `Ψ`, and method data;
- the weight sequence `a` and the Hölder-style parameters `v`, `Gv`, `D`.

Derived API:
- the weighted affine-linearization upper bound at time `t`;
- the specialized Chapter 6 error term initialized by the canonical starting gap
  `initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0`.
-/

-- Proof sketch: argue by induction on `t`. For the induction step, combine the one-step estimate
-- from method `(6.4.12)` with the strong convexity lower bound for `Ψ` at the oracle point
-- `v_t`, then apply the quadratic inequality
-- `⟪s, u⟫ + (σΨ / 2) ‖u‖² ≥ -(1 / (2 σΨ)) ‖s‖²` to
-- `s = ∇f(x_{t+1}) - ∇f(x_t)` and `u = x - v_t`. Finally insert the bound `(6.4.3)` and absorb
-- the resulting term into the Chapter 6 owner
-- `stronglyConvexCompositeErrorBound
--   (initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0) a v Gv D σΨ`.
/-- Theorem 6.15: if `Ψ` is `σ_Ψ`-strongly convex on the convex feasible set `Q`, method
`(6.4.12)` is run with positive weights `a_t > 0` and coefficients
`τ_t = a_{t+1} / A_{t+1}`, and the gradient differences satisfy the bound `(6.4.3)`, then for
every `t ≥ 0` and every feasible comparison point `x ∈ Q` the weighted composite objective at
`x_t` is bounded by the weighted affine linearizations at `x` plus the recursive error term
`\hat B_{v,t}` initialized by
`V₀ = initialLinearizationGap Q f (fun x : Q ↦ Ψ x) x₀`, where `x₀ = method.x0`. -/
theorem weighted_objective_upper_bound_of_strongly_convex_linear_oracle_composite_method
    {Q : Set E} {f Ψ : E → ℝ} {σΨ : ℝ}
    (hΨ : Ψ ∈ 𝒮^0_σΨ(Q))
    (method : LinearOracleCompositeMethod Q f (fun x : Q ↦ Ψ x))
    (a : ℕ → ℝ) (v Gv D : ℝ)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ,
        ‖gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t)‖ ≤
          (Real.rpow (a (t + 1)) v /
              Real.rpow (A[a](t.succ)) v) *
            Gv * Real.rpow D v)
    (t : ℕ) (x : Q) :
    A[a](t) * (f (method t) + Ψ (method t)) ≤
      (Finset.sum (Finset.range (t + 1)) fun k ↦
        a k *
          (f (method k) +
            inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
            Ψ x)) +
        stronglyConvexCompositeErrorBound
          (initialLinearizationGap Q f (fun x : Q ↦ Ψ x) method.x0) a v Gv D σΨ t := sorry

end
