import Nesterov.Chap06.Theorem_6_14
import Nesterov.Chap06.Algorithm_6_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConstrainedArgmin Gradient WeightSequenceNotation WithTopConvexAnalysis

universe u

namespace SecondOrderLocalModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.16 lies in the Chapter 6 second-order composite trust-region domain.

Mandatory owner-style sampling before refining:
- `CompositeTrustRegionContractionMethod` in `Algorithm_6_6`, the chapter's recursive owner for
  method `(6.4.50)`;
- `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the canonical quadratic Taylor-model
  owner;
- `contractedCompositeSecondOrderModel` in `Algorithm_6_6`, the chapter owner of the contracted
  quadratic composite subproblem;
- `ConditionalGradientContraction.estimatingFunctionalSequence` in `Theorem_6_14`, the chapter
  owner for recursive estimating-function families.

Best owner abstraction:
- source-facing: this theorem's second-order estimating function, error recursion, and
  second-order optimality measure on the finite feasible domain;
- core/canonical: `CompositeTrustRegionContractionMethod`, `secondOrderTaylorModelAt`,
  `contractedCompositeSecondOrderModel`, and
  `ConditionalGradientContraction.estimatingFunctionalSequence`;
- bridge/view: the finite-value representative `withTopRealPart problem.nonsmoothPart` and the
  iterate restriction to `Q ∩ dom Ψ`.

Primitive data:
- the ambient composite problem `problem`;
- the initial feasible point `x0`;
- the recursive method owner `method : CompositeTrustRegionContractionMethod problem x0`.

Derived API:
- the specialized estimating sequence for the initial model
  `f + withTopRealPart Ψ`;
- the recursive second-order error term;
- the source-facing second-order optimality measure on `Q ∩ dom Ψ`. -/

/-- The increment added at step `t + 1` to the second-order error term `\hat C_{ν,t}`. -/
def secondOrderErrorIncrement
    (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) : ℝ :=
  (a (t + 1) * a (t + 1) / A[a]((t + 1))) *
      (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) +
    (a (t + 1) * a (t + 1) / ((2 : ℝ) * A[a]((t + 1)))) * L * D * D

/-- Expanding `secondOrderErrorIncrement a L Hν D ν t` gives the `H_ν D^{2+ν}` and `L D^2`
contributions added at step `t + 1`, with the canonical Chapter 6 denominator `A[a](t + 1)`. -/
theorem secondOrderErrorIncrement_apply
    (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) :
    secondOrderErrorIncrement a L Hν D ν t =
      (a (t + 1) * a (t + 1) / A[a]((t + 1))) *
          (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) +
        (a (t + 1) * a (t + 1) / ((2 : ℝ) * A[a]((t + 1)))) * L * D * D :=
  rfl

/-- The recursive error term `\hat C_{ν,t}` for the second-order local-model method, using the
canonical accumulated weights `A[a](t)`. -/
def secondOrderError
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) : ℕ → ℝ
  | 0 => initialError
  | t + 1 => secondOrderError initialError a L Hν D ν t +
      secondOrderErrorIncrement a L Hν D ν t

/-- The second-order error term starts from the prescribed initial gap. -/
theorem secondOrderError_zero
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) :
    secondOrderError initialError a L Hν D ν 0 = initialError :=
  rfl

/-- The recursive step for `\hat C_{ν,t}` adds the increment from
`secondOrderErrorIncrement a L Hν D ν t`. -/
theorem secondOrderError_succ
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) :
    secondOrderError initialError a L Hν D ν (t + 1) =
      secondOrderError initialError a L Hν D ν t +
        secondOrderErrorIncrement a L Hν D ν t :=
  rfl

/-- The second-order optimality measure `θ(x)` is the maximal decrease predicted by the canonical
second-order Taylor model of `f` plus the regularizer gap at a finite feasible point
`x ∈ Q ∩ dom Ψ`, recorded in `EReal` so the owner remains faithful even when the supremum is not
bounded above in `ℝ`. -/
def secondOrderOptimalityMeasure
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) :
    ↥(Q ∩ dom Ψ) → EReal :=
  fun x ↦
    sSup ((fun y : E ↦
      (((f x + withTopRealPart Ψ x) -
            (secondOrderTaylorModelAt f x y + withTopRealPart Ψ y) : ℝ) : EReal)) ''
      (Q ∩ dom Ψ))

namespace SecondOrderOptimalityMeasureNotation

/- Source-facing Lean notation for the textbook second-order optimality measure `θ(x)` with the
ambient feasible set and composite objective data fixed by the surrounding context. -/
scoped notation:max "θ[" Q ", " f ", " Ψ "](" x:arg ")" =>
  secondOrderOptimalityMeasure Q f Ψ x

end SecondOrderOptimalityMeasureNotation

open scoped SecondOrderOptimalityMeasureNotation

/-- Expanding `θ[Q, f, Ψ](x)` gives the defining `EReal` supremum of the canonical second-order
Taylor-model decrease over the finite feasible domain `Q ∩ dom Ψ`. -/
theorem secondOrderOptimalityMeasure_def
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) (x : ↥(Q ∩ dom Ψ)) :
    θ[Q, f, Ψ](x) =
      sSup ((fun y : E ↦
        (((f x + withTopRealPart Ψ x) -
              (secondOrderTaylorModelAt f x y + withTopRealPart Ψ y) : ℝ) : EReal)) ''
        (Q ∩ dom Ψ)) :=
  rfl

section Method

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- Every iterate lies in the finite-value domain `Q ∩ dom Ψ`, because the method stays in `Q`
and `Ψ` is finite on `Q` by the owner hypothesis `ClosedConvexOn Q Ψ`. -/
theorem iterate_mem_optimalityDomain
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) :
    method t ∈ problem.feasibleSet ∩ dom problem.nonsmoothPart := by
  exact ⟨method.iterates_mem_feasibleSet t,
    problem.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain
      (method.iterates_mem_feasibleSet t)⟩

/-- The estimating sequence `φ_t` attached to Algorithm 6.6, obtained by specializing the
chapter owner `estimatingFunctionalSequence` to the initial model
`f + withTopRealPart Ψ`. -/
def estimatingFunction
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) :
    ℕ → E → ℝ :=
  ConditionalGradientContraction.estimatingFunctionalSequence
    a
    (fun x ↦ problem.smoothPart x + withTopRealPart problem.nonsmoothPart x)
    problem.smoothPart
    (fun x ↦ InnerProductSpace.toDualMap ℝ E (∇ problem.smoothPart x))
    (withTopRealPart problem.nonsmoothPart)
    method

/-- The estimating sequence starts from `φ₀(x) = a₀ \bar f(x)`. -/
theorem estimatingFunction_zero
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) :
    estimatingFunction method a 0 =
      fun x ↦ a 0 * (problem.smoothPart x + withTopRealPart problem.nonsmoothPart x) :=
  rfl

/-- The recursive step of the estimating sequence is
`φ_{t+1}(x) = φ_t(x) + a_{t+1} [f(x_t) + ⟪∇ f(x_t), x - x_t⟫ + Ψ(x)]`. -/
theorem estimatingFunction_succ
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) (t : ℕ) :
    estimatingFunction method a (t + 1) =
      fun x ↦
        estimatingFunction method a t x +
          a (t + 1) *
            (problem.smoothPart (method t) +
              inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
              withTopRealPart problem.nonsmoothPart x) :=
  rfl

/-- The canonical error sequence `\hat C_{ν,t}` anchored at the baseline point `xStar`. -/
def errorTerm
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ)
    (xStar : E) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) : ℕ → ℝ :=
  secondOrderError
    (a 0 *
      ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
        (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar)))
    a L Hν D ν

/-- Expanding `errorTerm method a xStar L Hν D ν` gives the recursive second-order error term
starting from the weighted initial objective gap at `x₀` relative to `xStar`. -/
theorem errorTerm_def
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ)
    (xStar : E) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) :
    errorTerm method a xStar L Hν D ν =
      secondOrderError
        (a 0 *
          ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
            (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar)))
        a L Hν D ν :=
  rfl

-- Proof sketch: combine the local quadratic-model minimizing property from
-- `CompositeTrustRegionContractionMethod.iterates_succ_mem_and_isMinOn` with the update formula
-- `x_{t+1} = (1 - τ_t) x_t + τ_t v_t`, use the quadratic upper-model assumption with Hölder
-- remainder and the operator-norm bound on the canonical Hessian to control the estimating-
-- sequence error, and then rewrite the second displayed inequality through the source-facing
-- second-order optimality measure on `Q ∩ dom Ψ`.
/-- Theorem 6.16: if `x_t` is generated by method `(6.4.50)`, then for every `ν ∈ [0, 1]` the
estimating-sequence bound
`A_t \bar f(x_t) ≤ φ_t(x) + \hat C_{ν,t}` holds for all `t ≥ 0` and `x ∈ Q`, and moreover the
one-step decrease satisfies
`\bar f(x_t) - \bar f(x_{t+1}) ≥ τ_t θ(x_t) - (H_ν D^{2+ν} / ((1+ν)(2+ν))) τ_t^{2+ν}`. -/
theorem estimating_function_bound_and_objective_drop
    (method : CompositeTrustRegionContractionMethod problem x0)
    (a : ℕ → ℝ) {L Hν D : ℝ} (xStar : E)
    (ν : Set.Icc (0 : ℝ) 1)
    (hxStar :
      xStar ∈
        argmin[problem.feasibleSet]
          (fun x ↦ problem.smoothPart x + withTopRealPart problem.nonsmoothPart x))
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_hessian_bound : ∀ t : ℕ, ‖hessian problem.smoothPart (method t)‖ ≤ L)
    (h_upper_model :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet →
        problem.smoothPart y ≤
          secondOrderTaylorModelAt problem.smoothPart x y +
            Hν * Real.rpow ‖y - x‖ (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) :
    (∀ t : ℕ, ∀ x : E, x ∈ problem.feasibleSet →
      A[a](t) *
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) ≤
        estimatingFunction method a t x + errorTerm method a xStar L Hν D ν t) ∧
    (∀ t : ℕ,
      (((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
              ⟨method t, iterate_mem_optimalityDomain method t⟩) -
          (((Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
              Real.rpow (method.stepSize t) (2 + (ν : ℝ)) : ℝ) : EReal)) := sorry

end Method

end SecondOrderLocalModel

end
