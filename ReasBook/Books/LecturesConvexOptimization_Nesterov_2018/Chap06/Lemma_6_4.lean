import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_14
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

section

variable (m : ℕ+)

local notation "E" => EuclideanSpace ℝ (Fin (m : ℕ))

/- Lemma 6.4 lies in the finite simplex / entropy-smoothing domain.

Sampled owner declarations:
* `normalizedEntropyProxFunction` and `normalizedEntropyProxFunction_apply` in
  `Chap06/Definition_6_14`;
* `η` and `eta_apply` via the recall surface in `Chap06/Definition_6_27`;
* `smoothMaximand` in `Chap06/Definition_6_20`;
* `smoothedDualObjectiveMinimand` in `Chap06/Definition_6_32`.

Best owner abstraction:
* source-facing: the entropy-regularized simplex objective and its canonical softmax maximizer for
  a positive temperature parameter;
* core/canonical: the simplex owner `Δ[m]`, the entropy owner `normalizedEntropyProxFunction`, the
  positive smoothing-parameter owner `{μ : ℝ // 0 < μ}`, and `η`;
* bridge/view: the coordinate formulas for the objective and the softmax point.

Primitive data:
* the simplex dimension `m : ℕ+`;
* the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
* the score vector `s : EuclideanSpace ℝ (Fin (m : ℕ))`.

Derived API:
* the pointwise objective expansion;
* the softmax denominator and its positivity;
* the simplex-membership and coordinate formulas for the canonical softmax point;
* the maximality and value characterizations.

Source/core/bridge triage:
* source-facing: `entropyRegularizedSimplexObjective` and `entropySimplexSoftmax`;
* core/canonical: `Δ[m]`, `normalizedEntropyProxFunction`, `{μ : ℝ // 0 < μ}`, and
  `η`;
* bridge/view: the coordinate expansion lemmas in this file.
-/

/-- The entropy-regularized linear functional on the standard simplex `Δ_m` for a positive
smoothing parameter `μ`. The entropy term is carried by the canonical prox owner
`normalizedEntropyProxFunction`; the convention `0 \log 0 = 0` is realized by `Real.log 0 = 0`. -/
def entropyRegularizedSimplexObjective (μ : {μ : ℝ // 0 < μ}) (s : E) : Δ[m] → ℝ :=
  fun u ↦
    ∑ j : Fin (m : ℕ), u j * s j -
      (μ : ℝ) * normalizedEntropyProxFunction m u + (μ : ℝ) * Real.log (m : ℝ)

-- Proof sketch: unfold `entropyRegularizedSimplexObjective`.
/-- Evaluating `entropyRegularizedSimplexObjective m μ s` gives the coordinate formula
`∑_j u_j s_j - μ ∑_j u_j log u_j`. -/
theorem entropyRegularizedSimplexObjective_apply (μ : {μ : ℝ // 0 < μ}) (s : E) (u : Δ[m]) :
    entropyRegularizedSimplexObjective m μ s u =
      ∑ j : Fin (m : ℕ), u j * s j - (μ : ℝ) * ∑ j : Fin (m : ℕ), u j * Real.log (u j) := by
  rw [entropyRegularizedSimplexObjective, normalizedEntropyProxFunction_apply]
  ring

/-- The exponential denominator appearing in the positive-temperature softmax formula. -/
def entropySimplexSoftmaxDenominator (μ : {μ : ℝ // 0 < μ}) (s : E) : ℝ :=
  ∑ i : Fin (m : ℕ), Real.exp (s i / (μ : ℝ))

-- Proof sketch: every summand `Real.exp (s i / μ)` is strictly positive, and the finite index type
-- `Fin (m : ℕ)` is nonempty because `m : ℕ+`.
/-- The softmax denominator is strictly positive. -/
theorem entropySimplexSoftmaxDenominator_pos (μ : {μ : ℝ // 0 < μ}) (s : E) :
    0 < entropySimplexSoftmaxDenominator m μ s := sorry

-- Proof sketch: each coordinate of the displayed function is nonnegative because `Real.exp` is
-- positive, and the normalization by the denominator makes the coordinate sum equal to `1`.
/-- The normalized exponential weights define a point of the standard simplex. -/
theorem entropySimplexSoftmax_mem_stdSimplex (μ : {μ : ℝ // 0 < μ}) (s : E) :
    (fun j : Fin (m : ℕ) ↦
      Real.exp (s j / (μ : ℝ)) / entropySimplexSoftmaxDenominator m μ s) ∈
        Δ[m] := sorry

/-- The canonical softmax point in `Δ_m` associated to `s` and the positive smoothing parameter
`μ`. -/
def entropySimplexSoftmax (μ : {μ : ℝ // 0 < μ}) (s : E) : Δ[m] :=
  ⟨fun j : Fin (m : ℕ) ↦
      Real.exp (s j / (μ : ℝ)) / entropySimplexSoftmaxDenominator m μ s,
    entropySimplexSoftmax_mem_stdSimplex m μ s⟩

-- Proof sketch: unfold `entropySimplexSoftmax`.
/-- The coordinates of `entropySimplexSoftmax m μ s` are the normalized exponentials
`exp (s_j / μ) / \sum_i exp (s_i / μ)`. -/
theorem entropySimplexSoftmax_apply (μ : {μ : ℝ // 0 < μ}) (s : E) (j : Fin (m : ℕ)) :
    entropySimplexSoftmax m μ s j =
      Real.exp (s j / (μ : ℝ)) / entropySimplexSoftmaxDenominator m μ s := rfl

-- Proof sketch: use strict concavity of `u ↦ ∑_j u_j s_j - μ ∑_j u_j log u_j` on the simplex,
-- derive the first-order optimality equations with the simplex constraint, and solve them to get
-- the normalized exponential formula.
/-- Lemma 6.4: a simplex point maximizes the entropy-regularized linear functional exactly when it
is the canonical softmax point `u_μ(s)`. -/
lemma entropyRegularizedSimplexObjective_isMaxOn_iff
    (μ : {μ : ℝ // 0 < μ}) (s : E) (u : Δ[m]) :
    IsMaxOn (entropyRegularizedSimplexObjective m μ s) Set.univ u ↔
      u = entropySimplexSoftmax m μ s := sorry

-- Proof sketch: substitute the explicit softmax coordinates into the entropy term, rewrite
-- `log u_j = s_j / μ - log (∑_i exp (s_i / μ))`, and simplify.
/-- The softmax maximizer attains the log-sum-exp value
`μ \log (\sum_i \exp (s_i / μ))`. -/
theorem entropyRegularizedSimplexObjective_softmax_eq_value
    (μ : {μ : ℝ // 0 < μ}) (s : E) :
    entropyRegularizedSimplexObjective m μ s (entropySimplexSoftmax m μ s) =
      η μ s := sorry

end

end
