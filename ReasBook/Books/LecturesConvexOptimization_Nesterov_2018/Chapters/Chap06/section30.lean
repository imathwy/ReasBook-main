import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_30 (from Chap06) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The penalized dual maximand
`u ↦ ⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u)` appearing in the smoothed primal objective. -/
def smoothedPrimalObjectiveMaximand
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) (x : E₁) : E₂ → ℝ :=
  fun u ↦ A x u - hatφ u - μ₂ * d₂ u

/-- Definition 6.30: for a positive smoothing parameter `μ₂` and a prox-function `d₂` on `Q₂`,
`smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ x` is the smoothed primal objective
`f_{μ₂}(x) = \hat f(x) + max_{u ∈ Q₂} {⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u)}`, recorded in Lean as
`hatf x + sSup (...)`; this agrees with the displayed maximum whenever a maximizer exists. -/
def smoothedPrimalObjective
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂)
    (hatf : E₁ → ℝ) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) : E₁ → ℝ :=
  fun x ↦ hatf x + sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x '' Q₂)

-- Proof sketch: unfold `smoothedPrimalObjective`; the right-hand side is exactly the defining
-- formula `\hat f(x) + sup_{u ∈ Q₂} (⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u))`.
/-- Evaluating `smoothedPrimalObjective` recovers the defining sum of `\hat f(x)` and the
supremum of the penalized dual maximand over `Q₂`. -/
@[simp]
theorem smoothedPrimalObjective_apply
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂)
    (hatf : E₁ → ℝ) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) (x : E₁) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ x =
      hatf x + sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x '' Q₂) :=
  rfl

/-- The argmax set of the penalized dual maximand at `x`, encoding the admissible choices of the
textbook point `u_{μ₂}(x)` as feasible maximizers on `Q₂`. -/
abbrev smoothedPrimalObjectiveArgmax
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) :
    E₁ → Set E₂ :=
  fun x ↦ {u | u ∈ Q₂ ∧ IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x) Q₂ u}

-- Proof sketch: unfold `smoothedPrimalObjectiveArgmax`; membership is definitionally the
-- statement that `u` belongs to `Q₂` and maximizes the penalized dual maximand on `Q₂`.
/-- A point belongs to `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x` exactly when it lies in
the feasible argmax set of `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u)` over `Q₂`. -/
@[simp]
theorem mem_smoothedPrimalObjectiveArgmax_iff
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ)
    (x : E₁) (u : E₂) :
    u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x ↔
      u ∈ Q₂ ∧ IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x) Q₂ u :=
  Iff.rfl

end

/-! ### Proposition_6_30 (from Chap06) -/
noncomputable section

open scoped BigOperators
open scoped StandardSimplex

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (m : ℕ+)

local notation "S" => EuclideanSpace ℝ (Fin (m : ℕ))

/- Proposition 6.30 lies in the finite simplex / entropy-smoothing specialization domain.

Sampled owner declarations:
* `entropyRegularizedSimplexObjective` in `Chap06/Lemma_6_4`, the canonical entropy-regularized
  simplex objective;
* `entropySimplexSoftmax` and `entropySimplexSoftmax_apply` in `Chap06/Lemma_6_4`, the canonical
  softmax maximizer and its coordinate formula;
* `entropyRegularizedSimplexObjective_isMaxOn_iff` in `Chap06/Lemma_6_4`, the canonical owner
  theorem characterizing maximizers of the entropy-regularized simplex objective.

Best owner abstraction:
* source-facing: the entropy-regularized affine maximization problem on `Δ[m]`;
* core/canonical: `entropyRegularizedSimplexObjective m μ s`, `entropySimplexSoftmax m μ s`, and
  `entropyRegularizedSimplexObjective_isMaxOn_iff`;
* bridge/view: the affine score vector `s_j = f_j + ⟪g_j, xBar - x_j⟫`.

Primitive data:
* the positive smoothing parameter `μ₂`;
* the affine-score data `xBar`, `f`, `g`, and `points`.

Derived API:
* the source-facing affine score vector in `EuclideanSpace ℝ (Fin m)`;
* its coordinate evaluation lemma;
* the canonical softmax point in `Δ[m]`;
* the source proposition's maximality and uniqueness statement, obtained from the owner theorem
  `entropyRegularizedSimplexObjective_isMaxOn_iff`.

Source/core/bridge triage:
* source-facing: Proposition 6.30's unique-maximizer statement for the affine entropy-smoothed
  simplex problem;
* core/canonical: `entropyRegularizedSimplexObjective_isMaxOn_iff`;
* bridge/view: the affine score specialization below.

The built Chapter 6 owner API already characterizes entropy-regularized simplex maximizers via
`entropyRegularizedSimplexObjective_isMaxOn_iff`. This file therefore adds only the source-facing
affine score specialization and then states Proposition 6.30 directly in terms of that canonical
owner, instead of introducing a parallel packaged maximizer notion.
-/

/-- The affine score vector with coordinates `f_j + ⟪g_j, xBar - x_j⟫`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def entropyRegularizedAffineScores (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) : S :=
  (EuclideanSpace.equiv (Fin (m : ℕ)) ℝ).symm fun j ↦
    f j + inner ℝ (g j) (xBar - points j)

/-- Evaluating `entropyRegularizedAffineScores` recovers the coordinate formula
`f_j + ⟪g_j, xBar - x_j⟫`. -/
-- Proof sketch: unfold `entropyRegularizedAffineScores` and evaluate the coordinate `j` through
-- `EuclideanSpace.equiv`.
@[simp] theorem entropyRegularizedAffineScores_apply (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (j : Fin (m : ℕ)) :
    entropyRegularizedAffineScores m xBar f g points j =
      f j + inner ℝ (g j) (xBar - points j) := sorry

-- Proof sketch: apply the owner theorem
-- `entropyRegularizedSimplexObjective_isMaxOn_iff` to the affine score vector
-- `entropyRegularizedAffineScores m xBar f g points`. This identifies the canonical maximizer as
-- the corresponding softmax point, and the `iff` gives uniqueness of any other maximizer.
/-- Proposition 6.30 [Chapter6_1.json:99]: for the affine scores
`s_j = f_j + ⟪g_j, xBar - x_j⟫` and every `μ₂ > 0`, the problem
`max_{u ∈ Δ_m} {∑_j u_j s_j - μ₂ (log m + ∑_j u_j log u_j)}` is maximized by the canonical
softmax point, and every simplex maximizer equals that point. In particular, the maximizer is
unique and is given componentwise by the normalized exponential formula from
`entropySimplexSoftmax_apply`. -/
theorem entropyRegularizedAffineSimplexObjective_hasUniqueMaximizer
    {μ₂ : ℝ} (hμ₂ : 0 < μ₂) (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) :
    IsMaxOn
        (fun v : Δ[m] ↦
          (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
            μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j)))
        Set.univ
        (entropySimplexSoftmax m ⟨μ₂, hμ₂⟩
          (entropyRegularizedAffineScores m xBar f g points)) ∧
      ∀ u : Δ[m],
        IsMaxOn
            (fun v : Δ[m] ↦
              (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
                μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j)))
            Set.univ u →
          u = entropySimplexSoftmax m ⟨μ₂, hμ₂⟩
            (entropyRegularizedAffineScores m xBar f g points) := sorry

end
