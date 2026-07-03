import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_29 (from Chap06) -/
/- Definition 6.29 lies in the chapter's prox-function / prox-center domain.

Sampled owner-style declarations:
- `IsProxFunction` in `Definition_6_31`, the chapter's canonical owner for the
  prox-function hypothesis on `d`;
- `IsProxCenter` in `Definition_6_31`, the chapter's canonical owner for the
  normalized prox-center condition;
- project `StrongConvexOnWith`, the chapter owner reused by `IsProxFunction`;
- mathlib `IsMinOn`, the ambient minimizer owner reused by `IsProxCenter`.

Best owner abstraction:
- source-facing: the prox-function condition on `Q` and the normalized
  prox-center condition at `x₀`;
- core/canonical: `IsProxFunction Q d` and `IsProxCenter Q d x₀`;
- bridge/view: this numbered item is a recall-only surface for those canonical
  owners rather than a second pair of duplicate local definitions.

Primitive data:
- the norm-like seminorm `p`, the feasible set `Q`, the prox-function
  candidate `d`, and the candidate center `x₀`.

Derived API:
- `IsProxFunction.continuousOn` and `IsProxFunction.strongConvexOnWith`;
- `IsProxCenter.mem`, `IsProxCenter.isMinOn`, and
  `IsProxCenter.value_eq_zero`.

The previous version duplicated the prox owners with the separate public names
`is_prox_function_on` and `is_prox_center_on`. Those notions already have a
canonical chapter owner in `Definition_6_31`, so this file now keeps only the
direct recall surface.
-/

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (p : Seminorm ℝ E) [Seminorm.IsNorm p]

variable (Q : Set E) (d : E → ℝ) (x₀ : E)

/- Definition 6.29 uses the chapter's canonical prox-function owner and the
canonical normalized prox-center owner. -/
recall IsProxFunction
recall IsProxFunction.continuousOn
recall IsProxFunction.strongConvexOnWith
recall IsProxCenter
recall IsProxCenter.mem
recall IsProxCenter.isMinOn
recall IsProxCenter.value_eq_zero

set_option linter.hashCommand false in
#check IsProxFunction p Q d

set_option linter.hashCommand false in
#check IsProxCenter Q d x₀

end

/-! ### Proposition_6_29 (from Chap06) -/
noncomputable section

open scoped BigOperators
open scoped StandardSimplex

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (m : ℕ+)

local notation "S" => EuclideanSpace ℝ (Fin (m : ℕ))

/- Proposition 6.29 lies in the finite simplex / entropy-smoothing specialization domain.

Sampled owner declarations:
* mathlib `stdSimplex`, via the chapter notation `Δ[m]` from `Definition_6_11`;
* `normalizedEntropyProxFunction` in `Definition_6_14`, the entropy prox owner on `Δ[m]`;
* `entropyRegularizedSimplexObjective` in `Lemma_6_4`, the canonical entropy-regularized simplex
  objective for a positive temperature and a score vector;
* `entropySimplexSoftmax` and `entropyRegularizedSimplexObjective_isMaxOn_iff` in `Lemma_6_4`,
  the canonical softmax maximizer and its maximality characterization.

Best owner abstraction:
* source-facing: the affine score vector `s_j = f_j + ⟪g_j, xBar - x_j⟫`;
* core/canonical: `entropyRegularizedSimplexObjective m μ s` and `entropySimplexSoftmax m μ s`;
* bridge/view: specializing those owners to `entropyRegularizedAffineScores m xBar f g points`.

Primitive data:
* the affine-score data `xBar : E`, `f`, `g : Fin m → E`, and `points : Fin m → E`.

Derived API:
* the Chapter 6 entropy-regularized simplex objective specialized to the affine score vector;
* the corresponding canonical softmax point and its coordinate formula;
* the source proposition's `IsMaxOn` statement, obtained from the owner theorem after removing the
  source's additive constant `μ₂ log m`.
-/

/-- The affine score vector with coordinates `f_j + ⟪g_j, xBar - x_j⟫` on a real inner-product
space. The textbook `ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def entropyRegularizedAffineScores (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) : S :=
  (EuclideanSpace.equiv (Fin (m : ℕ)) ℝ).symm fun j ↦
    f j + inner ℝ (g j) (xBar - points j)

/-- Evaluating `entropyRegularizedAffineScores` recovers the coordinate formula
`f_j + ⟪g_j, xBar - x_j⟫`. -/
@[simp] theorem entropyRegularizedAffineScores_apply (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (j : Fin (m : ℕ)) :
    entropyRegularizedAffineScores m xBar f g points j =
      f j + inner ℝ (g j) (xBar - points j) := by
  simp [entropyRegularizedAffineScores]

/-- Evaluating the canonical entropy-regularized simplex owner at the affine score vector gives
the entropy-smoothed affine formula without the additive constant `μ₂ log m`. -/
theorem entropyRegularizedAffineSimplexObjective_apply
    {μ₂ : ℝ} (hμ₂ : 0 < μ₂) (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (u : Δ[m]) :
    entropyRegularizedSimplexObjective m ⟨μ₂, hμ₂⟩
      (entropyRegularizedAffineScores m xBar f g points) u =
        (∑ j : Fin (m : ℕ), u j * (f j + inner ℝ (g j) (xBar - points j))) -
          μ₂ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) := by
  simp [entropyRegularizedSimplexObjective_apply, entropyRegularizedAffineScores]

/-- The coordinates of the canonical softmax point attached to the affine score vector are the
normalized exponentials `exp (s_j / μ₂) / \sum_l exp (s_l / μ₂)`. -/
theorem entropyRegularizedAffineSimplexSoftmax_apply
    {μ₂ : ℝ} (hμ₂ : 0 < μ₂) (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (j : Fin (m : ℕ)) :
    entropySimplexSoftmax m ⟨μ₂, hμ₂⟩ (entropyRegularizedAffineScores m xBar f g points) j =
      Real.exp ((f j + inner ℝ (g j) (xBar - points j)) / μ₂) /
        ∑ l : Fin (m : ℕ), Real.exp ((f l + inner ℝ (g l) (xBar - points l)) / μ₂) := by
  simp [entropySimplexSoftmax_apply, entropySimplexSoftmaxDenominator,
    entropyRegularizedAffineScores]

/-- Proposition 6.29: a simplex point maximizes the entropy-regularized affine objective exactly
when it is the canonical softmax point with coordinates
`exp (s_j / μ₂) / \sum_l exp (s_l / μ₂)`, where `s_j = f_j + ⟪g_j, xBar - x_j⟫`. -/
theorem entropyRegularizedAffineSimplexObjective_isMaxOn_iff
    {μ₂ : ℝ} (hμ₂ : 0 < μ₂) (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (u : Δ[m]) :
    IsMaxOn
        (fun v : Δ[m] ↦
          (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
            μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j)))
        Set.univ u ↔
      u = entropySimplexSoftmax m ⟨μ₂, hμ₂⟩ (entropyRegularizedAffineScores m xBar f g points) := by
  let μ : {μ : ℝ // 0 < μ} := ⟨μ₂, hμ₂⟩
  let s : S := entropyRegularizedAffineScores m xBar f g points
  have hshift :
      IsMaxOn (fun v : Δ[m] ↦ entropyRegularizedSimplexObjective m μ s v - μ₂ * Real.log (m : ℝ))
        Set.univ u ↔
        IsMaxOn (entropyRegularizedSimplexObjective m μ s) Set.univ u := by
    constructor
    · intro h
      simpa [sub_eq_add_neg] using
        h.add (isMaxOn_const : IsMaxOn (fun _ : Δ[m] ↦ μ₂ * Real.log (m : ℝ)) Set.univ u)
    · intro h
      simpa using
        h.sub (isMinOn_const : IsMinOn (fun _ : Δ[m] ↦ μ₂ * Real.log (m : ℝ)) Set.univ u)
  have hsource :
      (fun v : Δ[m] ↦
        (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
          μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j))) =
        fun v : Δ[m] ↦ entropyRegularizedSimplexObjective m μ s v - μ₂ * Real.log (m : ℝ) := by
    funext v
    rw [entropyRegularizedAffineSimplexObjective_apply]
    ring
  rw [hsource, hshift]
  simpa [μ, s] using entropyRegularizedSimplexObjective_isMaxOn_iff m μ s u

end
