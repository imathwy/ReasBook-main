import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_5 (from Chap06) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 6.5 lies in the chapter's structured primal-dual convex-objective domain.

Sampled owner-style declarations:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the exact chapter owner for the
  structured primal-dual data
- `StructuredObjectiveModel.objective` in `Chap06/Definition_6_6`, the canonical derived
  objective on the primal set
- `StructuredObjectiveModel.objective_apply` in `Chap06/Definition_6_6`, the exact source-facing
  evaluation formula
- `PrimalDualObjectiveModel` in `Chap06/Definition_6_28`, the later variant that adds
  nonemptiness hypotheses while already living at the same `NormedSpace` owner level

Best owner abstraction:
- source-facing/core: `StructuredObjectiveModel`
- bridge/view: the coercion from `StructuredObjectiveModel` to its objective function on
  `problem.primalSet`

Primitive data:
- the primal and dual feasible sets together with boundedness, closedness, and convexity
- the functions `smoothPart`, `dualPenalty`
- the linear map `linearMap`
- the continuity and convexity hypotheses for `smoothPart` and `dualPenalty`

Derived API:
- `StructuredObjectiveModel.maximand`
- `StructuredObjectiveModel.objective`
- the coercion to `problem.primalSet → EReal`
- `StructuredObjectiveModel.objective_apply`

Source/core/bridge triage:
- source-facing: `StructuredObjectiveModel`
- core/canonical: the same owner already introduced in `Definition_6_6`
- bridge/view: the objective coercion and the evaluation theorem

The owner abstraction already exists in `Definition_6_6`, so this item should be a direct
recall surface rather than a duplicate local structure. The textbook formula for `f` is then
recovered through the owner objective and its evaluation theorem.
-/

section

/- Definition 6.5: a structured objective model consists of bounded closed convex sets
`Q₁ ⊆ E₁` and `Q₂ ⊆ E₂`, continuous convex functions `\hat f` and `\hat φ`, and a linear
operator `A : E₁ → E₂*`; the associated primal objective is encoded by the recalled chapter
owner and its derived objective API. -/
recall StructuredObjectiveModel (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] :
    Type (max u v)

/- The source-facing primal objective attached to a structured model is the direct owner API. -/
recall StructuredObjectiveModel.objective
    (problem : StructuredObjectiveModel E₁ E₂) : problem.primalSet → EReal

/- The textbook evaluation formula is the direct recall of the owner theorem. -/
recall StructuredObjectiveModel.objective_apply
    (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.objective x =
      sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))

end

end

/-! ### Lemma_6_5 (from Chap06) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 6.5 lies in the affine variational-inequality / gap-function domain.

Sampled owner-style declarations:
- `AffineVariationalInequalityProblem.IsSolution` in `Chap06/Definition_6_17`, the chapter owner
  for the source-facing variational-inequality predicate;
- `AffineVariationalInequalityProblem.gapFunction` in `Chap06/Definition_6_18`, the chapter owner
  for the associated gap function on the feasible subtype;
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizer owner used across the project;
- `argmin[Q]` in `Chap01/Definition_1_3_3`, the chapter minimizer-set owner derived from
  `IsMinOn`.

Best owner abstraction:
- source-facing: `problem.IsSolution wStar`;
- core/canonical: `problem.gapFunction` together with `IsMinOn`;
- bridge/view: the equivalence between the source-facing solution predicate and minimizing the
  canonical gap function on the feasible subtype.

Primitive data:
- `problem : AffineVariationalInequalityProblem E`.

Derived API:
- the minimization statement `IsMinOn problem.gapFunction Set.univ wStar`;
- the zero-gap consequence at a solution or a minimizer.

Source/core/bridge triage:
- source-facing: Lemma 6.5 itself, relating the textbook variational inequality to gap
  minimization;
- core/canonical: `AffineVariationalInequalityProblem E`, `gapFunction`, and `IsMinOn`;
- bridge/view: the theorem below, written on the feasible subtype rather than rebuilding an
  ambient supremum functional.

The previous revision introduced a parallel ambient `ℝ`-valued gap-supremum owner. This file now
states Lemma 6.5 directly on the chapter owner `AffineVariationalInequalityProblem`, keeping only
the canonical gap-function minimization surface and its zero-gap consequences.
-/

namespace AffineVariationalInequalityProblem

/-- Lemma 6.5: a feasible point solves the affine variational inequality problem exactly when it
minimizes the associated canonical gap function on the feasible subtype. -/
theorem isSolution_iff_isMinOn_gapFunction
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet) :
    problem.IsSolution wStar ↔ IsMinOn problem.gapFunction Set.univ wStar := sorry

/-- Every minimizer of the canonical gap function has gap value `0`. -/
theorem gapFunction_eq_zero_of_isMinOn
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet)
    (hmin : IsMinOn problem.gapFunction Set.univ wStar) :
    problem.gapFunction wStar = 0 := sorry

/-- Every solution of an affine variational inequality problem has gap value `0`. -/
theorem gapFunction_eq_zero_of_isSolution
    (problem : AffineVariationalInequalityProblem E) (wStar : problem.feasibleSet)
    (hsol : problem.IsSolution wStar) :
    problem.gapFunction wStar = 0 := sorry

end AffineVariationalInequalityProblem

end

/-! ### Proposition_6_5 (from Chap06) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p]

/- Proposition 6.5 lies in the chapter's prox-function / prox-center quadratic-growth domain.

Sampled owner declarations in this domain:
- `IsProxFunction` in `Definition_6_31`, the chapter owner for prox-function data;
- `IsProxCenter` in `Definition_6_31`, the chapter owner for normalized prox-center data;
- `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Definition_2_14`, the
  canonical quadratic-growth theorem behind the prox-center lower bound.

Best owner abstraction:
- source-facing: the normalized prox-center lower bound;
- core/canonical: `IsProxFunction p Q₂ d₂`, `IsProxCenter Q₂ d₂ u₀`, and the owner theorem
  `prox_center_quadratic_lower_bound`;
- bridge/view: `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`.

Primitive data:
- the prox-function owner `hd₂ : IsProxFunction p Q₂ d₂`;
- the prox-center owner `hu₀ : IsProxCenter Q₂ d₂ u₀`;
- the feasible comparison point `u ∈ Q₂`.

Derived API:
- `hd₂.strongConvexOnWith`;
- `hu₀.mem`, `hu₀.isMinOn`, and `hu₀.value_eq_zero`;
- the quadratic lower bound itself.

The previous version duplicated the proposition theorem upstream in `Definition_6_31`, which left
the chapter with two owners of the same global declaration name. This file now restores the
numbered proposition as the sole owner of the lower bound, while `Definition_6_31` keeps only the
prox-function and prox-center data.
-/

section

variable {Q₂ : Set E} {d₂ : E → ℝ} {u₀ u : E}

/- Proposition 6.5: a normalized prox-center of a prox-function on `Q₂` gives the lower bound
`d₂ u ≥ (1 / 2) p(u - u₀)^2` at every feasible point `u ∈ Q₂`. -/
theorem prox_center_quadratic_lower_bound
    (hd₂ : IsProxFunction p Q₂ d₂)
    (hu₀ : IsProxCenter Q₂ d₂ u₀)
    (hu : u ∈ Q₂) :
    d₂ u ≥ (1 / 2 : ℝ) * (p (u - u₀)) ^ (2 : ℕ) := by
  have hquad :
      d₂ u ≥ d₂ u₀ + (1 / 2 : ℝ) * (p (u - u₀)) ^ (2 : ℕ) :=
    hd₂.strongConvexOnWith.quadratic_growth_of_isMinOn_of_mem hu₀.mem hu₀.isMinOn u hu
  simpa [hu₀.value_eq_zero] using hquad

end

/-! ### Theorem_6_5 (from Chap06) -/
section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

-- Proof sketch: rewrite `τ k` as
-- `(α (k - 1) - α (k + 1)) / α (k - 1)`, square to obtain the left-hand side as
-- `(α (k + 1) - α (k - 1)) ^ 2 / (α (k - 1)) ^ 2`, substitute
-- `λ₁ k * λ₂ k = α k * α (k - 1)`, and clear the positive denominator `(α (k - 1)) ^ 2`.
/-- Theorem 6.5: for a fixed index `k`, if
`α_{k-1} ≠ 0`, `λ₁,k λ₂,k = α_k α_{k-1}`, and
`τ_k = 1 - α_{k+1} / α_{k-1}`, then the step-size inequality
`τ_k^2 ≤ (α_{k+1} / α_{k-1}) λ₁,k λ₂,k` is equivalent to the three-term inequality
`(α_{k+1} - α_{k-1})^2 ≤ α_{k+1} α_k α_{k-1}^2`. -/
theorem tau_square_bound_iff_alpha_three_term_inequality
    (α : Set.Ici (-1 : ℤ) → 𝕜) (lambda₁ lambda₂ τ : ℕ → 𝕜) (k : ℕ)
    (hα_pred_ne : α (switching_parameters_pred_index k) ≠ 0)
    (hprod : lambda₁ k * lambda₂ k =
      α (switching_parameters_curr_index k) * α (switching_parameters_pred_index k))
    (hτ : τ k = 1 - α (switching_parameters_succ_index k) / α (switching_parameters_pred_index k)) :
    τ k ^ (2 : ℕ) ≤
        (α (switching_parameters_succ_index k) / α (switching_parameters_pred_index k)) *
          (lambda₁ k * lambda₂ k) ↔
      (α (switching_parameters_succ_index k) - α (switching_parameters_pred_index k)) ^ (2 : ℕ) ≤
        α (switching_parameters_succ_index k) * α (switching_parameters_curr_index k) *
          (α (switching_parameters_pred_index k)) ^ (2 : ℕ) := by
  let aPred : 𝕜 := α (switching_parameters_pred_index k)
  let aCurr : 𝕜 := α (switching_parameters_curr_index k)
  let aSucc : 𝕜 := α (switching_parameters_succ_index k)
  have haPred_ne : aPred ≠ 0 := by
    simpa [aPred] using hα_pred_ne
  change τ k ^ (2 : ℕ) ≤ (aSucc / aPred) * (lambda₁ k * lambda₂ k) ↔
      (aSucc - aPred) ^ (2 : ℕ) ≤ aSucc * aCurr * aPred ^ (2 : ℕ)
  have hτ_sq :
      τ k ^ (2 : ℕ) = (aSucc - aPred) ^ (2 : ℕ) / aPred ^ (2 : ℕ) := by
    rw [hτ]
    simp only [aPred, aSucc]
    field_simp [haPred_ne]
    ring
  have hprod' : lambda₁ k * lambda₂ k = aCurr * aPred := by
    simpa [aCurr, aPred] using hprod
  rw [hτ_sq, hprod']
  have haPred_sq_pos : 0 < aPred ^ (2 : ℕ) := by
    simpa using sq_pos_of_ne_zero haPred_ne
  rw [div_le_iff₀ haPred_sq_pos]
  field_simp [haPred_ne]

end
