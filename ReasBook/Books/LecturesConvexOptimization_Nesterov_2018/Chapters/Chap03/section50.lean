import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_50 (from Chap03) -/
open Set Metric

variable {E : Type*} [PseudoMetricSpace E]

/- This item lies in the chapter's interior-point domain.

Sampled owner-style declarations:
- `Set.interior`, the canonical topological owner of interior points;
- `mem_interior`, the owner theorem exposing interior membership by an open subset;
- `Metric.mem_nhds_iff`, the metric-space owner theorem turning neighborhood membership into
  contained-ball data;
- `exists_ball_subset_effectiveDomain_of_mem_interior` in `Theorem_3_1_11`, the chapter's earlier
  source-facing effective-domain specialization of the same topological owner abstraction;
- `exists_hard_feasibility_problem_for_short_separation_oracle_algorithms` in `Theorem_3_49`,
  whose hard-instance conclusion reuses the same owner predicate downstream in the chapter.

Best abstraction triage:
- source-facing: the canonical interior-nonemptiness predicate attached to `S`;
- core/canonical: `(interior S).Nonempty`;
- bridge/view: `interior_ball_assumption_iff_interior_nonempty`, identifying the textbook
  interior-ball formulation with the owner predicate.

Primitive data:
- the set `S ⊆ E`.

Derived API:
- the textbook interior-ball existential, derived from metric openness of `interior S`;
- center membership in `S`, derived from `0 < ε` and `Metric.ball xStar ε ⊆ S`;
- the bridge equivalence between the textbook ball condition and the owner predicate.

Source/core/bridge triage:
- source-facing: `(interior S).Nonempty`;
- core/canonical: `Set.interior`;
- bridge/view: `interior_ball_assumption_iff_interior_nonempty`.

This file therefore keeps the owner predicate itself as the main numbered recall, and records the
textbook ball formulation only as a companion bridge theorem. -/

section

variable (S : Set E)

/-
Definition 3.50: a set satisfies the interior ball assumption exactly when it has a nonempty
interior. The textbook Euclidean-ball formulation is recorded below as a bridge theorem, while the
main owner expression is the canonical predicate `(interior S).Nonempty`.
-/
#check (interior S).Nonempty

/-- The textbook interior-ball formulation is equivalent to the canonical owner predicate
`(interior S).Nonempty`. -/
-- Proof sketch: translate interior membership to neighborhood membership by
-- `mem_interior_iff_mem_nhds`, then use `Metric.mem_nhds_iff` to pass between neighborhoods and
-- contained positive-radius balls.
theorem interior_ball_assumption_iff_interior_nonempty :
    (∃ xStar : E, ∃ ε > 0, ball xStar ε ⊆ S) ↔ (interior S).Nonempty := by
  constructor
  · rintro ⟨xStar, ε, hε, hball⟩
    refine ⟨xStar, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    exact Metric.mem_nhds_iff.mpr ⟨ε, hε, hball⟩
  · rintro ⟨xStar, hxStar⟩
    rw [mem_interior_iff_mem_nhds] at hxStar
    rcases Metric.mem_nhds_iff.mp hxStar with ⟨ε, hε, hball⟩
    exact ⟨xStar, ε, hε, hball⟩

end

/-! ### Proposition_3_50 (from Chap03) -/
noncomputable section

universe u

open Set
open scoped LevelMethodNotation

variable {α : Type u}

/- Proposition 3.50 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner object for explicit real scalar sequences
  `(\hat f_k^*, f_k^*)`
* `LevelMethodHistory.gap`, `LevelMethodHistory.levelValue`, and
  `LevelMethodHistory.valueInterval` in `Lemma_3_3_1`, the derived owner API for
  `δ_k`, `ℓ_k(α)`, and `Δ_k`
* `bestFunctionValueUpTo` and `bestFunctionValueUpTo_antitone_step` in `Definition_3_55`, the
  chapter owner API for sampled prefix minima
* `SetConstrainedMinimizationProblem.optimalValue`,
  `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image`,
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, and
  `SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet` in
  `Chap01/Definition_1_3_7`, the project owner API for exact constrained minima, faithfully
  valued in `EReal`

Best owner abstraction:
* source-facing: the exact constrained model problem at step `k` and the sampled prefix minimum
  `f_k^*`
* core/canonical: `SetConstrainedMinimizationProblem.optimalValue`, `LevelMethodHistory`, and
  `bestFunctionValueUpTo`
* bridge/view: the explicit real-history bridge
  `levelMethodHistoryFromApproximateValues hatf f xSeq`, together with its attained-minimum
  specialization `levelMethodHistoryFromApproximateValues (fun k ↦ model k (xHat k)) f xSeq`

Primitive data:
* the feasible set `Q`
* the model family `model`
* the objective `f`
* the sample sequence `xSeq`

Derived API:
* the canonical exact lower value
  `(levelMethodApproximateProblem Q model k).optimalValue`
* the explicit real-history bridge `levelMethodHistoryFromApproximateValues hatf f xSeq`
* the attained-minimum specialization
  `levelMethodHistoryFromApproximateValues (fun k ↦ model k (xHat k)) f xSeq`
* the stepwise monotonicity and gap comparisons for pointwise monotone models

Source/core/bridge triage:
* source-facing: Proposition 3.50 and the textbook chain
  `\hat f_k^* ≤ \hat f_{k+1}^* ≤ f_{k+1}^* ≤ f_k^*`
* core/canonical: the `EReal` owner
  `(levelMethodApproximateProblem Q model k).optimalValue` together with
  `bestFunctionValueUpTo`
* bridge/view: explicit real lower-value histories
  `levelMethodHistoryFromApproximateValues hatf f xSeq` equipped with an exactness certificate to
  the canonical `EReal` owner; the attained-minimum specialization uses the same bridge with
  `hatf k = model k (xHat k)`

The refinement therefore moves the exact lower-value owner to
`SetConstrainedMinimizationProblem.optimalValue : EReal`. Real `LevelMethodHistory` objects are no
longer built unconditionally from the raw real infimum `⨅ x : Q, model k x`; instead they are
exposed only from explicit real lower-value data, together with bridge theorems relating those
data to the canonical `EReal` owner. Accordingly, the source-faithful stepwise order statement is
first proved on the canonical `EReal` owner, then transferred to arbitrary explicit real lower
values through an exactness certificate; the attained-minimum history is only a corollary.
-/

/-- The exact constrained model problem at step `k`, obtained by minimizing the model
`x ↦ model k x` over the feasible set `Q`. -/
abbrev levelMethodApproximateProblem
    (Q : Set α) (model : ℕ → α → ℝ) (k : ℕ) :
    SetConstrainedMinimizationProblem α :=
  .mk Q (model k)

/-- Explicit real scalar history attached to prescribed lower values `\hat f_k^*` and sampled
objective values. The mathematically faithful exact lower values remain the canonical `EReal`
owners `(levelMethodApproximateProblem Q model k).optimalValue`; this constructor is only the
real-history bridge used once those lower values have been supplied explicitly. -/
def levelMethodHistoryFromApproximateValues
    (approximateOptimalValue : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α) :
    LevelMethodHistory where
  approximateOptimalValue := approximateOptimalValue
  optimalValue k := bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k

/-- The lower coordinate of `levelMethodHistoryFromApproximateValues` is the supplied real lower
value. -/
theorem levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq
    (approximateOptimalValue : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α) (k : ℕ) :
    (levelMethodHistoryFromApproximateValues approximateOptimalValue f xSeq).approximateOptimalValue
        k =
      approximateOptimalValue k := rfl

/- The record value in `levelMethodHistoryFromApproximateValues` is the earlier chapter owner
`bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k` for the sampled minimum among `x₀, …, x_k`. -/
theorem levelMethodHistoryFromApproximateValues_optimalValue_eq
    (approximateOptimalValue : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α) (k : ℕ) :
    (levelMethodHistoryFromApproximateValues approximateOptimalValue f xSeq).optimalValue k =
      bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k := rfl

/-- If the supplied real lower values are exact, then the lower coordinate of
`levelMethodHistoryFromApproximateValues` agrees with the canonical `EReal` model minimum. -/
theorem levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
    (Q : Set α) (model : ℕ → α → ℝ) (hatf : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α)
    (hhat :
      ∀ k : ℕ, ((hatf k : ℝ) : EReal) = (levelMethodApproximateProblem Q model k).optimalValue)
    (k : ℕ) :
    (((levelMethodHistoryFromApproximateValues hatf f xSeq).approximateOptimalValue k : ℝ) :
        EReal) =
      (levelMethodApproximateProblem Q model k).optimalValue := by
  simpa [levelMethodHistoryFromApproximateValues] using hhat k

/-- The attained-minimum specialization of `levelMethodHistoryFromApproximateValues` agrees with
the canonical `EReal` lower-value owner at each step, provided the chosen sequence `xHat` really
minimizes each model on `Q`. -/
theorem levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
    (Q : Set α) (model : ℕ → α → ℝ) (f : α → ℝ) (xSeq xHat : ℕ → α)
    (hxHat_mem : ∀ k : ℕ, xHat k ∈ Q)
    (hxHat_min : ∀ k : ℕ, IsMinOn (model k) Q (xHat k))
    (k : ℕ) :
    ((LevelMethodHistory.approximateOptimalValue
        (levelMethodHistoryFromApproximateValues (fun i ↦ model i (xHat i)) f xSeq)
        k : ℝ) : EReal) =
      (levelMethodApproximateProblem Q model k).optimalValue := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      ((levelMethodApproximateProblem Q model j).optimalValue_eq_of_isMinOn
        (hxHat_mem j)
        (hxHat_min j)).symm
  simpa using
    levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model (fun i ↦ model i (xHat i)) f xSeq hhat k

section

variable {Q : Set α} {model : ℕ → α → ℝ}

/-- Pointwise monotonicity of the model family makes the canonical exact lower values monotone. -/
theorem levelMethodApproximateProblem_optimalValue_mono_of_pointwiseModelMono
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    (levelMethodApproximateProblem Q model k).optimalValue ≤
      (levelMethodApproximateProblem Q model (k + 1)).optimalValue := by
  simpa [levelMethodApproximateProblem] using
    (SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      (levelMethodApproximateProblem Q model k)
      (levelMethodApproximateProblem Q model (k + 1))
      rfl
      (hmono k))

section History

variable (f : α → ℝ) (xSeq : ℕ → α)

/-- If every model is an underestimator on `Q`, then each canonical exact lower value is bounded
above by the best sampled objective value. This is stated first on the faithful `EReal` owner. -/
theorem levelMethodApproximateProblem_optimalValue_le_bestFunctionValueUpTo_of_underestimator
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (k : ℕ) :
    (levelMethodApproximateProblem Q model k).optimalValue ≤
      (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k : EReal) := by
  obtain ⟨j, hj⟩ := bestFunctionValueUpTo_exists_eq (fun i ↦ f (xSeq i)) k
  have hsample :
      (levelMethodApproximateProblem Q model k).optimalValue ≤ (f (xSeq j) : EReal) := by
    have hmodel :
        (levelMethodApproximateProblem Q model k).optimalValue ≤ model k (xSeq j) :=
      (levelMethodApproximateProblem Q model k).optimalValue_le_of_mem_feasibleSet (hxSeq j)
    refine hmodel.trans ?_
    exact_mod_cast hunder k (xSeq j) (hxSeq j)
  have hj' :
      (f (xSeq j) : EReal) =
        (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k : EReal) := by
    exact_mod_cast hj
  exact hsample.trans_eq hj'

/-- Proposition 3.50, canonical form: the source-faithful stepwise order chain is stated on the
exact lower-value owner in `EReal`, so no extra attainment hypothesis is needed to express the
model lower values faithfully. -/
theorem levelMethodApproximateProblem_optimalValue_stepwiseBounds_of_monotoneUnderestimators
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    (levelMethodApproximateProblem Q model k).optimalValue ≤
      (levelMethodApproximateProblem Q model (k + 1)).optimalValue ∧
      (levelMethodApproximateProblem Q model (k + 1)).optimalValue ≤
        (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) : EReal) ∧
      (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) : EReal) ≤
        bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k := by
  have hoptimal :
      bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
        bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k :=
    bestFunctionValueUpTo_antitone_step k
  refine ⟨?_, ?_, ?_⟩
  · exact levelMethodApproximateProblem_optimalValue_mono_of_pointwiseModelMono hmono k
  · exact
      levelMethodApproximateProblem_optimalValue_le_bestFunctionValueUpTo_of_underestimator
        f xSeq hxSeq hunder (k + 1)
  · exact_mod_cast hoptimal

section ExplicitHistory

variable (hatf : ℕ → ℝ)

local notation "history" =>
  (levelMethodHistoryFromApproximateValues hatf f xSeq : LevelMethodHistory)

/-- Under the exactness certificate `hhat`, pointwise monotonicity of the model family makes the
explicit real lower coordinates monotone. -/
theorem levelMethodHistoryFromApproximateValues_approximateOptimalValue_mono_of_pointwiseModelMono
    (hhat :
      ∀ j : ℕ, ((hatf j : ℝ) : EReal) = (levelMethodApproximateProblem Q model j).optimalValue)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) := by
  have hmonoE :
      (levelMethodApproximateProblem Q model k).optimalValue ≤
        (levelMethodApproximateProblem Q model (k + 1)).optimalValue :=
    levelMethodApproximateProblem_optimalValue_mono_of_pointwiseModelMono hmono k
  rw [← levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model hatf f xSeq hhat k,
    ← levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model hatf f xSeq hhat (k + 1)] at hmonoE
  exact_mod_cast hmonoE

/-- Under the exactness certificate `hhat`, every model underestimator is bounded above by the
best sampled objective value in the explicit real history. -/
theorem
    levelMethodHistoryFromApproximateValues_fhat_le_fstar_of_underestimator
    (hhat :
      ∀ j : ℕ, ((hatf j : ℝ) : EReal) = (levelMethodApproximateProblem Q model j).optimalValue)
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (k : ℕ) :
    fhat(history, k) ≤ fstar(history, k) := by
  have hle :
      (levelMethodApproximateProblem Q model k).optimalValue ≤
        (fstar(history, k) : EReal) := by
    simpa [levelMethodHistoryFromApproximateValues] using
      (levelMethodApproximateProblem_optimalValue_le_bestFunctionValueUpTo_of_underestimator
        f xSeq hxSeq hunder k)
  rw [← levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model hatf f xSeq hhat k] at hle
  exact_mod_cast hle

/-- Proposition 3.50, source-facing real-history form: if the supplied lower values are exact,
then the textbook chain `\hat f_k^* ≤ \hat f_{k+1}^* ≤ f_{k+1}^* ≤ f_k^*` holds for
`levelMethodHistoryFromApproximateValues hatf f xSeq`. -/
theorem levelMethodHistoryFromApproximateValues_stepwiseBounds_of_monotoneUnderestimators
    (hhat :
      ∀ j : ℕ, ((hatf j : ℝ) : EReal) = (levelMethodApproximateProblem Q model j).optimalValue)
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) ∧
      fhat(history, (k + 1)) ≤ fstar(history, (k + 1)) ∧
      fstar(history, (k + 1)) ≤ fstar(history, k) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      levelMethodHistoryFromApproximateValues_approximateOptimalValue_mono_of_pointwiseModelMono
        f xSeq hatf hhat hmono k
  · exact
      levelMethodHistoryFromApproximateValues_fhat_le_fstar_of_underestimator
        f xSeq hatf hhat hxSeq hunder
        (k + 1)
  · simpa [levelMethodHistoryFromApproximateValues] using
      (show bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
          bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k from
        bestFunctionValueUpTo_antitone_step k)

end ExplicitHistory

section AttainedHistory

variable (xHat : ℕ → α)

local notation "history" =>
  levelMethodHistoryFromApproximateValues (fun i ↦ model i (xHat i)) f xSeq

/-- Companion bridge: under an explicit minimizing sequence `xHat`, pointwise monotonicity of the
model family makes the attained real lower coordinates monotone. -/
theorem attainedApproximateOptimalValue_mono_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
        Q model f xSeq xHat hxHat_mem hxHat_min j
  simpa using
    levelMethodHistoryFromApproximateValues_approximateOptimalValue_mono_of_pointwiseModelMono
      f xSeq (fun i ↦ model i (xHat i)) hhat hmono k

/-- Companion bridge: under an explicit minimizing sequence `xHat`, every model underestimator is
bounded above by the best sampled objective value in the attained real history. -/
theorem attainedApproximateOptimalValue_le_optimalValue_of_underestimator
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (k : ℕ) :
    fhat(history, k) ≤ fstar(history, k) := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
        Q model f xSeq xHat hxHat_mem hxHat_min j
  simpa using
    levelMethodHistoryFromApproximateValues_fhat_le_fstar_of_underestimator
      f xSeq (fun i ↦ model i (xHat i)) hhat hxSeq hunder
      k

/-- Companion bridge: under an explicit minimizing sequence `xHat`, the interval inclusion
`Δ_{k+1} ⊆ Δ_k` follows from pointwise monotonicity of the models. The underestimator hypothesis
from the textbook is redundant for this conclusion. -/
theorem attainedValueInterval_subset_step_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    Δ[history]((k + 1)) ⊆ Δ[history](k) := by
  intro t ht
  rw [LevelMethodHistory.mem_valueInterval_iff] at ht ⊢
  refine ⟨?_, ?_⟩
  · exact le_trans
      (attainedApproximateOptimalValue_mono_of_pointwiseModelMono
        f xSeq xHat hxHat_mem hxHat_min hmono k)
      ht.1
  · exact le_trans ht.2 <|
      by
        simpa using
          (show bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
              bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k from
            bestFunctionValueUpTo_antitone_step k)

/-- Companion bridge: under an explicit minimizing sequence `xHat`, the level-method gap
`δ_k = f_k^* - \hat f_k^*` decreases from step `k` to step `k + 1` under pointwise monotone
models. The underestimator hypothesis is redundant for this conclusion. -/
theorem attainedGap_antitone_step_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    δ[history]((k + 1)) ≤ δ[history](k) := by
  have hoptimal :
      fstar(history, (k + 1)) ≤ fstar(history, k) := by
    simpa using
      (show bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
          bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k from
        bestFunctionValueUpTo_antitone_step k)
  rw [LevelMethodHistory.gap_eq_sub, LevelMethodHistory.gap_eq_sub]
  linarith [attainedApproximateOptimalValue_mono_of_pointwiseModelMono
    f xSeq xHat hxHat_mem hxHat_min hmono k, hoptimal]

/-- Companion bridge: under an explicit minimizing sequence `xHat`, pointwise monotonicity of the
models makes the attained-history intervals nested downward and the attained-history gaps
nonincreasing. -/
theorem attainedLevelMethodValueInterval_subset_and_gap_antitone_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    Δ[history]((k + 1)) ⊆ Δ[history](k) ∧
      δ[history]((k + 1)) ≤ δ[history](k) := by
  exact ⟨attainedValueInterval_subset_step_of_pointwiseModelMono
      f xSeq xHat hxHat_mem hxHat_min hmono k,
    attainedGap_antitone_step_of_pointwiseModelMono
      f xSeq xHat hxHat_mem hxHat_min hmono k⟩

/-- Companion bridge: under an explicit minimizing sequence `xHat`, the textbook real chain
`\hat f_k^* ≤ \hat f_{k+1}^* ≤ f_{k+1}^* ≤ f_k^*` follows from the canonical `EReal` Proposition
3.50 theorem. -/
theorem attainedLevelMethodStepwiseBounds_of_monotoneUnderestimators
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) ∧
      fhat(history, (k + 1)) ≤ fstar(history, (k + 1)) ∧
      fstar(history, (k + 1)) ≤ fstar(history, k) := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
        Q model f xSeq xHat hxHat_mem hxHat_min j
  simpa using
    levelMethodHistoryFromApproximateValues_stepwiseBounds_of_monotoneUnderestimators
      f xSeq (fun i ↦ model i (xHat i)) hhat hxSeq hunder hmono k

end AttainedHistory

end History

end

/-! ### Theorem_3_50 (from Chap03) -/
noncomputable section

open EuclideanSpace
open scoped ConvexLipschitz

/- Primary domain: value-oracle lower bounds for constrained convex minimization on `ℓ∞`-balls.

Relevant owner-style declarations sampled before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3` for the primitive feasible-set
  and objective data of a constrained minimization problem;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7` for the
  derived optimal-value and `ε`-accuracy API;
- `ConvexLipschitzOn` and the Lean notation `𝓕⁰⁰[M](Q)` for the textbook class
  `𝓕_M^{0,0}(Q)` in `Chap03/Definition_3_64`, the
  source-facing Chapter 3 owner of fixed-parameter convex Lipschitz objectives on a feasible set;
- `DeterministicValueOracleMethod` and
  `DeterministicValueOracleMethod.oracleTranscript` in `Chap01/Theorem_1_3_9`, the chapter owner
  for ordered deterministic value-oracle methods;
- `DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin` in
  `Chap01/Theorem_1_3_9`, the closest upstream owner-pattern for bounded-budget oracle
  correctness on a source-facing problem class;
- `linftyLipschitzClass` and `mem_linftyLipschitzClass_iff_lipschitzOnWith` in
  `Chap01/Definition_1_3_4`, the chapter owner and canonical bridge for `ℓ∞`-Lipschitz
  objectives;
- `EuclideanSpace.linftyClosedBall` in `Chap01/Definition_1_3_2` for the source-facing
  `ℓ∞`-ball owner built from the chapter's `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)`.

Source/core/bridge triage:
- source-facing: the Theorem 3.50 problem-class predicate on
  `SetConstrainedMinimizationProblem`, adding the textbook `ℓ∞`-ball and Lipschitz/convex
  hypotheses without strengthening the source assumptions;
- core/canonical: `SetConstrainedMinimizationProblem`, the source-facing class
  `𝓕⁰⁰[M](B∞(0, R))`, its derived optimal-value and approximate-minimizer API, and
  `DeterministicValueOracleMethod`;
- bridge/view: the source-facing `EuclideanSpace.linftyClosedBall` owner from
  `Definition_1_3_2`, the Chapter 1 coordinate-transport bridge to `LipschitzOnWith`, and the
  canonical feasible-set-indexed method type `Set E → DeterministicValueOracleMethod E`, which
  reuses the Chapter 1 transcript recursion while exposing the constrained problem's feasible set
  to the algorithm.

Primitive data:
- for problems: only the feasible set and objective, owned by
  `SetConstrainedMinimizationProblem`;
- for algorithms: a feasible-set-indexed family `Set E → DeterministicValueOracleMethod E` of
  deterministic query and output rules, each already owned by
  `DeterministicValueOracleMethod`.

Derived API:
- `optimalValue` and `IsApproximateMinimizer` from the Chapter 1 owner abstraction;
- the source-facing Theorem 3.50 class predicate adding nonempty/convex and `Q ⊆ B∞(0, R)` to
  the Chapter 3 function-class owner `problem.objective ∈ 𝓕⁰⁰[M](B∞(0, R))`;
- the companion bridge
  `linftyClosedBall_lipschitz_iff_lipschitzOnWith_coordImage`, which recovers the canonical
  coordinate-transported `LipschitzOnWith` view without making it the main owner;
- the uniform-accuracy predicate phrased through the Chapter 1 derived API `queryAfter` and
  `outputAfter` after specializing the feasible-set-indexed owner at `problem.feasibleSet`. -/

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/-- On `B∞(0, R)`, the textbook `ℓ∞`-Lipschitz estimate is equivalent to the Chapter 1
coordinate-transported `LipschitzOnWith` bridge. The source-facing Theorem 3.50 class keeps the
`‖·‖∞` surface and uses this theorem only as a companion view. -/
theorem linftyClosedBall_lipschitz_iff_lipschitzOnWith_coordImage
    {f : E → ℝ} {R M : NNReal} :
    (∀ x ∈ linftyClosedBall R, ∀ y ∈ linftyClosedBall R,
      |f x - f y| ≤ (M : ℝ) * ‖x - y‖∞) ↔
      LipschitzOnWith M (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
        (coordEquiv '' (linftyClosedBall R : Set E)) := by
  sorry

namespace SetConstrainedMinimizationProblem

/-- Theorem 3.50's constrained problem class is the Chapter 1 owner
`SetConstrainedMinimizationProblem` together with the textbook hypotheses that the feasible set is
nonempty and convex, lies in the ambient closed `ℓ∞`-ball `B∞(0, R)`, and belongs to the
source-facing Chapter 3 class `𝓕_{M}^{0,0}(B∞(0, R))`. The ball radius is carried on the canonical
nonnegative owner `R : NNReal`, rather than as a raw real plus a separate positivity guard. -/
def IsInLinftyConstrainedProblemClass
    (problem : SetConstrainedMinimizationProblem E) (R M : NNReal) : Prop :=
  problem.feasibleSet.Nonempty ∧
    Convex ℝ problem.feasibleSet ∧
    problem.feasibleSet ⊆ linftyClosedBall R ∧
    problem.objective ∈ 𝓕⁰⁰[M](linftyClosedBall R)

end SetConstrainedMinimizationProblem

namespace DeterministicValueOracleMethod

/-- A deterministic value-oracle method solves the constrained problem class from Theorem 3.50
within `T` calls when, for every admissible constrained problem, the feasible-set-specialized
method queries only inside `B∞(0, R)` and its transcript-based output is an `ε`-approximate
minimizer in the canonical Chapter 1 sense. -/
def SolvesLinftyConstrainedProblemClassWithin
    (method : Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ problem : SetConstrainedMinimizationProblem E,
    problem.IsInLinftyConstrainedProblemClass R M →
      let algorithm := method problem.feasibleSet
      (∀ t : ℕ, t < T → algorithm.queryAfter problem t ∈ linftyClosedBall R) ∧
        problem.IsApproximateMinimizer ε (algorithm.outputAfter problem T)

end DeterministicValueOracleMethod

/-- Theorem 3.50: if the target accuracy satisfies `0 < ε` and a feasible-set-aware deterministic
value-oracle method with at most `T` oracle calls uniformly guarantees, for every nonempty convex
`Q ⊆ B∞(0, R)` and every `f ∈ 𝓕_{M}^{0,0}(B∞(0, R))`, an `ε`-approximate minimizer of the induced
set-constrained problem, then the query budget satisfies the lower bound
`n * log (M R / (8 ε)) ≤ T`. -/
-- Proof sketch: specialize to the finite hard family `u ↦ f_u` on the uniform grid inside
-- `B∞(0, R)`, where `f_u(x) = M * ‖x - u‖∞` and `Q = B∞(0, R)`. A depth-`T` value-query
-- transcript leaves exponentially many candidate minimizers consistent with the observed values,
-- so if `T < n * log (M R / (8 ε))` then two separated hard instances remain indistinguishable.
-- Any single feasible output is therefore `ε`-suboptimal on at least one of them.
theorem value_oracle_query_lower_bound_of_uniform_epsilon_guarantee
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hε : 0 < ε)
    (hmethod : DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin
      method R M ε T) :
    (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)) ≤ (T : ℝ) := sorry

end
