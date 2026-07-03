import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_18 (from Chap07) -/
noncomputable section

open scoped RealSymmetricMatrixSpace

variable {p n : ℕ}

local notation "Eₚ" => EuclideanSpace ℝ (Fin p)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Definition 7.18 lies in Chapter 7's symmetric-matrix spectral-radius domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, the chapter owner for real symmetric matrices;
- Chapter 7 Definition 7.21 `linearMatrixCombination`, the existing owner for coefficient-sum
  matrix maps;
- Chapter 7 Definition 7.17's direct use of `spectralRadius`, the canonical spectral-radius owner.

Best owner abstraction:
- source-facing: the spectral-radius objective `x ↦ ρ(∑ᵢ xᵢ Aᵢ)`;
- core/canonical: `𝕊^n`, `linearMatrixCombination`, and `spectralRadius`;
- bridge/view: the evaluation formula below rewriting the owner map to the textbook sum.

Primitive data:
- a family `coeffMatrices : Fin p → 𝕊^n` of symmetric coefficient matrices.

Derived API:
- the Chapter 7 coefficient-sum owner `linearMatrixCombination`;
- the real-valued spectral-radius expression obtained by applying `spectralRadius` to that sum.

This refinement removes the duplicate local subtype and local linear-map owner from this file and
reuses the established chapter owners directly. -/

/-- Definition 7.18: from symmetric coefficient matrices `A₁, …, Aₚ`, the induced objective maps
`x ∈ ℝᵖ` to the spectral radius of the linear matrix combination `∑ᵢ xᵢ Aᵢ`. -/
def spectralRadiusObjective (coeffMatrices : Fin p → SymmMat) : Eₚ → ℝ :=
  fun x ↦
    (spectralRadius ℝ
      ((linearMatrixCombination fun i ↦ (coeffMatrices i : Mₙ)) x)).toReal

/-- Evaluating `spectralRadiusObjective` recovers the spectral radius of `∑ᵢ xᵢ Aᵢ`. -/
-- Proof sketch: unfold `spectralRadiusObjective` and rewrite the coefficient-sum owner
-- `linearMatrixCombination` using its upstream evaluation formula.
theorem spectralRadiusObjective_apply
    (coeffMatrices : Fin p → SymmMat) (x : Eₚ) :
    spectralRadiusObjective coeffMatrices x =
      (spectralRadius ℝ (∑ i : Fin p, x i • (coeffMatrices i : Mₙ))).toReal := by
  simpa [spectralRadiusObjective] using
    congrArg (fun A : Mₙ ↦ (spectralRadius ℝ A).toReal)
      (linearMatrixCombination_apply (fun i ↦ (coeffMatrices i : Mₙ)) x)

end

/-! ### Lemma_7_18 (from Chap07) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 7.18 lies in the Chapter 7 strict-positivity / closed-convex weighted-sum
subdifferential domain.

Mandatory domain-style sampling before refinement:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in `Definition_7_81`, the source-facing
  owner and its primitive projection lemma;
- `ClosedConvexFunction` in `Chap03/Definition_3_1_1_5`, the canonical closed-convex owner for
  `WithTop ℝ`-valued functions, used on the chapter’s standard pointwise lift
  `fun x ↦ (f x : WithTop ℝ)`;
- `ClosedConvexFunction.nonneg_weighted_add` and
  `subdifferential_nonneg_weighted_add_eq_of_pos` in `Chap03/Lemma_3_1_12`, the chapter's
  closed-convex weighted-sum API written directly on the canonical pointwise combination
  `α₁ • f₁ + α₂ • f₂`;
- `ClosedConvexOn.nonneg_smul` in `Chap03/Theorem_3_1_5`, the owner pattern behind the zero-weight
  and one-summand branches.

Best owner abstraction:
- source-facing: `StrictlyPositiveOn Q f`;
- core/canonical: the closed-convex owner
  `ClosedConvexFunction (fun x ↦ (f x : WithTop ℝ))` together with the canonical pointwise
  weighted sum `α₁ • f₁ + α₂ • f₂`;
- bridge/view: the source-facing closure theorems in this file, which keep the conclusion on
  `StrictlyPositiveOn` while routing the genuinely two-summand case through the Chapter 3
  closed-convex sum rule.

Primitive data:
- the set `Q`;
- the summands `f₁`, `f₂`;
- the closed-convex owner witnesses `hcc₁`, `hcc₂` for the lifted summands;
- the weights `α₁`, `α₂`;
- the owner witnesses `hf₁`, `hf₂`.

Derived API:
- `StrictlyPositiveOn.nonneg_smul`;
- `StrictlyPositiveOn.nonnegative_linear_combination`.
-/

-- Proof sketch: if `α = 0`, the target is the zero function, whose only whole-space subgradient
-- is `0`; if `α > 0`, divide the defining subgradient inequality for `α • f` by `α` to recover a
-- subgradient of `f`, then rescale the strict-positivity inequality.
theorem StrictlyPositiveOn.nonneg_smul
    {Q : Set E} {f : E → ℝ} (hf : StrictlyPositiveOn Q f)
    {α : ℝ} (hα : 0 ≤ α) :
    StrictlyPositiveOn Q (α • f) := sorry

-- Proof sketch: split the zero-weight branches and dispatch them with
-- `StrictlyPositiveOn.nonneg_smul`. In the genuinely two-summand branch `α₁, α₂ > 0`, use
-- `subdifferential_nonneg_weighted_add_eq_of_pos` for the canonical `WithTop` lifts to write a
-- subgradient of `α₁ • f₁ + α₂ • f₂` as `α₁ • g₁ + α₂ • g₂`, then combine the defining
-- inequalities from `hf₁` and `hf₂`.
/-- Lemma 7.18: if the canonical `WithTop ℝ` lifts of `f₁` and `f₂` are closed convex and each
is strictly positive on `Q`, then every nonnegative linear combination `α₁ • f₁ + α₂ • f₂` is
strictly positive on `Q`. -/
theorem StrictlyPositiveOn.nonnegative_linear_combination
    {Q : Set E} {f₁ f₂ : E → ℝ}
    (hf₁ : StrictlyPositiveOn Q f₁) (hf₂ : StrictlyPositiveOn Q f₂)
    (hcc₁ : ClosedConvexFunction (fun x ↦ (f₁ x : WithTop ℝ)))
    (hcc₂ : ClosedConvexFunction (fun x ↦ (f₂ x : WithTop ℝ)))
    {α₁ α₂ : ℝ} (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    StrictlyPositiveOn Q (α₁ • f₁ + α₂ • f₂) := sorry

/-! ### Proposition_7_18 (from Chap07) -/
noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open scoped StandardSimplex

variable {n : ℕ} {m : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δₙ" => Δ[n]

/- Proposition 7.18 lies in Chapter 7's linear-packing / simplex-normalization domain.

Sampled owner-style declarations:
- `LinearPackingProblem`, `LinearPackingProblem.gauge`, `LinearPackingProblem.scaledGauge`,
  `LinearPackingProblem.mem_feasibleSet_iff`, and `LinearPackingProblem.optimalValue` in
  `Chap07/Definition_7_41`, the chapter owner carrying the packing data `(a_i, b, c)` together
  with the positivity assumptions `b_i > 0` and `c_j > 0`;
- `maxTypeObjective` and `maxTypeObjective_le_iff` in `Chap02/Lemma_2_18`, the chapter owner for
  finite maxima over a nonempty family;
- `stdSimplex` and the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the canonical owner
  of the standard simplex.

Best owner abstraction:
- source-facing: Proposition 7.18's reciprocal normalized formulations of the packing value `ψ*`;
- core/canonical: `LinearPackingProblem (m : ℕ) n`, its owner value `problem.optimalValue`, the
  feasible-set owner `problem.feasibleSet`, `maxTypeObjective`, and `Δ[n]`;
- bridge/view: the normalized constraint gauge `problem.gauge`, the derived feasibility criterion
  `problem.gauge ≤ 1`, the normalized slice `problem.normalizedSlice`, and the simplex rescaling
  `problem.scaledGauge`.

Primitive data:
- one owner `problem : LinearPackingProblem (m : ℕ) n`.

Derived API:
- the gauge `y ↦ max_i ⟪a_i, y⟫ / b_i`;
- the equivalent gauge presentation of `problem.feasibleSet`;
- the normalized slice `problem.normalizedSlice = {y ∈ ℝⁿ_+ | ⟪c, y⟫ = 1}`;
- the simplex gauge obtained from the diagonal change of variables `x_j = c_j y_j`.

This refinement removes the duplicate local supremum owner. Proposition 7.18 is now stated
directly on the chapter packing owner `LinearPackingProblem.optimalValue : EReal`, while the
textbook ratio expressions are kept as thin source-facing bridge theorems, with the reciprocal
recorded through `ℝ≥0∞` so the zero-minimum and empty-slice regimes remain faithful. -/

namespace LinearPackingProblem

-- Proof sketch: use `problem.mem_feasibleSet_iff` to rewrite feasibility as the coordinatewise
-- inequalities `⟪a_i, y⟫ ≤ b_i`, then divide by the positive owner data `b_i > 0` and collect the
-- resulting family through `maxTypeObjective_le_iff`.
/-- The packing-feasibility condition is equivalently the gauge inequality
`max_i (⟪a_i, y⟫ / b_i) ≤ 1`. -/
theorem mem_feasibleSet_iff_gauge_le_one
    (problem : LinearPackingProblem (m : ℕ) n) {y : E} :
    y ∈ problem.feasibleSet ↔ y ∈ nonnegativeOrthant n ∧ problem.gauge y ≤ 1 := by
  rw [problem.mem_feasibleSet_iff, gauge]
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    rw [maxTypeObjective_le_iff]
    intro i
    have hi : inner ℝ (problem.a i) y ≤ 1 * problem.b i := by
      simpa using hy.2 i
    exact (_root_.div_le_iff₀ (problem.b_pos_apply i)).2 hi
  · rintro ⟨hy_nonneg, hy_gauge⟩
    refine ⟨hy_nonneg, ?_⟩
    rw [maxTypeObjective_le_iff] at hy_gauge
    intro i
    have hi : inner ℝ (problem.a i) y / problem.b i ≤ 1 := by
      simpa using hy_gauge i
    have hi' : inner ℝ (problem.a i) y ≤ 1 * problem.b i :=
      (_root_.div_le_iff₀ (problem.b_pos_apply i)).1 hi
    simpa using hi'

-- Proof sketch: rescale any feasible nonnegative `y` by its positive `c`-pairing to land on the
-- slice `⟪c, y⟫ = 1`, compare the packing value with the reciprocal normalized gauge infimum, and
-- interpret that reciprocal in `ℝ≥0∞` so the zero-infimum / unbounded branch remains visible.
/-- Proposition 7.18: viewed in the canonical owner `EReal`, the packing value `ψ*` is the
reciprocal of the normalized gauge infimum on the slice `⟪c, y⟫ = 1`, with the reciprocal taken
in `ℝ≥0∞` so a zero infimum yields `⊤`. -/
theorem optimalValue_eq_inv_normalizedMin
    (problem : LinearPackingProblem (m : ℕ) n) :
    problem.optimalValue =
      (((sInf ((fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice))⁻¹ :
          ENNReal) : EReal) := sorry

-- Proof sketch: apply the change of variables `x_j = c_j y_j`, use the owner positivity
-- `problem.c_pos_apply j` to identify the normalized orthant slice `⟪c, y⟫ = 1` with `Δ[n]`, and
-- rewrite the gauge in terms of the scaled rows `j ↦ aᵢⱼ / c_j`.
/-- The normalized orthant minimum from Proposition 7.18 is carried to the corresponding simplex
infimum by the diagonal rescaling determined by the positive objective vector `c`. -/
theorem normalizedMin_eq_simplexMin_scaledGauge
    (problem : LinearPackingProblem (m : ℕ) n) :
    sInf ((fun y ↦ ENNReal.ofReal (problem.gauge y)) '' problem.normalizedSlice) =
      sInf (Set.range fun x : Δₙ ↦ ENNReal.ofReal (problem.scaledGauge x)) := sorry

-- Proof sketch: combine `optimalValue_eq_inv_normalizedMin` with the simplex reparametrization
-- `normalizedMin_eq_simplexMin_scaledGauge`.
/-- Proposition 7.18 in simplex form: the packing value `ψ*` is the reciprocal of the simplex
gauge infimum over `Δ_n`, with the reciprocal taken in `ℝ≥0∞` so a zero infimum yields `⊤` in the
canonical owner codomain `EReal`. -/
theorem optimalValue_eq_inv_simplexMin_scaledGauge
    (problem : LinearPackingProblem (m : ℕ) n) :
    problem.optimalValue =
      (((sInf (Set.range fun x : Δₙ ↦ ENNReal.ofReal (problem.scaledGauge x)))⁻¹ :
          ENNReal) : EReal) := sorry

end LinearPackingProblem

end

/-! ### Theorem_7_18 (from Chap07) -/
universe u v

section

variable {Scenario : Type u} {Decision : Type v}

/- Theorem 7.18 lies in Chapter 7's worst-case static-comparison / order-theoretic gap domain.

Mandatory domain-style sampling:
- mathlib `IsLUB`, the canonical owner for least upper bounds of sets of reals;
- mathlib `isLUB_sSup`, the canonical complete-lattice specialization of that owner;
- mathlib `Set.mem_range_self`, the bridge from a fixed scenario to membership in the range of the
  scenario-wise gap function;
- `staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy` in `Chap07/Theorem_7_17`,
  the nearby Chapter 7 pattern of keeping static-comparison values on canonical order owners
  rather than on local wrapper data.

Best owner abstraction:
- source-facing: the scenario-wise gap `v ↦ f (x v) v - f xStatic v` and the claim that every
  realized gap is bounded by any least upper bound `Δ` of its range;
- core/canonical: `IsLUB` on the range of that gap function;
- bridge/view: `Set.mem_range_self u`, which identifies the gap at the fixed scenario `u` as an
  element of the ranged owner set.

Primitive data:
- the payoff function `f`;
- the decision rule `x`;
- the comparison static strategy `xStatic`;
- the least-upper-bound witness `hΔ`.

Derived API:
- the pointwise scenario gap at `u`;
- the upper-bound conclusion obtained by specializing the `IsLUB` owner to the range element
  coming from `u`.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: `IsLUB`;
- bridge/view: `Set.mem_range_self`.
-/

-- Proof sketch: if `Δ` is the least upper bound of the set of scenario-wise gaps, then it is in
-- particular an upper bound for every element of that set; the gap at a fixed scenario `u` belongs
-- to the range by `Set.mem_range_self u`.
/-- Theorem 7.18: if `Δ` is the least upper bound of the scenario-wise gap
`v ↦ f (x v) v - f xStatic v` of a decision rule relative to a static strategy, then for every
scenario `u` the gap at `u` is bounded above by `Δ`. This is the distribution-free worst-case
guarantee relative to the static strategy. -/
theorem pointwise_gap_le_of_isLUB_worst_case_gap_against_static_strategy
    (f : Decision → Scenario → ℝ)
    (x : Scenario → Decision)
    (xStatic : Decision)
    {Δ : ℝ}
    (hΔ : IsLUB (Set.range fun v : Scenario ↦ f (x v) v - f xStatic v) Δ)
    (u : Scenario) :
    f (x u) u - f xStatic u ≤ Δ :=
  hΔ.1 <| Set.mem_range_self u

end
