import Mathlib
import Nesterov.Chap02.Lemma_2_18
import Nesterov.Chap06.Definition_6_11
import Nesterov.Chap07.Definition_7_41

-- Declarations for this item will be appended below by the statement pipeline.

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
