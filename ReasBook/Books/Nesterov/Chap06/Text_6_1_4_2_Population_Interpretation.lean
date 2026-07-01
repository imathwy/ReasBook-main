import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v

variable {ι : Type u}

/-- The positive population weights `m_j` used in the continuous location model. -/
abbrev ContinuousLocationWeights (ι : Type u) :=
  ι → {m : ℝ // 0 < m}

namespace ContinuousLocationWeights

@[simp] theorem weights_pos (weights : ContinuousLocationWeights ι) (j : ι) :
    0 < (weights j : ℝ) :=
  (weights j).2

end ContinuousLocationWeights

section

variable [Fintype ι]
variable (E : Type v) [NormedAddCommGroup E]

/-- The dual feasible set `Q₂`, consisting of tuples whose components all have norm at most `1`. -/
def continuousLocationDualAdmissibleSet : Set (ι → E) :=
  {u | ∀ j, ‖u j‖ ≤ 1}

/-- The weighted Euclidean norm on dual tuples used to define the prox-function `d₂`. -/
def continuousLocationDualTupleNorm
    (weights : ContinuousLocationWeights ι) (u : ι → E) : ℝ :=
  Real.sqrt (∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))

/-- The prox-function `d₂(u) = (1 / 2) \sum_j m_j \|u_j\|^2`, written via the weighted
tuple norm. -/
def continuousLocationDualProxFunction
    (weights : ContinuousLocationWeights ι) : (ι → E) → ℝ :=
  fun u ↦ (1 / 2 : ℝ) * (continuousLocationDualTupleNorm E weights u) ^ (2 : ℕ)

end

section

variable [Fintype ι]

/-- The total population weight `P = \sum_j m_j` in the continuous location model. -/
def continuousLocationTotalPopulation (weights : ContinuousLocationWeights ι) : ℝ :=
  ∑ j, (weights j : ℝ)

end

variable [Fintype ι]

-- Proof sketch: unfold `continuousLocationTotalPopulation`.
/-- Expanding `continuousLocationTotalPopulation` gives the finite sum `\sum_j m_j`. -/
theorem continuousLocationTotalPopulation_def
    (weights : ContinuousLocationWeights ι) :
    continuousLocationTotalPopulation weights = ∑ j, (weights j : ℝ) :=
  rfl

section

variable [Fintype ι]
variable (E : Type v) [NormedAddCommGroup E]

/-- The quantity `D₂`, defined as the maximal value of the prox-function `d₂` on the dual
feasible set `Q₂`. -/
def continuousLocationDualProxMaximum (weights : ContinuousLocationWeights ι) : ℝ :=
  sSup (continuousLocationDualProxFunction E weights '' continuousLocationDualAdmissibleSet E)

end

section

variable (E : Type v) [NormedAddCommGroup E]

-- Proof sketch: unfold `continuousLocationDualProxMaximum`.
/-- Expanding `continuousLocationDualProxMaximum` gives the supremum of `d₂` over `Q₂`. -/
theorem continuousLocationDualProxMaximum_def
    (weights : ContinuousLocationWeights ι) :
    continuousLocationDualProxMaximum E weights =
      sSup
        (continuousLocationDualProxFunction E weights ''
          continuousLocationDualAdmissibleSet E) :=
  rfl

-- Proof sketch: in a nontrivial real normed space, choose for each block `u_j` a unit vector;
-- then every component saturates the constraint `‖u_j‖ ≤ 1`, so `d₂(u) = (1 / 2) * ∑_j m_j`.
-- The reverse inequality follows because each admissible block has norm at most `1`, hence
-- `‖u_j‖^2 ≤ 1` in the weighted sum defining `d₂`.
/-- Text 6.1.4.2-Population Interpretation: in a nontrivial real normed space, the maximal value
`D₂` of the prox-function `d₂` on `Q₂` equals `P / 2`, where `P = \sum_j m_j` is the total
population weight of the model. -/
theorem continuousLocationDualProxMaximum_eq_half_totalPopulation
    [NormedSpace ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    continuousLocationDualProxMaximum E weights = continuousLocationTotalPopulation weights / 2 :=
  sorry

end

end
