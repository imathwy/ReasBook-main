import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_19_10 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u}

/- Layering for Example 19.10:
- `source-facing`: the normalized conductance walk `p(x,y) = C(x,y) / conductance C x` and the
  reversing measure with singleton masses `π({x}) = conductance C x`.
- `core/canonical`: the owner declarations `conductance`, `IsRandomWalkWithWeights`, and
  `Kernel.IsReversible`.
- `bridge/view`: `conductanceTransitionMatrix` and `conductanceMeasure` package the textbook
  source-facing data in terms of those canonical owners. -/

/-- The transition matrix obtained by normalizing the conductances in the row of `x`. -/
def conductanceTransitionMatrix (C : E → E → ℝ≥0∞) (x y : E) : ℝ≥0∞ :=
  C x y / conductance C x

-- Proof sketch: unfold `conductanceTransitionMatrix`; the entry `(x,y)` is defined by the quotient
-- `C x y / conductance C x`.
/-- The conductance transition matrix satisfies `p(x,y) = C(x,y) / C(x)`. -/
@[simp]
theorem conductanceTransitionMatrix_apply (C : E → E → ℝ≥0∞) (x y : E) :
    conductanceTransitionMatrix C x y = C x y / conductance C x := rfl

section ConductanceReversibility

variable {C : E → E → ℝ≥0∞}

-- Proof sketch: use `hC_finite` and `hC_pos` to factor `conductance C x` out of the row sum
-- `∑' y, C x y / conductance C x`; this gives `(∑' y, C x y) / conductance C x = 1`.
/-- The normalized conductance matrix has row sum `1`, so it is a stochastic matrix. -/
theorem conductanceTransitionMatrix_isStochastic
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    IsStochasticMatrix (conductanceTransitionMatrix C) := sorry

-- Proof sketch: the owner abstraction `IsRandomWalkWithWeights` packages exactly the symmetry,
-- finiteness, and row-normalization data attached to the conductance transition matrix in
-- Example 19.10. Use `conductanceTransitionMatrix_isStochastic` for the row-sum field and
-- `conductanceTransitionMatrix_apply` for the normalization formula.
/-- The normalized conductance matrix is the random walk with weights `C` in the sense of
Definition 19.11. -/
theorem conductanceTransitionMatrix_isRandomWalkWithWeights
    (hC_symm : ∀ x y : E, C x y = C y x)
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    IsRandomWalkWithWeights (conductanceTransitionMatrix C) C := sorry

-- Proof sketch: substitute the definition of `conductanceTransitionMatrix`; the factor
-- `conductance C x` cancels against the denominator because `hC_pos x` makes the
-- denominator strictly positive.
/-- Multiplying `p(x,y)` by the vertex weight `C(x)` recovers the original conductance `C(x,y)`. -/
theorem conductance_mul_transitionMatrix
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) (x y : E) :
    conductance C x * conductanceTransitionMatrix C x y = C x y := sorry

end ConductanceReversibility

section ConductanceMeasure

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- The measure on the vertex set whose singleton mass at `x` is the total conductance `C(x)`. -/
def conductanceMeasure (C : E → E → ℝ≥0∞) : Measure E :=
  Measure.sum fun x : E ↦ conductance C x • Measure.dirac x

-- Proof sketch: expand `conductanceMeasure` as a sum of weighted Dirac masses and evaluate it on
-- the singleton `{x}`; only the `x`-term survives.
/-- The conductance measure assigns to `{x}` the total outgoing conductance `C(x)`. -/
@[simp]
theorem conductanceMeasure_apply_singleton (C : E → E → ℝ≥0∞) (x : E) :
    conductanceMeasure C {x} = conductance C x := sorry

section ConductanceReversibility

variable {C : E → E → ℝ≥0∞}

-- Proof sketch: on singleton sets `{x}` and `{y}`, the reversibility identity becomes
-- `conductance C x * conductanceTransitionMatrix C x y =
-- conductance C y * conductanceTransitionMatrix C y x`. Apply
-- `conductance_mul_transitionMatrix` on both sides and use the symmetry hypothesis
-- `hC_symm`.
/-- Example 19.10: for a symmetric conductance family `C` with finite positive vertex weights, the
discrete kernel with transition matrix `p(x,y) = C(x,y) / C(x)` is reversible with respect to the
measure whose singleton masses are `π({x}) = C(x)`. -/
theorem conductanceKernel_isReversible
    (hC_symm : ∀ x y : E, C x y = C y x)
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    Kernel.IsReversible
      (discreteMatrixKernel (conductanceTransitionMatrix C))
      (conductanceMeasure C) := sorry

end ConductanceReversibility
end ConductanceMeasure

end ProbabilityTheory
