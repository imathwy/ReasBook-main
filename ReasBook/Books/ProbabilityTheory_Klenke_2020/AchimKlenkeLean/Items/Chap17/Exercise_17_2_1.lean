import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Theorem_5_28
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap10.Definition_10_3
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_16
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_12
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_42
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Example_17_22
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Lemma_17_45
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v}

/-- The source-facing rowwise support data `Aₓ` contains every possible next state from `x` for
the transition matrix `p`. -/
def HasStepSupportWithin (p : E → E → ℝ≥0∞) (A : E → Set E) : Prop :=
  ∀ ⦃x y : E⦄, p x y ≠ 0 → y ∈ A x

/-- The source-facing rowwise support data `Aₓ` has size at most three. -/
def HasAtMostThreePointSet (A : E → Set E) : Prop :=
  ∀ x : E, ∃ a b c : E, ∀ ⦃y : E⦄, y ∈ A x → y = a ∨ y = b ∨ y = c

/-- Each row of the transition matrix has support of size at most three. This is the rowwise
source-facing finite-support hypothesis from the exercise. -/
def HasAtMostThreePointStepSupportAt (p : E → E → ℝ≥0∞) (x : E) : Prop :=
  ∃ a b c : E, ∀ y : E, p x y ≠ 0 → y = a ∨ y = b ∨ y = c

/-- Each row of the transition matrix has support of size at most three. -/
def HasAtMostThreePointStepSupport (p : E → E → ℝ≥0∞) : Prop :=
  ∀ x : E, HasAtMostThreePointStepSupportAt p x

/-- A fixed rowwise support container of size at most three yields the exercise's rowwise
three-point support hypothesis for the transition matrix `p`. -/
theorem HasAtMostThreePointSet.hasAtMostThreePointStepSupport
    {p : E → E → ℝ≥0∞} {A : E → Set E} (hA : HasAtMostThreePointSet A)
    (hpA : HasStepSupportWithin p A) :
    HasAtMostThreePointStepSupport p := by
  intro x
  rcases hA x with ⟨a, b, c, hAxc⟩
  refine ⟨a, b, c, ?_⟩
  intro y hy
  exact hAxc (hpA hy)

section ThreePointSupport

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Coe E ℝ]
  {p : E → E → ℝ≥0∞}

private def transitionNextStateMean : E → ℝ :=
  fun x ↦ ∫ y, (y : ℝ) ∂ discreteMatrixKernel p x

private def transitionNextStateSecondMoment : E → ℝ :=
  fun x ↦ ∫ y, (y : ℝ) ^ (2 : ℕ) ∂ discreteMatrixKernel p x

/-- The one-step drift of the transition matrix `p`, expressed as the conditional mean of the
increment `X₁ - X₀` via the owner kernel `discreteMatrixKernel p`. -/
def transitionDrift (p : E → E → ℝ≥0∞) : E → ℝ :=
  fun x ↦ transitionNextStateMean (p := p) x - (x : ℝ)

/-- The predictable square-variation increment of the transition matrix `p`, i.e. the conditional
variance of the next state, equivalently the centered conditional second moment of the increment
`X₁ - X₀`. -/
def transitionSquareVariationIncrement (p : E → E → ℝ≥0∞) : E → ℝ :=
  fun x ↦
    transitionNextStateSecondMoment (p := p) x - transitionNextStateMean (p := p) x ^ (2 : ℕ)

/-- The compensated process obtained by subtracting the accumulated drift from the real-valued
chain `X`, written using the owner partial-sum process on the drift observable `transitionDrift p`.
-/
def compensatedTransitionProcess (p : E → E → ℝ≥0∞) (X : ℕ → Ω → E) : ℕ → Ω → ℝ :=
  fun n ω ↦
    (X n ω : ℝ) - partialSum (fun n ↦ transitionDrift p ∘ X n) n ω

end ThreePointSupport

/-- The square-variation density from the Moran model in Example 17.22 and formula `(17.12)`,
written on the owner state space `Fin (N + 1)` via `moranFrequency`. -/
def moranSquareVariationDensity (N : ℕ+) : Fin (N + 1) → ℝ :=
  fun i ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N i * (1 - moranFrequency N i)

section ProcessPastFiltration

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Coe E ℝ]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable {p : E → E → ℝ≥0∞}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

local notation "ℱ" => processFiltration X

/-- Exercise 17.2.1 (1): for a countable real-valued state space with at most three possible next
states from each point, subtracting the accumulated drift `d(X_k)` from the Markov chain produces
a martingale, and the square variation process of that compensated chain is the accumulated
canonical density coming from the three-point-support hypothesis. -/
/-
Proof sketch: apply the one-step Markov property with the drift function coming from the
three-point-support hypothesis, identify the conditional expectation of the next increment with the
rowwise first moment of `p`, and then use the centered second-moment formula to identify the
square variation density.
-/
theorem compensatedTransitionProcess_martingale_and_squareVariation
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p) (x : E) :
    Martingale (compensatedTransitionProcess p X) ℱ (P x : Measure Ω) ∧
      IsSquareVariationProcess ℱ (P x : Measure Ω)
        (compensatedTransitionProcess p X)
        (partialSum (fun n ↦ transitionSquareVariationIncrement p ∘ X n)) :=
  sorry

end ProcessPastFiltration

/-- Exercise 17.2.1 (2): the canonical square-variation density from part (i) takes values in
`[0, ∞)`. Equivalently, the canonical square-variation increment is nonnegative for every state
`x`. -/
/-
Proof sketch: each summand in the square-variation increment is a square multiplied by a
nonnegative transition weight, so the whole series is nonnegative.
-/
theorem transitionSquareVariationIncrement_nonneg [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} (h_support : HasAtMostThreePointStepSupport p) (x : E) :
    0 ≤ transitionSquareVariationIncrement p x := sorry

section ProcessPastFiltration

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Coe E ℝ]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable {p : E → E → ℝ≥0∞}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

local notation "ℱ" => processFiltration X

/-- Exercise 17.2.1 (3): the function `f : E → [0, ∞)` from part (i) is unique. Any nonnegative
square-variation density for the compensated chain agrees with the canonical function
coming from the three-point-support hypothesis. -/
/-
Proof sketch: compare the given square-variation process with the canonical one from
`compensatedTransitionProcess_martingale_and_squareVariation`; equality of predictable quadratic
variation increments forces the rowwise density to agree with the canonical square-variation
increment.
-/
theorem squareVariationDensity_unique
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p) (x : E)
    {f : E → NNReal}
    (h_squareVariation :
      IsSquareVariationProcess ℱ (P x : Measure Ω)
        (compensatedTransitionProcess p X)
        (partialSum (fun n ↦ (fun x ↦ (f x : ℝ)) ∘ X n))) :
    (fun x ↦ (f x : ℝ)) = transitionSquareVariationIncrement p := sorry

end ProcessPastFiltration

-- Proof sketch: once the source-facing rowwise support container `Aₓ` is fixed and has
-- cardinality at most three, the rows `p x` and `q x` have at most three unknown masses inside
-- `Aₓ`. Stochasticity, the drift identity, and the square-variation identity give three linear
-- relations, which determine those masses uniquely; injectivity of `E → ℝ` prevents distinct
-- states from collapsing to the same real location.
/-- Exercise 17.2.1 (ii), rowwise form: on a genuine real state space `E ⊂ ℝ`, once the
source-facing support container `Aₓ` is fixed, the row `p x` is uniquely determined by its drift
and square-variation increment at `x`. -/
theorem transitionRow_eq_of_drift_eq_and_squareVariationIncrement_eq [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (h_real : Function.Injective (fun x : E ↦ (x : ℝ)))
    {A : E → Set E} (hA : HasAtMostThreePointSet A)
    {p q : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (hq : IsStochasticMatrix q)
    (h_support_p : HasAtMostThreePointStepSupport p)
    (h_support_q : HasAtMostThreePointStepSupport q)
    (hpA : HasStepSupportWithin p A)
    (hqA : HasStepSupportWithin q A)
    {x : E}
    (hd : transitionDrift p x = transitionDrift q x)
    (hf :
      transitionSquareVariationIncrement p x = transitionSquareVariationIncrement q x) :
    p x = q x := sorry

-- Proof sketch: apply the rowwise uniqueness statement at each state `x`, using the fixed
-- source-facing support container `Aₓ`.
/-- Exercise 17.2.1 (ii): on a genuine real state space `E ⊂ ℝ`, a stochastic transition matrix
whose rows lie in a fixed rowwise support container `Aₓ` of size at most three is uniquely
determined by its drift function and its square-variation increment function. -/
theorem transitionMatrix_eq_of_drift_eq_and_squareVariationIncrement_eq [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (h_real : Function.Injective (fun x : E ↦ (x : ℝ)))
    {A : E → Set E} (hA : HasAtMostThreePointSet A)
    {p q : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (hq : IsStochasticMatrix q)
    (h_support_p : HasAtMostThreePointStepSupport p)
    (h_support_q : HasAtMostThreePointStepSupport q)
    (hpA : HasStepSupportWithin p A)
    (hqA : HasStepSupportWithin q A)
    (hd : transitionDrift p = transitionDrift q)
    (hf :
      transitionSquareVariationIncrement p = transitionSquareVariationIncrement q) :
    p = q := sorry

-- Proof sketch: at a fixed Moran count state `i`, the row support lies in the three neighboring
-- count states. The stochastic-row equation together with the zero drift and the explicit
-- square-variation density from `(17.12)`, written via `moranFrequency`, determines the three row
-- entries uniquely, so the row must equal the corresponding row of `moranTransitionMatrix N`.
/-- Exercise 17.2.1 (5): for the discrete Moran model of Example 17.22, the zero drift and the
explicit square-variation formula `(17.12)` determine the transition row at each state `i` to be
the corresponding row of the canonical owner matrix `moranTransitionMatrix N`. -/
theorem moranTransitionMatrix_row_of_squareVariationFormula
    {N : ℕ+} {p : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞} (hp : IsStochasticMatrix p)
    {i : Fin (N + 1)}
    (h_support : ∀ j : Fin (N + 1), p i j ≠ 0 →
      (j : ℕ) = (i : ℕ) + 1 ∨ j = i ∨ (i : ℕ) = (j : ℕ) + 1)
    (hd :
      ∑' j : Fin (N + 1), ((moranFrequency N j - moranFrequency N i) * (p i j).toReal) = 0)
    (hf :
      ∑' j : Fin (N + 1),
        (((moranFrequency N j - moranFrequency N i) ^ (2 : ℕ)) * (p i j).toReal) =
          moranSquareVariationDensity N i) :
    p i = moranTransitionMatrix N i := sorry

end ProbabilityTheory
