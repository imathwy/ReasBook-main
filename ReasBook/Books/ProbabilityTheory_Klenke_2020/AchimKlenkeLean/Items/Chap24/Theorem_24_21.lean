import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_14
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap24.Corollary_24_9
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap24.Definition_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E] [Bornology E]

/-- A Poisson point process on `E` with intensity `μ` under `P`, expressed using bounded
measurable-set marginals. -/
def IsPoissonPointProcessOnBoundedSets
    (μ : Measure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  IsRandomMeasure P X ∧
  HasIndependentIncrements P X ∧
  IsLocallyFiniteMeasure μ ∧
  ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → (μ A) ≠ ⊤ →
    HasLaw (fun ω ↦ X ω A)
      (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure (μ A).toNNReal))
      (P : Measure Ω)

/-- The bounded-set truncated first-moment condition on a measure `ν` on `NNReal × E`. It is the
local integrability hypothesis `∫ 𝟙_A(t) min (1, x) ν(d(x,t)) < ∞` from the textbook. -/
def HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (NNReal × E)) : Prop :=
  ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
    ∫⁻ z, Set.indicator A (fun _ : E ↦ min (1 : ℝ≥0∞) (z.1 : ℝ≥0∞)) z.2 ∂ν < ∞

-- Proof sketch: unfold `HasFiniteTruncatedFirstMomentOnBoundedSets`; this is exactly the bounded
-- measurable-set truncated first-moment condition displayed in the source theorem.
/-- Unfolding `HasFiniteTruncatedFirstMomentOnBoundedSets` recovers the textbook hypothesis
`∫ 𝟙_A(t) min (1, x) ν(d(x,t)) < ∞` on every bounded measurable set `A ⊆ E`. -/
theorem hasFiniteTruncatedFirstMomentOnBoundedSets_iff
    (ν : Measure (NNReal × E)) :
    HasFiniteTruncatedFirstMomentOnBoundedSets ν ↔
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
        ∫⁻ z, Set.indicator A (fun _ : E ↦ min (1 : ℝ≥0∞) (z.1 : ℝ≥0∞)) z.2 ∂ν < ∞ := sorry

/-- The restriction of the canonical measure `ν` to jumps landing in `A`, viewed as a measure on
the jump-size coordinate. This is the textbook Lévy measure `ν(· × A)`. -/
def restrictedLevyMeasure (ν : Measure (NNReal × E)) (A : Set E) : Measure NNReal :=
  Measure.map Prod.fst (ν.restrict (Prod.snd ⁻¹' A))

-- Proof sketch: unfold `restrictedLevyMeasure`; by definition it is the first-coordinate pushforward
-- of `ν` restricted to the slice with second coordinate in `A`.
/-- Unfolding `restrictedLevyMeasure ν A` gives the pushforward description of the slice
`ν(· × A)`. -/
theorem restrictedLevyMeasure_def (ν : Measure (NNReal × E)) (A : Set E) :
    restrictedLevyMeasure ν A = Measure.map Prod.fst (ν.restrict (Prod.snd ⁻¹' A)) := sorry

/-- The random measure obtained from a Poisson point process on `NNReal × E` by weighting each
point `(x,t)` with its jump size `x` and adding the deterministic measure `α`. -/
def poissonDrivenRandomMeasure
    (α : Measure E) (X : Ω → Measure (NNReal × E)) (ω : Ω) : Measure E :=
  α + Measure.map Prod.snd ((X ω).withDensity fun z ↦ (z.1 : ℝ≥0∞))

-- Proof sketch: unfold `poissonDrivenRandomMeasure`; it is exactly the deterministic part `α`
-- plus the weighted pushforward of `X ω` along the location map `(x,t) ↦ t`.
/-- Unfolding `poissonDrivenRandomMeasure` gives the textbook formula
`Y(A) = α(A) + ∫ x 𝟙_A(t) X(d(x,t))`. -/
theorem poissonDrivenRandomMeasure_def
    (α : Measure E) (X : Ω → Measure (NNReal × E)) (ω : Ω) :
    poissonDrivenRandomMeasure α X ω =
      α + Measure.map Prod.snd ((X ω).withDensity fun z ↦ (z.1 : ℝ≥0∞)) := sorry

/-- A random measure on `E` under `P` has infinitely divisible bounded-set evaluations when it is
measurable, has independent increments, and every bounded measurable-set evaluation has an almost
surely finite infinitely divisible law on `NNReal`. -/
class IsInfinitelyDivisibleRandomMeasureOnBoundedSets
    (P : ProbabilityMeasure Ω) (Y : Ω → Measure E) : Prop where
  /-- The measure-valued map underlying `Y` is measurable. -/
  measurable : Measurable Y
  /-- The random measure `Y` has independent increments. -/
  independent_increments : HasIndependentIncrements P Y
  /-- Every bounded measurable-set evaluation of `Y` is finite almost surely. -/
  eval_ae_lt_top :
    ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
      ∀ᵐ ω ∂(P : Measure Ω), Y ω A < ∞
  /-- Every bounded measurable-set evaluation of `Y` has an infinitely divisible law on
  `NNReal`. -/
  eval_isInfinitelyDivisible :
    ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
      ∃ μA : ProbabilityMeasure NNReal,
        HasLaw (fun ω ↦ (Y ω A).toNNReal) (μA : Measure NNReal) (P : Measure Ω) ∧
          MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μA

/-- A random measure has canonical measure `ν` and deterministic part `α` when each bounded
measurable-set evaluation has the Lévy--Khinchin representation with drift `α(A)` and Lévy measure
`ν(· × A)`. -/
class HasCanonicalMeasureAndDeterministicPart
    (P : ProbabilityMeasure Ω) (Y : Ω → Measure E) (α : Measure E)
    (ν : Measure (NNReal × E)) : Prop extends IsInfinitelyDivisibleRandomMeasureOnBoundedSets P Y where
  /-- On each bounded measurable set `A`, the law of `Y(A)` has deterministic part `α(A)` and
  Lévy measure `ν(· × A)`. -/
  eval_hasLevyKhinchin :
    ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
      ∃ μA : ProbabilityMeasure NNReal,
        HasLaw (fun ω ↦ (Y ω A).toNNReal) (μA : Measure NNReal) (P : Measure Ω) ∧
          HasSubordinatorLevyKhinchinRepresentation
            μA (α A).toNNReal (restrictedLevyMeasure ν A)

-- Proof sketch: combine the Poisson random-measure construction from Theorem 24.16 with the
-- one-dimensional subordinator statement from Theorem 24.17 on each bounded measurable set `A`.
-- The definition of `poissonDrivenRandomMeasure` rewrites `Y(A)` as
-- `α(A) + ∫ x 𝟙_A(t) X(d(x,t))`, the Poisson-point-process property gives independent
-- increments, and the restricted jump measure `restrictedLevyMeasure ν A` is the Lévy measure of
-- the resulting marginal law.
/-- Theorem 24.21: if `X ∼ PPP_ν` on `NNReal × E` and `ν` satisfies the truncated first-moment
condition on bounded measurable subsets of `E`, then the random measure
`Y(A) = α(A) + ∫ x 𝟙_A(t) X(d(x,t))` is an infinitely divisible random measure with independent
increments, canonical measure `ν`, and deterministic part `α`. -/
theorem poissonDrivenRandomMeasure_hasCanonicalMeasureAndDeterministicPart
    {P : ProbabilityMeasure Ω} {ν : Measure (NNReal × E)} {α : Measure E}
    {X : Ω → Measure (NNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets ν)
    (hX : IsPoissonPointProcessOnBoundedSets ν P X) :
    HasCanonicalMeasureAndDeterministicPart P (poissonDrivenRandomMeasure α X) α ν := sorry

/-- The Poisson construction of Theorem 24.21 canonically equips the resulting random measure with
its deterministic part and canonical measure. -/
instance poissonDrivenRandomMeasure_instHasCanonicalMeasureAndDeterministicPart
    {P : ProbabilityMeasure Ω} {ν : Measure (NNReal × E)} {α : Measure E}
    {X : Ω → Measure (NNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets ν)
    (hX : IsPoissonPointProcessOnBoundedSets ν P X) :
    HasCanonicalMeasureAndDeterministicPart P (poissonDrivenRandomMeasure α X) α ν :=
  poissonDrivenRandomMeasure_hasCanonicalMeasureAndDeterministicPart hν hX

end ProbabilityTheory
