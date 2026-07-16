import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_32

open scoped MeasureTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

noncomputable section

universe u v

/- Definition 16.1 is organized around a canonical owner and two source-facing views.

- `IsCFP` is the source-facing notion of a characteristic function on `ℝ`.
- `MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible` is the `core/canonical` owner
  predicate on laws in an additive measurable space.
- `IsInfinitelyDivisibleCFP` and `IsInfinitelyDivisibleRandomVariable` are the two
  `bridge/view` formulations used in the chapter.

The refinements below keep the source-facing bridge notions, but route their owner-side API
through canonical `ProbabilityMeasure` constructions instead of parallel local wrappers.
-/

/-- A complex-valued function on `ℝ` is a characteristic function of a probability law when it is
the Fourier transform of some probability measure on `ℝ`. -/
def IsCFP (φ : ℝ → ℂ) : Prop :=
  ∃ μ : ProbabilityMeasure ℝ, charFun μ = φ

/-- A characteristic function on `ℝ` is infinitely divisible if every positive integer root can
again be realized as the characteristic function of a probability law on `ℝ`. -/
def IsInfinitelyDivisibleCFP (φ : ℝ → ℂ) : Prop :=
  ∀ n : ℕ+, ∃ φn : ℝ → ℂ,
    IsCFP φn ∧ φ = fun t ↦ φn t ^ (n : ℕ)

namespace MeasureTheory.ProbabilityMeasure

/-- The characteristic function of a probability law on `ℝ` is a CFP. -/
theorem isCFP_charFun (μ : ProbabilityMeasure ℝ) :
    IsCFP (charFun μ) :=
  ⟨μ, rfl⟩

/-- The characteristic function of the `n`th convolution power is the `n`th power of the
underlying characteristic function. -/
theorem charFun_pow (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    charFun ((μ ^ n : ProbabilityMeasure ℝ) : Measure ℝ) = fun t ↦ charFun μ t ^ n := sorry

variable {E : Type u} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Definition 16.1: a probability law on an additive measurable space is infinitely divisible if,
for every positive integer `n`, it admits an `n`th additive convolution root. The source-facing
characteristic-function and random-variable formulations below specialize this owner notion to
laws on `ℝ`. -/
class IsInfinitelyDivisible (μ : ProbabilityMeasure E) : Prop where
  /-- For each positive integer `n`, there is a probability law whose `n`th convolution power is
  `μ`. -/
  exists_root : ∀ n : ℕ+, ∃ ν : ProbabilityMeasure E, ν ^ (n : ℕ) = μ

-- Proof sketch: for `δ_x`, take the `n`th root `δ_(x / n)` and use the convolution-monoid power
-- together with the behavior of convolution on Dirac masses.
/-- Every Dirac probability measure on `ℝ` is infinitely divisible. -/
instance diracProba_isInfinitelyDivisible (x : ℝ) :
    IsInfinitelyDivisible (diracProba x) := sorry

-- Proof sketch: choose an `n`th convolution root from `exists_root`, then identify the
-- characteristic function of its convolution power with the `n`th pointwise power of the root
-- characteristic function using `charFun_pow`.
/-- The characteristic function of an infinitely divisible probability law is infinitely divisible
in the characteristic-function sense. -/
theorem charFun_isInfinitelyDivisible {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    IsInfinitelyDivisibleCFP (charFun μ) := sorry

end MeasureTheory.ProbabilityMeasure

section RandomVariable

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
variable (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E)

/-- An additive measurable-space-valued random variable is infinitely divisible if, for every
positive integer `n`, its law is the law of a sum of `n` i.i.d. random variables on some
probability space. -/
def IsInfinitelyDivisibleRandomVariable : Prop :=
  ∀ n : ℕ+, ∃ Ω' : Type u, ∃ _ : MeasurableSpace Ω',
    ∃ P' : ProbabilityMeasure Ω', ∃ ν : ProbabilityMeasure E,
      ∃ Y : Fin n → Ω' → E,
        (∀ i, Measurable (Y i)) ∧
          (∀ i, HasLaw (Y i) ν P') ∧
          iIndepFun Y P' ∧
          IdentDistrib X (fun ω ↦ ∑ i, Y i ω) P P'

-- Proof sketch: one direction pushes the i.i.d. decomposition to the law of `X`; the other
-- direction uses `ProbabilityTheory.exists_iid` to realize each convolution root on a probability
-- space and then sums the coordinate family.
/-- Infinite divisibility of an additive measurable-space-valued random variable is equivalent to
infinite divisibility of its law as a probability measure on its value space. -/
theorem isInfinitelyDivisibleRandomVariable_iff_law_isInfinitelyDivisible
    (hX : Measurable X) :
    IsInfinitelyDivisibleRandomVariable P X ↔
      IsInfinitelyDivisible (ProbabilityMeasure.map ⟨P, inferInstance⟩ hX.aemeasurable) := sorry

end RandomVariable
