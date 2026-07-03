import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_16_1 (from Items/Chap16) -/
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

/-! ### Exercise_16_1_1 (from Items/Chap16) -/
open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: choose an arbitrary convolution root `ν` of order `n`; since `μ` is supported on
-- `Icc a b`, the law `ν` is supported on an interval of width `(b - a) / n`, so
-- `Var[id; (ν : Measure ℝ)] ≤ ((b - a) / n)^2 / 4`. Passing to the `n`-fold convolution power and
-- using additivity of variance forces `Var[id; (μ : Measure ℝ)] = 0`, hence `μ` is Dirac.
/-- If an infinitely divisible probability measure on `ℝ` has full mass on a compact interval,
then it is a Dirac mass at a point of that interval. -/
theorem eq_diracProba_of_isInfinitelyDivisible_of_measure_Icc_eq_one
    (μ : ProbabilityMeasure ℝ) [IsInfinitelyDivisible μ] (a b : ℝ)
    (hμ : (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∃ x ∈ Set.Icc a b, μ = diracProba x := by
  rcases _root_.eq_dirac_of_isInfinitelyDivisible_of_measure_Icc_eq_one
      μ a b hμ with ⟨x, hx, hdirac⟩
  refine ⟨x, hx, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa [MeasureTheory.diracProba] using hdirac

-- Proof sketch: unpack the bounded-interval concentration hypothesis as some `Icc a b` of full
-- mass, then apply `eq_diracProba_of_isInfinitelyDivisible_of_measure_Icc_eq_one`.
/-- Exercise 16.1.1: an infinitely divisible probability distribution on `ℝ` that is concentrated
on a bounded interval is a Dirac measure. -/
theorem eq_diracProba_of_isInfinitelyDivisible_of_concentrated_on_bounded_interval
    (μ : ProbabilityMeasure ℝ) [IsInfinitelyDivisible μ]
    (hμ : ∃ a b : ℝ, (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∃ x : ℝ, μ = diracProba x := by
  rcases hμ with ⟨a, b, hμ⟩
  rcases eq_diracProba_of_isInfinitelyDivisible_of_measure_Icc_eq_one μ a b hμ with
    ⟨x, -, hx⟩
  exact ⟨x, hx⟩

end MeasureTheory.ProbabilityMeasure

/-! ### Exercise_16_1_2 (from Items/Chap16) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

section

variable {φ : ℝ → ℂ} {φs : ℕ+ → ℝ → ℂ}

-- Proof sketch: for each positive integer `n`, realize `φs n` as the characteristic function of
-- a probability measure `μₙ`. Since `(φs n)^n = φ`, the measures `μₙ` are `n`th convolution roots
-- of a fixed infinitely divisible law, so Lévy's continuity theorem forces `μₙ` to converge
-- weakly to `δ₀`. The compact-uniform convergence of the characteristic functions then follows
-- from the weak-convergence-to-uniform-on-compacts theorem for characteristic functions.
/-- Exercise 16.1.2 (1): if `φₙ` is a CFP for each positive integer `n` and
`φₙ(t)^n = φ(t)` for every real `t`, then `φₙ → 1` uniformly on every compact subset of `ℝ`. -/
theorem cfp_power_roots_tendstoUniformlyOn_one
    (hcfp : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ n : ℕ+, ∀ t : ℝ, (φs n t) ^ (n : ℕ) = φ t) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n t ↦ φs n t) (fun _ : ℝ ↦ (1 : ℂ)) atTop K := sorry

end

-- Proof sketch: choose the positive-integer roots supplied by `IsInfinitelyDivisibleCFP φ` and
-- apply `cfp_power_roots_tendstoUniformlyOn_one` to them. If `φ t = 0`, then every root vanishes
-- at `t`, contradicting convergence to `1` on the compact singleton `{t}`.
/-- Exercise 16.1.2 (2): an infinitely divisible characteristic function on `ℝ` has no zeros. -/
theorem infinitelyDivisibleCFP_ne_zero
    {φ : ℝ → ℂ} (hφ : IsInfinitelyDivisibleCFP φ) :
    ∀ t : ℝ, φ t ≠ 0 := sorry

namespace MeasureTheory.ProbabilityMeasure

/-- The characteristic function of an infinitely divisible probability law on `ℝ` has no zeros. -/
theorem charFun_ne_zero_of_isInfinitelyDivisible {μ : ProbabilityMeasure ℝ}
    (hμ : IsInfinitelyDivisible μ) :
    ∀ t : ℝ, charFun (μ : Measure ℝ) t ≠ 0 := by
  intro t
  exact infinitelyDivisibleCFP_ne_zero (charFun_isInfinitelyDivisible hμ) t

end MeasureTheory.ProbabilityMeasure

/-! ### Exercise_16_1_3 (from Items/Chap16) -/
open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: use the subordinator Lévy--Khinchin representation from Theorem 16.14 to split
-- the law into the deterministic drift part `α` and a jump contribution supported in `[0, ∞)`.
-- Show first that every interval `[0, x)` with `x < α` has zero mass, and then prove that any
-- `x > α` receives positive mass by isolating the event that the jump part is sufficiently small.
/-- Exercise 16.1.3 in owner-abstraction form: the drift parameter is the essential infimum of
the identity map under the law `μ`. -/
theorem HasSubordinatorLevyKhinchinRepresentation.drift_eq_essInf
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    α = essInf id (μ : Measure NNReal) := sorry

/-- Exercise 16.1.3: under a Lévy--Khinchin representation on `[0, ∞)`, the drift parameter `α`
is the supremum of the null initial intervals `[0, x)` of the law `μ`. On `NNReal`, `[0, x)` is
represented by `Set.Iio x`. -/
theorem HasSubordinatorLevyKhinchinRepresentation.drift_eq_sSup_null_initial_interval
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    α = sSup {x : NNReal | (μ : Measure NNReal) (Set.Iio x) = 0} := by
  simpa [essInf_eq_sSup] using hrep.drift_eq_essInf

end MeasureTheory.ProbabilityMeasure
