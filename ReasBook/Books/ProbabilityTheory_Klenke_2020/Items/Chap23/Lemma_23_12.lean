import Mathlib
import AchimKlenkeLean.Items.Chap12.Definition_12_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InformationTheory MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

section EmpiricalCounts

variable {S : Type u} [DecidableEq S]

/-- The number of coordinates of a word `x : Fin n → S` equal to the symbol `a`. -/
def empiricalCount (n : ℕ) (x : Fin n → S) (a : S) : ℕ :=
  Fintype.card {i // x i = a}

end EmpiricalCounts

section EmpiricalSets

variable {S : Type u} [MeasurableSpace S]

-- Internal bridge from the source-facing `ℕ` indexing of Chapter 23 to the Chapter 12 owner
-- `empiricalDistributionTuple`, which is indexed by `ℕ+`.
private noncomputable abbrev empiricalWordDistribution {n : ℕ} (hn : n ≠ 0) (x : Fin n → S) :
    ProbabilityMeasure S :=
  let x' : Fin (Nat.toPNat n (Nat.pos_of_ne_zero hn)) → S := x
  empiricalDistributionTuple x'

/-- The event that a word of length `n` has empirical distribution `ν`. For `n = 0` this event is
empty, so the associated set of empirical distributions is empty as well. This is the
`source-facing` event attached to the Chapter 12 owner `empiricalDistributionTuple` on a
singleton-measurable alphabet. -/
def empiricalDistributionEvent [MeasurableSingletonClass S]
    (n : ℕ) (ν : ProbabilityMeasure S) : Set (Fin n → S) :=
  if hn : n = 0 then ∅ else
    fun x ↦ empiricalWordDistribution hn x = ν

-- Proof sketch: unfold `empiricalDistributionEvent`.
-- For `n ≠ 0`, membership is exactly the pointwise equality between `ν` and the normalized
-- coordinate counts, while for `n = 0` the event is empty.
/-- Membership in `empiricalDistributionEvent n ν` is the pointwise normalized-count condition when
`n ≠ 0`. -/
theorem mem_empiricalDistributionEvent_iff [DecidableEq S] [MeasurableSingletonClass S]
    {n : ℕ} {ν : ProbabilityMeasure S} {x : Fin n → S} :
    x ∈ empiricalDistributionEvent n ν ↔
      n ≠ 0 ∧
        ∀ a : S, (ν : Measure S) {a} = ((empiricalCount n x a : ℕ) : ENNReal) / (n : ENNReal) := by
  sorry

/-- The set `E_n` of empirical distributions realized by words of length `n`. -/
def empiricalDistributions [MeasurableSingletonClass S] (n : ℕ) : Set (ProbabilityMeasure S) :=
  fun ν ↦ ∃ x : Fin n → S, x ∈ empiricalDistributionEvent n ν

-- Proof sketch: unfold `empiricalDistributions`; this is exactly the existential realization of
-- the empirical-distribution event by some word of length `n`.
/-- A probability measure belongs to `empiricalDistributions n` exactly when it is realized
by some word of length `n`. -/
theorem mem_empiricalDistributions_iff [MeasurableSingletonClass S]
    (n : ℕ) (ν : ProbabilityMeasure S) :
    ν ∈ empiricalDistributions n ↔ ∃ x : Fin n → S, x ∈ empiricalDistributionEvent n ν := Iff.rfl

end EmpiricalSets

section FiniteAlphabet

/-- The combinatorial lower prefactor `(n + 1)^{-#S}`. -/
def empiricalLowerPrefactor (S : Type u) [Fintype S] (n : ℕ) : ENNReal :=
  ((n + 1 : ℕ) : ENNReal)⁻¹ ^ Fintype.card S

-- Proof sketch: unfold `empiricalLowerPrefactor` as the canonical power `((n + 1)⁻¹)^(#S)` and
-- rewrite that power as the product of `Fintype.card S` copies of `(n + 1)⁻¹`.
/-- Expanding `empiricalLowerPrefactor S n` gives the finite product form of `(n + 1)^{-#S}`. -/
theorem empiricalLowerPrefactor_def (S : Type u) [Fintype S] (n : ℕ) :
    empiricalLowerPrefactor S n =
      Finset.univ.prod fun _ : Fin (Fintype.card S) ↦ ((n + 1 : ℕ) : ENNReal)⁻¹ := by
  rw [empiricalLowerPrefactor]
  exact (Fin.prod_const (Fintype.card S) (((n + 1 : ℕ) : ENNReal)⁻¹)).symm

end FiniteAlphabet

section MeasureLayer

variable {S : Type u} [MeasurableSpace S]

/-- The probability that an i.i.d. word with letter law `μ` has empirical distribution `ν`. -/
def empiricalDistributionProbability [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (n : ℕ)
    (ν : ProbabilityMeasure S) : ENNReal :=
  ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) : Measure (Fin n → S))
    (empiricalDistributionEvent n ν)

-- Proof sketch: unfold `empiricalDistributionProbability`; it is the measure of the empirical-law
-- event under the product law `ProbabilityMeasure.pi (fun _ : Fin n ↦ μ)`.
/-- Expanding `empiricalDistributionProbability μ n ν` gives the product-law mass of the event that
the empirical distribution equals `ν`. -/
theorem empiricalDistributionProbability_def
    [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (n : ℕ) (ν : ProbabilityMeasure S) :
    empiricalDistributionProbability μ n ν =
      ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) :
        Measure (Fin n → S)) (empiricalDistributionEvent n ν) := rfl

-- Proof sketch: count the words with empirical law `ν` by multinomial coefficients, rewrite the
-- common product weight as `exp (-n * H(ν | μ))`, then bound the multinomial multiplicity between
-- `empiricalLowerPrefactor n * exp (n * H(ν))` and `exp (n * H(ν))`.
/-- Lemma 23.12: for every `n` and every empirical distribution `ν ∈ E_n`, the probability that an
i.i.d. sample with one-letter law `μ` has empirical distribution `ν` is bounded below by
`(n + 1)^{-#S} exp (-n H(ν | μ))` and above by `exp (-n H(ν | μ))`, where the relative entropy is
the canonical Kullback-Leibler divergence `klDiv (ν : Measure S) (μ : Measure S)`. -/
theorem empiricalDistributionProbability_sanov_bounds
    [Fintype S] [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (n : ℕ) (ν : ProbabilityMeasure S)
    (hν : ν ∈ empiricalDistributions n) :
    empiricalLowerPrefactor S n *
        EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) ≤
      empiricalDistributionProbability μ n ν ∧
      empiricalDistributionProbability μ n ν ≤
        EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := sorry

end MeasureLayer

end ProbabilityTheory
