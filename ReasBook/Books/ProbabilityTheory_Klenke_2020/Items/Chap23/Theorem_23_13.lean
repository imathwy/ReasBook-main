import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter InformationTheory MeasureTheory
open scoped BigOperators Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {S : Type v} [MeasurableSpace S]

/-- The underlying measure of the empirical distribution of the first `n + 1` sample values is the
normalized sum of the Dirac masses at those values. This is the Chapter 23 sequence-indexed
specialization of the owner theorem `empiricalDistribution_toMeasure` from Definition 12.25. -/
theorem empiricalMeasure_toMeasure (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) :
    (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω : Measure S) =
      ((n + 1 : ℕ) : ENNReal)⁻¹ • ∑ i : Fin (n + 1), Measure.dirac (X i ω) := by
  simpa [Nat.succPNat, Nat.succ_eq_add_one] using
    (@empiricalDistribution_toMeasure Ω S _ _ (Nat.succPNat n) (fun i ↦ X i) ω)

section FiniteAlphabet

variable [TopologicalSpace S] [DiscreteTopology S] [BorelSpace S]

-- Proof sketch: on a finite discrete alphabet, each singleton mass of `empiricalMeasure X n` is a
-- finite average of measurable indicator functions of the events `{ω | X i ω = a}`; measurability
-- of the probability-measure-valued map follows from this finite coordinate description.
/-- The empirical-measure map is measurable for measurable coordinate maps into a finite discrete
alphabet. -/
theorem measurable_empiricalMeasure [Fintype S]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)) := sorry

/-- The law of the empirical measure `ξ_n(X)` under the reference probability measure `P`. -/
noncomputable def empiricalMeasureLaw [Fintype S] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    ProbabilityMeasure (ProbabilityMeasure S) :=
  ProbabilityMeasure.map ⟨P, inferInstance⟩
    (measurable_empiricalMeasure X hX n).aemeasurable

-- Proof sketch: unfold `empiricalMeasureLaw`; it is defined as the pushforward of `P` by the
-- empirical-measure map `empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)`.
/-- Expanding `empiricalMeasureLaw P X hX n` gives the pushforward of `P` by the empirical-measure
map `empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)`. -/
theorem empiricalMeasureLaw_def [Fintype S] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    empiricalMeasureLaw P X hX n =
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (measurable_empiricalMeasure X hX n).aemeasurable := sorry

-- Proof sketch: `InformationTheory.klDiv` is the canonical relative entropy on measures, and on a
-- finite discrete alphabet it is lower semicontinuous in the weak topology on probability
-- measures.
/-- The relative-entropy rate function `ν ↦ klDiv ν μ` is lower semicontinuous on the space of
probability measures on a finite discrete alphabet. -/
theorem lowerSemicontinuous_relativeEntropyRate
    [Fintype S]
    (μ : ProbabilityMeasure S) :
    LowerSemicontinuous
      (fun ν : ProbabilityMeasure S ↦ klDiv (ν : Measure S) (μ : Measure S)) := sorry

-- Proof sketch: use the combinatorial estimates for single empirical measures from the preceding
-- lemma, identify the exponential cost with the relative entropy `klDiv`, and pass from exact
-- empirical measures to arbitrary open sets via approximation inside the finite-dimensional
-- simplex.
/-- Theorem 23.13: Sanov's theorem. For i.i.d. `S`-valued random variables with common law `μ`, the
distributions of the empirical measures satisfy the large-deviation upper bound on closed sets and
the lower bound on open sets; in the chapter's `0`-based indexing, the `n`th empirical measure
uses the first `n + 1` samples, so the speed is `n + 1`, and the rate function is the relative
entropy `ν ↦ klDiv (ν : Measure S) (μ : Measure S)`. -/
theorem sanov_empiricalMeasure_largeDeviations
    [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ) :
    (∀ s : Set (ProbabilityMeasure S), IsClosed s →
      Filter.limsup
          (fun n : ℕ ↦
            ((n + 1 : ℝ) : EReal)⁻¹ *
              (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log))
          atTop
        ≤ -sInf ((fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s)) ∧
      ∀ s : Set (ProbabilityMeasure S), IsOpen s →
        -sInf ((fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s) ≤
          Filter.liminf
            (fun n : ℕ ↦
              ((n + 1 : ℝ) : EReal)⁻¹ *
              (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log))
            atTop := sorry

end FiniteAlphabet

end ProbabilityTheory
