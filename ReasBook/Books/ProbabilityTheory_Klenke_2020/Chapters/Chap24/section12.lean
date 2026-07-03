import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_24_12 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

variable {Ω : Type v} [MeasurableSpace Ω]
variable {E : Type u} [PseudoMetricSpace E] [MeasurableSpace E]

/-- The intensity measure of a kernel-valued random measure is the averaged measure obtained by
composing the kernel with the ambient probability measure. -/
abbrev kernelIntensityMeasure (P : ProbabilityMeasure Ω) (X : Kernel Ω E) : Measure E :=
  X ∘ₘ (P : Measure Ω)

-- Proof sketch: `kernelIntensityMeasure P X` is definitionally the kernel-measure composition
-- `X ∘ₘ (P : Measure Ω)`, so the displayed formula is just the standard application rule for
-- measure composition on measurable sets.
/-- On measurable sets, `kernelIntensityMeasure` is given by averaging the kernel evaluations. -/
theorem kernelIntensityMeasure_apply
    (P : ProbabilityMeasure Ω) (X : Kernel Ω E) {A : Set E} (hA : MeasurableSet A) :
    kernelIntensityMeasure P X A = ∫⁻ ω, X ω A ∂(P : Measure Ω) := sorry

/-- A kernel-valued random measure has independent increments if evaluations on every finite family
of pairwise disjoint measurable sets are independent random variables. -/
def KernelHasIndependentIncrements (P : ProbabilityMeasure Ω) (X : Kernel Ω E) : Prop :=
  ∀ n, ∀ A : Fin n → Set E,
    (∀ i, MeasurableSet (A i)) →
    Pairwise (fun i j ↦ Disjoint (A i) (A j)) →
    iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)

-- Proof sketch: unfold `KernelHasIndependentIncrements`; the statement is exactly the finite-family
-- independence condition for evaluations on pairwise disjoint measurable sets.
/-- Unfolding `KernelHasIndependentIncrements` gives the textbook independent-increments criterion
for a measure-valued kernel. -/
theorem kernelHasIndependentIncrements_iff (P : ProbabilityMeasure Ω) (X : Kernel Ω E) :
    KernelHasIndependentIncrements P X ↔
      ∀ n, ∀ A : Fin n → Set E,
        (∀ i, MeasurableSet (A i)) →
        Pairwise (fun i j ↦ Disjoint (A i) (A j)) →
        iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω) := sorry

/-- The Poisson law with parameter `lam`, viewed as a measure on `ℝ≥0∞` via the canonical
embedding
`ℕ ↪ ℝ≥0∞`. -/
def poissonCountMeasure (lam : NNReal) : Measure ENNReal :=
  Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure lam)

-- Proof sketch: unfold `poissonCountMeasure`; the right-hand side is exactly the pushforward of
-- the canonical Poisson law on `ℕ` along the inclusion `ℕ ↪ ℝ≥0∞`.
/-- Unfolding `poissonCountMeasure` gives the pushforward of the canonical Poisson law on `ℕ`. -/
theorem poissonCountMeasure_def (lam : NNReal) :
    poissonCountMeasure lam =
      Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure lam) := sorry

/-- A kernel-valued random measure is a Poisson point process with intensity candidate `μ` if it
has independent increments and every finite-intensity measurable evaluation has the Poisson law
with parameter prescribed by `μ`. -/
def IsPoissonPointProcess (P : ProbabilityMeasure Ω) (X : Kernel Ω E) (μ : Measure E) : Prop :=
  KernelHasIndependentIncrements P X ∧
    ∀ A : Set E, MeasurableSet A → μ A < ∞ →
      HasLaw (fun ω ↦ X ω A)
        (poissonCountMeasure ((μ A).toNNReal))
        (P : Measure Ω)

-- Proof sketch: unfold `IsPoissonPointProcess`; the statement is exactly the conjunction of the
-- independent-increments clause and the finite-intensity Poisson count laws.
/-- Unfolding `IsPoissonPointProcess` gives independent increments together with the Poisson laws
for all finite-intensity measurable counts. -/
theorem isPoissonPointProcess_iff (P : ProbabilityMeasure Ω) (X : Kernel Ω E)
    (μ : Measure E) :
    IsPoissonPointProcess P X μ ↔
      KernelHasIndependentIncrements P X ∧
        ∀ A : Set E, MeasurableSet A → μ A < ∞ →
          HasLaw (fun ω ↦ X ω A)
            (poissonCountMeasure ((μ A).toNNReal))
            (P : Measure Ω) := sorry

-- Proof sketch: first use the boundedly finite hypothesis to obtain the sigma-finite
-- decomposition from the textbook argument, then construct independent Poisson random measures on
-- the finite pieces, superpose them, and identify the resulting finite-intensity count laws and
-- averaged intensity measure.
/-- Theorem 24.12: every boundedly finite intensity measure on `E` is the intensity measure of some
Poisson point process. -/
theorem exists_poisson_point_process_with_intensity_measure
    (μ : Measure E)
    (hμ : ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A → μ A < ∞) :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω) (X : Kernel Ω E),
      IsPoissonPointProcess P X μ ∧ kernelIntensityMeasure P X = μ := sorry
