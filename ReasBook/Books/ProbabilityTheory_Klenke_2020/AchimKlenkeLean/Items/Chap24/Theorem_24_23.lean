import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap24.Definition_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
variable {F : Type w} [MeasurableSpace F] [PseudoMetricSpace F] [BorelSpace F]
variable [LocallyCompactSpace F]

/-- A random measure on `E` is a Poisson point process with intensity `μ` when it is measurable,
is locally finite almost surely, has independent increments on pairwise disjoint bounded
measurable sets, and its bounded-set counts have the Poisson laws prescribed by `μ`. -/
def IsPoissonPointProcess
    (μ : Measure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  IsRandomMeasure P X ∧
    (∀ (n : ℕ) (A : Fin n → Set E),
      (∀ i, MeasurableSet (A i)) →
      (∀ i, Bornology.IsBounded (A i)) →
      Pairwise (fun i j ↦ Disjoint (A i) (A j)) →
      iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)) ∧
    IsLocallyFiniteMeasure μ ∧
    ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → (μ A) ≠ ⊤ →
      HasLaw (fun ω ↦ X ω A)
        (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure (μ A).toNNReal))
        (P : Measure Ω)

-- Proof sketch: unfold `IsPoissonPointProcess`; the statement is exactly the conjunction of the
-- random-measure, local-finiteness, independent-increments, and Poisson marginal-law conditions.
/-- Unfolding `IsPoissonPointProcess μ P X` gives the chapter's bounded-set Poisson-point-process
conditions for `X` with intensity `μ`. -/
theorem isPoissonPointProcess_iff
    (μ : Measure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E) :
    IsPoissonPointProcess μ P X ↔
      IsRandomMeasure P X ∧
        (∀ (n : ℕ) (A : Fin n → Set E),
          (∀ i, MeasurableSet (A i)) →
          (∀ i, Bornology.IsBounded (A i)) →
          Pairwise (fun i j ↦ Disjoint (A i) (A j)) →
          iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)) ∧
        IsLocallyFiniteMeasure μ ∧
        ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → (μ A) ≠ ⊤ →
          HasLaw (fun ω ↦ X ω A)
            (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure (μ A).toNNReal))
            (P : Measure Ω) := sorry

/-- The random measure obtained by coloring each point `x` of `X ω` with the mark `Y x ω`. -/
def coloredPointProcess
    (X : Ω → Measure E) (Y : E → Ω → F) : Ω → Measure (E × F) :=
  fun ω ↦ (X ω).map (fun x ↦ (x, Y x ω))

-- Proof sketch: unfold `coloredPointProcess`; by definition it pushes the realization `X ω`
-- forward along the marking map `x ↦ (x, Y x ω)`.
/-- Evaluating the colored point process at `ω` gives the pushforward of `X ω` by the mark map. -/
theorem coloredPointProcess_apply
    (X : Ω → Measure E) (Y : E → Ω → F) (ω : Ω) :
    coloredPointProcess X Y ω = (X ω).map (fun x ↦ (x, Y x ω)) := sorry

-- Proof sketch: use the atom-free hypothesis to avoid collisions of different base points after
-- marking, identify the Laplace/void probabilities of the pushforward random measure from the iid
-- mark law `ν`, and apply the Poisson point process characterization for the intensity
-- `μ.prod (ν : Measure F)`.
/-- Theorem 24.23: if `X` is a Poisson point process on `E` with atom-free intensity `μ`, and
`(Y_x)_{x ∈ E}` is an independent family of `F`-valued random variables with common law `ν`,
independent
of `X`, then coloring each point `x` of `X` by the mark `Y_x` yields a Poisson point process on
`E × F` with intensity `μ.prod (ν : Measure F)`. -/
theorem coloredPointProcess_isPoissonPointProcess
    {P : ProbabilityMeasure Ω} {μ : Measure E} [NoAtoms μ] {ν : ProbabilityMeasure F}
    {X : Ω → Measure E} (hX : IsPoissonPointProcess μ P X)
    {Y : E → Ω → F} (hY_indep : iIndepFun Y (P : Measure Ω))
    (hY_law : ∀ x : E, HasLaw (Y x) (ν : Measure F) (P : Measure Ω))
    (hXY_indep : IndepFun X (fun ω ↦ fun x ↦ Y x ω) (P : Measure Ω)) :
    IsPoissonPointProcess (μ.prod (ν : Measure F)) P (coloredPointProcess X Y) := sorry

end ProbabilityTheory
