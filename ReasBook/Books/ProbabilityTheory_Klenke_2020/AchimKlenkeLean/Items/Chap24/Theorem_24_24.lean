import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3
import ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u u' v w

namespace ProbabilityTheory

variable {Omega : Type u} [MeasurableSpace Omega]
variable {Omega' : Type u'} [MeasurableSpace Omega']
variable {E : Type v} [MeasurableSpace E]
variable {F : Type w} [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
  [BorelSpace F] [T2Space F] [LocallyCompactSpace F] [Bornology F]

/-- The intensity measure `μκ` obtained by applying the transition kernel `κ` to the source
measure `μ`. -/
abbrev kernelImageMeasure (mu : Measure E) (kappa : Kernel E F) : Measure F :=
  kappa ∘ₘ mu

-- Proof sketch: unfold `kernelImageMeasure`; this is the standard application formula for
-- composing a kernel with a measure.
/-- Evaluating `kernelImageMeasure μ κ` on a measurable set integrates the kernel rows against the
source measure `μ`. -/
theorem kernelImageMeasure_apply
    (mu : Measure E) (kappa : Kernel E F) {A : Set F} (hA : MeasurableSet A) :
    kernelImageMeasure mu kappa A = ∫⁻ x, kappa x A ∂mu := sorry

/-- The Laplace transform identity that characterizes the kernel-colored random measure `X^κ` in
Theorem 24.24. -/
def HasKernelColoredLaplaceTransform
    (P : ProbabilityMeasure Omega) (mu : Measure E)
    (kappa : Kernel E F) [IsMarkovKernel kappa] (Xkappa : Omega → Measure F)
    (hXkappa : IsRandomMeasure P Xkappa) : Prop :=
  ∀ f : CompactlySupportedContinuousMap F NNReal,
    (∫ nu, Real.exp (-∫ y, (f y : ℝ) ∂nu)
      ∂(P.map hXkappa.1.aemeasurable : Measure (Measure F))) =
      Real.exp (∫ x, ∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kappa x ∂mu)

-- Proof sketch: unfold `HasKernelColoredLaplaceTransform`; it is exactly the Poisson
-- kernel-coloring Laplace formula displayed in the textbook proof.
/-- Unfolding `HasKernelColoredLaplaceTransform` gives the exponential Laplace formula for the
kernel-colored random measure. -/
theorem hasKernelColoredLaplaceTransform_iff
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xkappa : Omega → Measure F) (hXkappa : IsRandomMeasure P Xkappa) :
    HasKernelColoredLaplaceTransform P mu kappa Xkappa hXkappa ↔
      ∀ f : CompactlySupportedContinuousMap F NNReal,
        (∫ nu, Real.exp (-∫ y, (f y : ℝ) ∂nu)
          ∂(P.map hXkappa.1.aemeasurable : Measure (Measure F))) =
          Real.exp (∫ x, ∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kappa x ∂mu) := sorry

-- Proof sketch: apply `random_measure_distribution_ext_iff_laplace_transform_eq` to the law of
-- `X^κ` and to any Poisson point process realization with intensity `μκ`. The hypothesis
-- `HasKernelColoredLaplaceTransform` gives the Laplace transform of `X^κ`, and Theorem 24.14
-- gives the same Laplace transform for the realizing `PPP_{μκ}`.
/-- Theorem 24.24: if the kernel-colored random measure `X^κ` has the textbook Laplace transform,
then its distribution agrees with the Poisson point process law `PPP_{μκ}`, represented here by
any realization `Y` of that Poisson point process law. -/
theorem kernelColoredRandomMeasure_distribution_eq_poissonPointProcessLaw
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xkappa : Omega → Measure F) (hXkappa : IsRandomMeasure P Xkappa)
    (hLaplace : HasKernelColoredLaplaceTransform P mu kappa Xkappa hXkappa)
    (P' : ProbabilityMeasure Omega') (Y : Omega' → Measure F)
    (hY : IsPoissonPointProcess (kernelImageMeasure mu kappa) P' Y) :
    P.map hXkappa.1.aemeasurable =
      poissonPointProcessLaw (kernelImageMeasure mu kappa) P' Y hY := sorry

end ProbabilityTheory
