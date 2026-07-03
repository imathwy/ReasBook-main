import AchimKlenkeLean.Items.Chap14.Lemma_14_27
import AchimKlenkeLean.Items.Chap18.Theorem_18_8
import AchimKlenkeLean.Items.Chap18.Theorem_18_9
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/- Layering for Corollary 18.10:
- source-facing conclusion: every bounded harmonic function for an irreducible lattice random walk
  is constant;
- core/canonical owner: the increment law `ν : PMF (LatticePoint d)` and its convolution kernel
  `dirac_convolution_kernel ν.toMeasure`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law. -/

-- Proof sketch: realize the walk through the canonical convolution kernel determined by the step
-- law `ν`, build the successful coupling at the preceding theorem level, and then apply the
-- bounded-harmonic-function rigidity theorem to conclude that the values at any two starting
-- points coincide.
/-- Corollary 18.10 at the owner layer: for an irreducible random walk on `ℤ^d` with increment
law `ν`, every bounded harmonic function for `dirac_convolution_kernel ν.toMeasure` is constant.
-/
theorem bounded_harmonicFunction_constant_of_irreducible_latticeRandomWalk
    {d : ℕ} (ν : PMF (LatticePoint d))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    {f : LatticePoint d → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (dirac_convolution_kernel ν.toMeasure) f) :
    ∀ x y : LatticePoint d, f x = f y := sorry

-- Proof sketch: for a translation-invariant stochastic transition matrix `p`, the common
-- increment law is encoded by the row at the origin,
-- so the owner theorem above applies after reading the walk through that intrinsic law.
/-- Bridge form of Corollary 18.10: for an irreducible translation-invariant stochastic lattice
transition matrix `p`, every bounded harmonic function for `discreteMatrixKernel p` is
constant. -/
theorem translationInvariant_bounded_harmonicFunction_constant_of_irreducible_latticeRandomWalk
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (hp : IsStochasticMatrix p)
    (htranslation : IsTranslationInvariantStepMatrix p)
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    {f : LatticePoint d → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) :
    ∀ x y : LatticePoint d, f x = f y := sorry

end ProbabilityTheory
