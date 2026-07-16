import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Lemma_2_40
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap14.Lemma_14_27
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_16
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Definition_18_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Definition_18_5
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/- Layering for Theorem 18.8:
- source-facing statement: an aperiodic irreducible translation-invariant stochastic transition
  matrix `p` on `ℤ^d` admits a successful coupling;
- core/canonical owner: the increment law `ν : PMF (LatticePoint d)` together with its
  convolution kernel `dirac_convolution_kernel ν.toMeasure`;
- bridge/view: translation invariance expressed by `IsTranslationInvariantStepMatrix p`, with the
  row at the origin encoding the common increment law. -/

-- Proof sketch: follow the textbook's three-step construction. First couple the walk with the
-- product model on `{-1, 0, 1}^d` coordinatewise, then split a general step law with positive mass
-- on that cube into a Bernoulli mixture of the product model and a remainder walk, and finally
-- pass to an `N`-step skeleton using irreducibility and aperiodicity to obtain the needed positive
-- cube masses before filling in the intermediate times.
/-- Theorem 18.8 at the owner layer: every aperiodic irreducible random walk on `ℤ^d` with
increment law `ν` admits a successful coupling. -/
theorem exists_successfulCoupling_of_aperiodic_irreducible_latticeRandomWalk
    {d : ℕ} (ν : PMF (LatticePoint d))
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure))
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)] :
    HasSuccessfulCoupling (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) := sorry

-- Proof sketch: for a translation-invariant stochastic transition matrix `p`, the row measure at
-- the origin is the common increment law, and the induced kernel is the owner convolution kernel
-- attached to that law.
/-- Bridge form of Theorem 18.8: every aperiodic irreducible translation-invariant stochastic
transition matrix `p` on `ℤ^d` admits a successful coupling. -/
theorem translationInvariant_exists_successfulCoupling_of_aperiodic_irreducible_latticeRandomWalk
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    (hp : IsStochasticMatrix p)
    (htranslation : IsTranslationInvariantStepMatrix p)
    (haperiodic : IsAperiodic (discreteMatrixKernel p))
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)] :
    HasSuccessfulCoupling p := sorry

end ProbabilityTheory
