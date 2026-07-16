import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Theorem_17_41
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Definition_18_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Definition_18_5
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Example_18_6
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']

/- Layering for Exercise 18.2.3:
- source-facing conclusion: for an aperiodic irreducible recurrent lattice random walk, the
  independent coalescent coupling succeeds from every starting pair;
- core/canonical owner: the increment law `ν : PMF (LatticePoint d)` with owner kernel
  `dirac_convolution_kernel ν.toMeasure`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law. -/

-- Proof sketch: let the two coordinates evolve independently until they meet, and consider their
-- difference process on `ℤ^d`. Translation invariance makes this difference a recurrent random
-- walk, so it hits `0` almost surely from every initial displacement. Once the independent
-- coalescent reaches the diagonal, `independentCoalescentMatrix` keeps the two coordinates
-- together forever, which is exactly the success criterion from Definition 18.5.
/-- Exercise 18.2.3 at the owner layer: if `X` is an aperiodic irreducible recurrent random walk
on `ℤ^d` with increment law `ν`, then every realization of the associated independent coalescent
chain is a successful Markov coupling. -/
theorem independentCoalescent_isSuccessfulMarkovCoupling_of_aperiodic_irreducible_recurrent_latticeRandomWalk
    {d : ℕ} (ν : PMF (LatticePoint d))
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    [IsMarkovProcessRealization
      (fun n ↦
        discreteMatrixKernel
          (independentCoalescentMatrix
            (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y})) ^ n)
      Pcouple Z]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint d)) (dirac_convolution_kernel ν.toMeasure)]
    (hrec : IsRecurrentMarkovChain P X)
    (haperiodic : IsAperiodic (dirac_convolution_kernel ν.toMeasure)) :
    IsSuccessfulMarkovCoupling
      (fun x y ↦ dirac_convolution_kernel ν.toMeasure x {y}) Pcouple Z := sorry

-- Proof sketch: if the walk is presented by a translation-invariant transition matrix `p`, then
-- the common increment law is encoded by the row at the origin, so the owner theorem above
-- applies to that intrinsic law.
/-- Bridge form of Exercise 18.2.3: if `X` is an aperiodic irreducible recurrent random walk on
`ℤ^d` with translation-invariant transition matrix `p`, then every realization of the associated
independent coalescent chain is a successful Markov coupling. -/
theorem
    translationInvariant_independentCoalescent_isSuccessfulMarkovCoupling_of_aperiodic_irreducible_recurrent_latticeRandomWalk
    {d : ℕ} (p : LatticePoint d → LatticePoint d → ENNReal)
    {P : LatticePoint d → ProbabilityMeasure Ω} {X : ℕ → Ω → LatticePoint d}
    {Pcouple : LatticePoint d × LatticePoint d → ProbabilityMeasure Ω'}
    {Z : ℕ → Ω' → LatticePoint d × LatticePoint d}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) Pcouple Z]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint d)) (discreteMatrixKernel p)]
    (htranslation : IsTranslationInvariantStepMatrix p)
    (hrec : IsRecurrentMarkovChain P X)
    (haperiodic : IsAperiodic (discreteMatrixKernel p)) :
    IsSuccessfulMarkovCoupling p Pcouple Z := sorry

end ProbabilityTheory
