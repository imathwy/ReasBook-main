import AchimKlenkeLean.Items.Chap17.Theorem_17_41
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Layering for Exercise 17.5.4:
- source-facing conclusion: every state of the realized walk is transient in dimension `D ≥ 3`;
- core/canonical owner: the increment law `ν : PMF (LatticePoint D)` together with
  `[IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law. -/

-- Proof sketch: combine the irreducible recurrent/transient dichotomy from Theorem 17.37 with the
-- Chung--Fuchs recurrence criterion from Theorem 17.41, whose dimension-`≥ 3` case rules out
-- recurrence for irreducible lattice random walks.
/-- Exercise 17.5.4 at the owner layer: in dimension `D ≥ 3`, every irreducible random walk on
`ℤ^D` with increment law `ν` is transient. The public statement is organized around the intrinsic
step law rather than a chosen translation-invariant matrix presentation. -/
theorem irreducible_latticeRandomWalk_isTransient
    {D : ℕ} (hD : 3 ≤ D)
    (ν : PMF (LatticePoint D))
    (P : LatticePoint D → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint D)
    [IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint D)) (dirac_convolution_kernel ν.toMeasure)] :
    ∀ x : LatticePoint D, IsTransientState P X x := sorry

-- Proof sketch: if the transition matrix is translation invariant, the row at the origin encodes
-- the intrinsic increment law, so the owner theorem above reads directly in this presentation.
/-- Bridge form of Exercise 17.5.4: in dimension `D ≥ 3`, every irreducible translation-invariant
random walk on `ℤ^D` with transition matrix `p` is transient. -/
theorem translationInvariant_irreducible_latticeRandomWalk_isTransient
    {D : ℕ} (hD : 3 ≤ D)
    (p : LatticePoint D → LatticePoint D → ENNReal)
    (P : LatticePoint D → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint D)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure (LatticePoint D)) (discreteMatrixKernel p)]
    (htranslation : IsTranslationInvariantStepMatrix p) :
    ∀ x : LatticePoint D, IsTransientState P X x := sorry

end ProbabilityTheory
