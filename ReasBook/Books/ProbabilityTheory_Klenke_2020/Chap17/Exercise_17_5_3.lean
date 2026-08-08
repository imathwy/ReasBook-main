import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_41

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Layering for Exercise 17.5.3:
- core/canonical owner: a planar step law `ν : PMF (LatticePoint 2)` together with
  `[IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]`;
- bridge/view: a translation-invariant lattice transition matrix `p`, whose row at the origin
  encodes the common increment law;
- source-facing conclusion: zero mean and finite second moment force recurrence in dimension `2`. -/

-- Proof sketch: apply the two-dimensional Chung--Fuchs recurrence criterion to the canonical step
-- law `ν`; the coordinatewise vanishing first moments and the finite quadratic moment of
-- `latticeEmbedding` are exactly the standard planar hypotheses.
/-- Exercise 17.5.3 at the owner layer: a random walk on `ℤ²` with step law `ν`, zero drift, and
finite second moment is recurrent. The public statement is organized around the intrinsic
increment law rather than a chosen translation-invariant matrix presentation. -/
theorem planarRandomWalk_isRecurrent_of_zeroMean_of_finiteSecondMoment
    (ν : PMF (LatticePoint 2))
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel ν.toMeasure ^ n) P X]
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (ν x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * ν x < ⊤) :
    IsRecurrentMarkovChain P X := sorry

-- Proof sketch: if the transition matrix is translation invariant, the common increment law is
-- encoded by the row at the origin,
-- so the owner theorem above reads directly in this matrix presentation.
/-- Bridge form of Exercise 17.5.3: a translation-invariant random walk on `ℤ²` whose common
increment law `p 0` has zero mean and finite second moment is recurrent. -/
theorem translationInvariant_planarRandomWalk_isRecurrent_of_zeroMean_of_finiteSecondMoment
    (p : LatticePoint 2 → LatticePoint 2 → ENNReal)
    (P : LatticePoint 2 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 2)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hmean : ∀ i : Fin 2, ∑' x : LatticePoint 2, (x i : ℝ) * (p 0 x).toReal = 0)
    (hsecond :
      ∑' x : LatticePoint 2, ENNReal.ofReal (‖latticeEmbedding x‖ ^ 2) * p 0 x < ⊤) :
    IsRecurrentMarkovChain P X := sorry

end ProbabilityTheory
