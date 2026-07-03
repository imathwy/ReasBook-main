import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_17_39 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section LatticeWalk

variable (D : ℕ) (P : LatticePoint D → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint D)

-- Proof sketch: identify the coordinate process as the symmetric nearest-neighbor random walk on
-- the lattice `ℤ^D`, compute or estimate the Green function at the origin, and apply the
-- recurrence criterion `G(0,0) = ∞ ↔` recurrence; this is precisely Pólya's theorem.
/-- Theorem 17.39 (1): the symmetric nearest-neighbor simple random walk on `ℤ^D` is recurrent if
and only if the dimension satisfies `D ≤ 2`. -/
theorem symmetricSimpleRandomWalk_lattice_recurrent_iff_dimension_le_two
    [NeZero D] (p : LatticePoint D → LatticePoint D → ENNReal)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (hp : IsTranslationInvariantStepMatrix p)
    (hstep : ∀ y, p 0 y = symmetricSimpleRandomWalkStepPMF D y) :
    IsRecurrentMarkovChain P X ↔ D ≤ 2 := by
  simpa using
    translationInvariant_symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two p P X hp hstep

end LatticeWalk

section OneDimensionalWalk

variable (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)

section BiasedSimpleRandomWalk

-- Proof sketch: evaluate the return probabilities at even times by the central-binomial formula,
-- resum the resulting series with the generalized binomial theorem, and rewrite the closed form
-- using `(1 - 4 p (1 - p)) ^ (1 / 2) = |2p - 1|`.
/-- Theorem 17.39 (2): for the one-dimensional nearest-neighbor walk with right-jump probability
`p` and left-jump probability `1 - p`, the Green function at the origin has the value
`1 / |2p - 1|` when `p ≠ 1 / 2` and is infinite when `p = 1 / 2`. This is the textbook formula
for `G(0,0)`. The parameter `p : I` is the canonical probability-valued owner, and the walk
kernel is derived from the step law `biasedSimpleRandomWalkStepPMF p`. -/
theorem biasedSimpleRandomWalk_greenFunction_zero_zero
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (p : I)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X] :
    (G[P, X]) 0 0 =
      if (p : ℝ) = 1 / 2 then
        ∞
      else
        ENNReal.ofReal ((|2 * (p : ℝ) - 1|)⁻¹) := sorry

/-- Companion rewrite of Theorem 17.39 (2): expanding `(G[P, X]) 0 0` via Definition 17.33
recovers the visit-probability series at the origin. -/
theorem biasedSimpleRandomWalk_visitSeries_zero_zero
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (p : I)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X] :
    (∑' n : ℕ, (P 0 : Measure Ω) {ω | X n ω = 0}) =
      if (p : ℝ) = 1 / 2 then
        ∞
      else
        ENNReal.ofReal ((|2 * (p : ℝ) - 1|)⁻¹) := by
  have hX : IsStochasticProcess X :=
    (IsMarkovProcessRealization.hasNaturalMarkovProperty
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      (P := P) (X := X) 0).1
  simpa [greenFunction_eq_tsum_stateProbabilities P X hX 0 0] using
    biasedSimpleRandomWalk_greenFunction_zero_zero P X p

-- Proof sketch: combine the preceding Green-function formula with the characterization of
-- recurrence by divergence of `G(0,0)` for the one-dimensional simple random walk.
/-- Theorem 17.39 (3): a one-dimensional simple random walk with right-jump probability `p` is
recurrent exactly in the symmetric case `p = 1 / 2`. -/
theorem biasedSimpleRandomWalk_recurrent_iff_symmetric
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (p : I)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n) P X] :
    IsRecurrentMarkovChain P X ↔ (p : ℝ) = 1 / 2 := sorry

end BiasedSimpleRandomWalk

-- Proof sketch: start from the Green-function lower bound
-- `G_N(0,0) ≥ (2L + 1)⁻¹ ∑_{|y| ≤ L} G_N(0,y)`, choose `L = εN`, apply the weak law of large
-- numbers to the centered increment law `ν`, and let `ε → 0` to force `G(0,0) = ∞`.
/-- Theorem 17.39 (4): a one-dimensional random walk on `ℤ` with finite first moment and mean-zero
increment law is recurrent. -/
theorem integerRandomWalk_recurrent_of_integrable_mean_zero
    (ν : ProbabilityMeasure ℤ)
    (hν_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) (ν : Measure ℤ))
    (hν_mean_zero : ∫ z, (z : ℝ) ∂(ν : Measure ℤ) = 0)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) P X] :
    IsRecurrentMarkovChain P X := sorry

end OneDimensionalWalk

end ProbabilityTheory
