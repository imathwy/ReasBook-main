import AchimKlenkeLean.Items.Chap17.Theorem_17_39
import AchimKlenkeLean.Items.Chap19.Example_19_10
import AchimKlenkeLean.Items.Chap19.Theorem_19_25
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory unitInterval
open unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-
`source-facing`: Example 19.26 studies the nearest-neighbor simple random walk on `ℤ` and the
associated effective resistance from `0` to `∞`.
`core/canonical`: the Chapter 19 owner `effectiveResistanceToInfinity` and the canonical symmetric
nearest-neighbor walk kernel on `ℤ`, obtained from the Chapter 17 owner
`biasedSimpleRandomWalkStepPMF` at the symmetric parameter `1 / 2`, together with the owner
singleton-kernel formula `biasedSimpleRandomWalkKernel_apply_singleton`.
`bridge/view`: this file fixes the nearest-neighbor graph on `ℤ` and records the resulting
conductance family and row-normalized transition matrix.
-/

attribute [local instance] Classical.propDecidable

local notation "halfBias" =>
  (show I from ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩)

/-- The nearest-neighbor simple graph on `ℤ`: two integers are adjacent exactly when they differ
by `1`. -/
def integerNearestNeighborGraph : SimpleGraph ℤ where
  Adj x y := |x - y| = 1
  symm := by
    intro x y
    simp [abs_sub_comm]
  loopless := by
    exact ⟨by
      intro x
      simp⟩

/-- The conductance family of the nearest-neighbor network on `ℤ`, obtained from the unit edge
weights of `integerNearestNeighborGraph`. -/
def integerNearestNeighborConductance : ℤ → ℤ → ℝ≥0∞ :=
  simpleGraphWeights integerNearestNeighborGraph

/-- Evaluating the integer nearest-neighbor conductance gives the indicator of the adjacency
relation `|x - y| = 1`. -/
theorem integerNearestNeighborConductance_apply (x y : ℤ) :
    integerNearestNeighborConductance x y = if |x - y| = 1 then 1 else 0 := by
  simp [integerNearestNeighborConductance, simpleGraphWeights, integerNearestNeighborGraph]

/-- The transition matrix of the symmetric nearest-neighbor random walk on `ℤ`, obtained by
normalizing the unit edge conductances rowwise. -/
def integerNearestNeighborTransitionMatrix : ℤ → ℤ → ℝ≥0∞ :=
  conductanceTransitionMatrix integerNearestNeighborConductance

/-- Evaluating the symmetric nearest-neighbor transition matrix gives probability `1 / 2` on
adjacent integers and `0` elsewhere. -/
theorem integerNearestNeighborTransitionMatrix_apply (x y : ℤ) :
    integerNearestNeighborTransitionMatrix x y =
      if |x - y| = 1 then (1 / (2 : ℝ≥0∞)) else 0 := sorry

/-- The conductance-derived nearest-neighbor transition matrix agrees pointwise with the canonical
singleton-mass kernel of the symmetric simple random walk on `ℤ`. -/
theorem integerNearestNeighborTransitionMatrix_eq_symmetricSimpleRandomWalkKernel (x y : ℤ) :
    integerNearestNeighborTransitionMatrix x y =
      dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure x {y} :=
  sorry

/-- The canonical symmetric nearest-neighbor kernel on `ℤ` is the simple random walk on
`integerNearestNeighborGraph`, hence the random walk with weights
`integerNearestNeighborConductance`. -/
theorem integerNearestNeighborKernel_isSimpleRandomWalk :
    IsSimpleRandomWalk
      (fun x y ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure x {y})
      integerNearestNeighborGraph := by
  sorry

/-- Example 19.26: the symmetric simple random walk on `ℤ`, driven by the canonical
nearest-neighbor kernel with equal jump probabilities `1 / 2`, is recurrent. -/
theorem symmetricSimpleRandomWalk_Z_isRecurrent
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure ^ n)
      P X] :
    IsRecurrentMarkovChain P X := by
  let p : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hp : (p : ℝ) = 1 / 2 := rfl
  simpa [p] using (biasedSimpleRandomWalk_recurrent_iff_symmetric P X p).2 hp

-- Proof sketch: the edge resistances are all `1`, so the two rays from `0` act as parallel
-- copies of the divergent series of unit resistances; hence the resulting effective resistance is
-- still infinite.
/-- Example 19.26: for the symmetric nearest-neighbor walk on `ℤ`, the Chapter 19 owner
`effectiveResistanceToInfinity` of the unit-conductance network equals the textbook
series/parallel expression `(1 / 2) * ∑_{i=0}^\infty R(i,i+1)`. -/
theorem integerNearestNeighbor_effectiveResistanceToInfinity_eq_series
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure ^ n)
      P X] :
    effectiveResistanceToInfinity integerNearestNeighborConductance P X 0 =
      (1 / (2 : ℝ≥0∞)) * ∑' _ : ℕ, (1 : ℝ≥0∞) := sorry

/-- Example 19.26: for the symmetric simple random walk on `ℤ` with conductances
`C(x,y) = 𝟙_{\{|x-y|=1\}}`, the effective resistance from `0` to `∞` is infinite. -/
theorem integerNearestNeighbor_effectiveResistanceToInfinity_eq_top
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure ^ n)
      P X] :
    effectiveResistanceToInfinity integerNearestNeighborConductance P X 0 = ∞ := by
  letI :
      IsRandomWalkWithWeights
        (fun x y ↦
          dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure x {y})
        integerNearestNeighborConductance := by
    simpa [IsSimpleRandomWalk, integerNearestNeighborConductance] using
      integerNearestNeighborKernel_isSimpleRandomWalk
  have hrec : IsRecurrentMarkovChain P X := symmetricSimpleRandomWalk_Z_isRecurrent P X
  have hconductance :
      IsRecurrentState P X 0 ↔
        effectiveConductanceToInfinity integerNearestNeighborConductance P X 0 = 0 :=
    isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
      0
  have hresistance :
      effectiveConductanceToInfinity integerNearestNeighborConductance P X 0 = 0 ↔
        effectiveResistanceToInfinity integerNearestNeighborConductance P X 0 = ∞ :=
    effectiveConductanceToInfinity_eq_zero_iff_effectiveResistanceToInfinity_eq_top
      integerNearestNeighborConductance P X 0
  exact hresistance.mp (hconductance.mp (hrec 0))

end ProbabilityTheory
