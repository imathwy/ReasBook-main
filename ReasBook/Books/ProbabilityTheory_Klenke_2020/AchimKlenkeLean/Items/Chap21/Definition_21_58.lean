import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_56
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Example_21_57

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

variable {P : ℕ → ℕ → NNReal}

/-- The `n`-th partition sum defining the `p`-variation of a path on `[0, T]` along the
admissible partition sequence `P`. -/
noncomputable def partitionPVariationSum
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (p : ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    Real.rpow
      (|G (partitionNextPointUpTo P n k T) - G (P n k)|)
      p

/-- The `n`-th partition sum defining quadratic covariation on `[0, T]` along the admissible
partition sequence `P`. -/
noncomputable def partitionQuadraticCovariationSum
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    (F (partitionNextPointUpTo P n k T) - F (P n k)) *
      (G (partitionNextPointUpTo P n k T) - G (P n k))

/-- Definition 21.58 (1): `V` is a `p`-variation process for `G` along the admissible partition
sequence `P` when the partition sums converge pointwise to `V`. -/
def HasPVariationAlongPartition
    (p : ℝ) (G : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (V : PathwiseProcess) : Prop :=
  ∀ T : NNReal, Tendsto (partitionPVariationSum P p G T) atTop (nhds (V T))

namespace HasPVariationAlongPartition

/-- A `p`-variation process along `P` carries the defining convergence at each fixed time. -/
theorem tendsto_partition_sum
    [IsAdmissiblePartitionSequence P] {p : ℝ} {G : PathSpace} {V : PathwiseProcess}
    (hV : HasPVariationAlongPartition p G P V) (T : NNReal) :
    Tendsto (partitionPVariationSum P p G T) atTop (nhds (V T)) :=
  hV T

end HasPVariationAlongPartition

/-- Definition 21.58 (2): `V` is the square variation `⟨G⟩` along `P` when it is the
`2`-variation process of `G` along `P`. -/
abbrev HasSquareVariationAlongPartition
    (G : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (V : PathwiseProcess) : Prop :=
  HasPVariationAlongPartition 2 G P V

namespace HasSquareVariationAlongPartition

/-- A square-variation process along `P` carries the defining convergence at each fixed time. -/
theorem tendsto_partition_sum
    [IsAdmissiblePartitionSequence P] {G : PathSpace} {V : PathwiseProcess}
    (hV : HasSquareVariationAlongPartition G P V) (T : NNReal) :
    Tendsto (partitionPVariationSum P 2 G T) atTop (nhds (V T)) :=
  hV T

end HasSquareVariationAlongPartition

/-- A continuous path has continuous square variation along `P` if it admits a continuous
square-variation path along `P`. -/
def HasContinuousSquareVariationAlongPartition
    (G : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] : Prop :=
  ∃ V : PathSpace, HasSquareVariationAlongPartition G P V

/-- Definition 21.58 (3): the class `𝒞_qv^P` consists of continuous paths whose square variation
along `P` is represented by a continuous path. -/
def 𝒞_qvAlong
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] : Set PathSpace :=
  fun G ↦ HasContinuousSquareVariationAlongPartition G P

/- Membership in `𝒞_qvAlong P` is the derived set-level view of the owner property
`HasContinuousSquareVariationAlongPartition`. -/
theorem mem_𝒞_qvAlong_iff
    [IsAdmissiblePartitionSequence P] (G : PathSpace) :
    G ∈ 𝒞_qvAlong P ↔ HasContinuousSquareVariationAlongPartition G P :=
  Iff.rfl

/-- Definition 21.58 (4): `covFG` is a quadratic covariation process for `F` and `G` along the
admissible partition sequence `P` when the mixed partition sums converge pointwise to `covFG`. -/
def HasQuadraticCovariationAlongPartition
    (F G : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (covFG : PathwiseProcess) : Prop :=
  ∀ T : NNReal, Tendsto (partitionQuadraticCovariationSum P F G T) atTop (nhds (covFG T))

namespace HasQuadraticCovariationAlongPartition

/-- A quadratic covariation process along `P` carries the defining mixed-sum convergence at each
fixed time. -/
theorem tendsto_partition_sum
    [IsAdmissiblePartitionSequence P] {F G : PathSpace} {covFG : PathwiseProcess}
    (hcovFG : HasQuadraticCovariationAlongPartition F G P covFG) (T : NNReal) :
    Tendsto (partitionQuadraticCovariationSum P F G T) atTop (nhds (covFG T)) :=
  hcovFG T

end HasQuadraticCovariationAlongPartition

/-- The `n`-th dyadic partition sum used to define the `p`-variation of a path on `[0, T]`. -/
noncomputable abbrev dyadic_p_variation_sum
    (p : ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  partitionPVariationSum dyadicPartitionSequence p G T n

/-- The `n`-th dyadic partition sum used to define quadratic covariation on `[0, T]`. -/
noncomputable abbrev dyadic_quadratic_covariation_sum
    (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  partitionQuadraticCovariationSum dyadicPartitionSequence F G T n

/-- The dyadic specialization of Definition 21.58 (1). -/
abbrev HasPVariationAlong (p : ℝ) (G : PathSpace) (V : PathwiseProcess) : Prop :=
  HasPVariationAlongPartition p G dyadicPartitionSequence V

namespace HasPVariationAlong

/-- A dyadic `p`-variation process carries the defining convergence at each fixed time. -/
theorem tendsto_partition_sum
    {p : ℝ} {G : PathSpace} {V : PathwiseProcess} (hV : HasPVariationAlong p G V) (T : NNReal) :
    Tendsto (dyadic_p_variation_sum p G T) atTop (nhds (V T)) :=
  hV T

end HasPVariationAlong

/-- The dyadic specialization of Definition 21.58 (2). -/
abbrev HasSquareVariationAlong (G : PathSpace) (V : PathwiseProcess) : Prop :=
  HasSquareVariationAlongPartition G dyadicPartitionSequence V

/-- A continuous path has continuous square variation along the dyadic partitions if it admits a
continuous square-variation path. -/
abbrev HasContinuousSquareVariation (G : PathSpace) : Prop :=
  HasContinuousSquareVariationAlongPartition G dyadicPartitionSequence

/-- Definition 21.58 (3): the class `𝒞_qv` consists of continuous paths whose square variation
process is continuous in time along the dyadic partitions. -/
abbrev 𝒞_qv : Set PathSpace :=
  𝒞_qvAlong dyadicPartitionSequence

/- Membership in `𝒞_qv` is the derived set-level view of the owner property
`HasContinuousSquareVariation`. -/
theorem mem_𝒞_qv_iff (G : PathSpace) :
    G ∈ 𝒞_qv ↔ HasContinuousSquareVariation G :=
  Iff.rfl

/-- The dyadic specialization of Definition 21.58 (4). -/
abbrev HasQuadraticCovariationAlong
    (F G : PathSpace) (covFG : PathwiseProcess) : Prop :=
  HasQuadraticCovariationAlongPartition F G dyadicPartitionSequence covFG

namespace HasQuadraticCovariationAlong

/-- A dyadic quadratic covariation process carries the defining mixed-sum convergence at each
fixed time. -/
theorem tendsto_partition_sum
    {F G : PathSpace} {covFG : PathwiseProcess}
    (hcovFG : HasQuadraticCovariationAlong F G covFG) (T : NNReal) :
    Tendsto (dyadic_quadratic_covariation_sum F G T) atTop (nhds (covFG T)) :=
  hcovFG T

end HasQuadraticCovariationAlong

-- Proof sketch: choose continuous square-variation realizations of `F + G` and `F - G`, define
-- the mixed bracket by the polarization formula
-- `((⟨F + G⟩ - ⟨F - G⟩) / 4)_T`, and pass to the limit in the partition sums using the
-- termwise polarization identity for mixed increments.
/-- If `F + G` and `F - G` have continuous square variation along the admissible partition
sequence `P`, then the quadratic covariation `⟨F,G⟩` along `P` exists and is represented by a
continuous path. -/
theorem exists_quadratic_covariation_along_partition_of_hasContinuousSquareVariation
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] {F G : PathSpace}
    (hFsubG : HasContinuousSquareVariationAlongPartition (F - G) P)
    (hFaddG : HasContinuousSquareVariationAlongPartition (F + G) P) :
    ∃ covFG : PathSpace, HasQuadraticCovariationAlongPartition F G P covFG := sorry

/-- If `F + G` and `F - G` lie in `𝒞_qv`, then the dyadic quadratic covariation `⟨F,G⟩` exists and
is represented by a continuous path. -/
theorem exists_quadratic_covariation_along_of_hasContinuousSquareVariation
    {F G : PathSpace}
    (hFsubG : HasContinuousSquareVariation (F - G))
    (hFaddG : HasContinuousSquareVariation (F + G)) :
    ∃ covFG : PathSpace, HasQuadraticCovariationAlong F G covFG := by
  simpa using
    exists_quadratic_covariation_along_partition_of_hasContinuousSquareVariation
      dyadicPartitionSequence hFsubG hFaddG
