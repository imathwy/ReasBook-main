import ProbabilityTheory_Klenke_2020.Chap07.Theorem_7_37

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators MeasureTheory

noncomputable section

universe u

namespace MeasureTheory
namespace Measure

variable {Ω : Type u} [MeasurableSpace Ω]

attribute [local instance] Classical.propDecidable

local notation "MeasurableFinpartition" =>
  Finpartition (⊤ : Subtype (MeasurableSet : Set Ω → Prop))

variable (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The piecewise constant density attached to a finite measurable partition, obtained by averaging
`ν` over each partition cell with respect to `μ`. This auxiliary density is only exposed in the
finite-measure setting of Example 7.39, so the cell averages are faithful real-valued quantities. -/
def partitionAverageDensity (Z : MeasurableFinpartition) : Ω → ℝ :=
  fun ω ↦
    ∑ C ∈ Z.parts,
      C.1.indicator
        (fun _ ↦ if μ C.1 = 0 then 0 else (ν C.1).toReal / (μ C.1).toReal) ω

-- Proof sketch: unfold `partitionAverageDensity`; each summand is an indicator of a nonnegative
-- constant, so every term in the finite sum is nonnegative.
/-- The partition-average density associated to a measurable finite partition is pointwise
nonnegative. -/
private theorem partitionAverageDensity_nonneg
    (Z : MeasurableFinpartition) (ω : Ω) :
    0 ≤ partitionAverageDensity μ ν Z ω := sorry

/-- The partition-average criterion from Example 7.39: the family of densities obtained by
averaging `ν` over the cells of each finite measurable partition is uniformly integrable in
`L¹(μ)`, and every such density integrates to the total mass `ν(Ω)`. -/
def PartitionAverageCriterion : Prop :=
  UniformIntegrable (fun Z : MeasurableFinpartition ↦ partitionAverageDensity μ ν Z) 1 μ ∧
    ∀ Z : MeasurableFinpartition,
      ∫ ω, partitionAverageDensity μ ν Z ω ∂μ = (ν Set.univ).toReal

-- Proof sketch: for `ν ≪ μ`, the preceding theorem gives total continuity, and the source proof
-- then yields the uniform-integrability criterion for the partition averages together with the
-- integral identity. Conversely, if the family is uniformly integrable and every partition average
-- integrates to `ν(Ω)`, test the two-cell partition `{A, Aᶜ}` for a `μ`-null set `A`.
/-- Example 7.39: for finite measures `μ` and `ν`, the family of partition-average densities
associated to finite measurable partitions of `Ω` is uniformly integrable in `L¹(μ)` and each
member integrates to `ν(Ω)` if and only if `ν` is absolutely continuous with respect to `μ`. This
is the canonical core statement; the equivalent total-continuity formulation is recorded below. -/
theorem partitionAverageDensities_uniformIntegrable_integral_iff_absolutelyContinuous :
    PartitionAverageCriterion μ ν ↔ ν ≪ μ := sorry

-- Proof sketch: combine the preceding equivalence with
-- `absolutelyContinuous_iff_totallyContinuous`.
/-- Example 7.39: for finite measures `μ` and `ν`, the following are equivalent: the family of
partition-average densities associated to finite measurable partitions of `Ω` is uniformly
integrable in `L¹(μ)` and each member integrates to `ν(Ω)`; `ν` is absolutely continuous with
respect to `μ`; and `ν` is totally continuous with respect to `μ`. -/
theorem partitionAverageDensities_tfae_absolutelyContinuous_totallyContinuous :
    List.TFAE [PartitionAverageCriterion μ ν, ν ≪ μ, TotallyContinuous ν μ] := sorry

end Measure
end MeasureTheory
