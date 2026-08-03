module

import Topology_Munkres_2000.Book.Example_18_5
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

public section

open Filter Topology

/-- The value `1 - 1 / (n + 1)` lies in the open unit interval. -/
theorem openUnitIntervalSeq_mem (n : ℕ) :
    1 - 1 / (n + 1 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
  -- The reciprocal is positive and at most one, placing the term between the endpoints.
  have hpos : 0 < 1 / (n + 1 : ℝ) := by
    positivity
  have hle : 1 / (n + 1 : ℝ) ≤ 1 := by
    rw [div_le_one]
    · norm_num
    · positivity
  constructor
  · linarith
  · linarith

/-- Example 43.2 (1): Reindexing the textbook sequence by `ℕ`, its `n`th term
is `1 - 1 / (n + 1)` in `Set.Ioo (-1 : ℝ) 1`. -/
@[expose]
noncomputable def openUnitIntervalSeq (n : ℕ) : Set.Ioo (-1 : ℝ) 1 :=
  ⟨1 - 1 / (n + 1 : ℝ), openUnitIntervalSeq_mem n⟩

/-- Coercing `openUnitIntervalSeq n` to `ℝ` recovers its defining formula. -/
theorem openUnitIntervalSeq_coe (n : ℕ) :
    (openUnitIntervalSeq n : ℝ) = 1 - 1 / (n + 1 : ℝ) := rfl

/-- Viewed in `ℝ`, the sequence `openUnitIntervalSeq` tends to `1`. -/
theorem tendsto_openUnitIntervalSeq_coe :
    Tendsto (fun n ↦ (openUnitIntervalSeq n : ℝ)) atTop (𝓝 1) := by
  -- Subtract the reciprocal sequence, which tends to zero, from the constant sequence one.
  simpa only [openUnitIntervalSeq_coe, sub_zero] using
    (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- Example 43.2 (2): The sequence `openUnitIntervalSeq` is Cauchy in the
inherited metric on `Set.Ioo (-1 : ℝ) 1`. -/
theorem cauchySeq_openUnitIntervalSeq : CauchySeq openUnitIntervalSeq := by
  -- Ambient convergence gives ambient Cauchyness, reflected through the subtype embedding.
  rw [CauchySeq, ← isUniformEmbedding_subtype_val.isUniformInducing.cauchy_map_iff]
  simpa only [CauchySeq, Filter.map_map, Function.comp_def] using
    tendsto_openUnitIntervalSeq_coe.cauchySeq

/-- Example 43.2 (3): The sequence `openUnitIntervalSeq` does not converge in
`Set.Ioo (-1 : ℝ) 1`. -/
theorem not_tendsto_openUnitIntervalSeq :
    ¬ ∃ x : Set.Ioo (-1 : ℝ) 1, Tendsto openUnitIntervalSeq atTop (𝓝 x) := by
  -- Any subtype limit would also be an ambient real limit, hence equal the excluded endpoint.
  rintro ⟨x, hx⟩
  have hxCoe : Tendsto (fun n ↦ (openUnitIntervalSeq n : ℝ)) atTop (𝓝 (x : ℝ)) :=
    tendsto_subtype_rng.mp hx
  have hxEq : (x : ℝ) = 1 :=
    tendsto_nhds_unique hxCoe tendsto_openUnitIntervalSeq_coe
  linarith [x.property.2]

/-- Example 43.2 (4): The open unit interval with its inherited metric is not
a complete metric space. -/
theorem not_completeSpace_openUnitInterval :
    ¬ CompleteSpace (Set.Ioo (-1 : ℝ) 1) := by
  -- Completeness would force the constructed Cauchy sequence to converge in the interval.
  intro hComplete
  letI : CompleteSpace (Set.Ioo (-1 : ℝ) 1) := hComplete
  exact not_tendsto_openUnitIntervalSeq
    (cauchySeq_tendsto_of_complete cauchySeq_openUnitIntervalSeq)

/- Example 43.2 (5): The open unit interval is homeomorphic to the real line,
and the real line is complete in its usual metric. -/
#check openUnitIntervalOrderIso.toHomeomorph
#synth CompleteSpace ℝ

/-- Example 43.2 (6): Completeness of the specified metric differs for the
homeomorphic spaces `Set.Ioo (-1 : ℝ) 1` and `ℝ`. -/
theorem openUnitInterval_completeness_mismatch :
    ¬ (CompleteSpace (Set.Ioo (-1 : ℝ) 1) ↔ CompleteSpace ℝ) := by
  -- The alleged equivalence transfers the known completeness of ℝ to the incomplete interval.
  intro hComplete
  apply not_completeSpace_openUnitInterval
  exact hComplete.mpr inferInstance
