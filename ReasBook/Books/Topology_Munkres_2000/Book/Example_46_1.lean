module

public import Topology_Munkres_2000.Book.Exercise_21_6.PowerSequence
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.UnitInterval

public section

open Filter Set Topology

/-- Helper for Example 46.1: every function in `UnitIntervalPower.sequence` is continuous. -/
theorem continuous_unitIntervalPowerSequence (n : ℕ) :
    Continuous (UnitIntervalPower.sequence n) := by
  -- Identify the opaque sequence term with the natural power of the subtype projection.
  have hsequence :
      UnitIntervalPower.sequence n =
        fun x : Set.Icc (0 : ℝ) 1 ↦ (x : ℝ) ^ n := by
    funext x
    exact UnitIntervalPower.sequence_apply n x
  rw [hsequence]
  exact continuous_subtype_val.pow n

/- Example 46.1 (2). The power functions converge pointwise on `[0, 1]` to
`UnitIntervalPower.limit`. -/
#check UnitIntervalPower.tendsto_limit

/-- Helper for Example 46.1: the pointwise limit of the power functions is not continuous. -/
theorem not_continuous_unitIntervalPowerLimit :
    ¬Continuous UnitIntervalPower.limit := by
  intro hcontinuous
  -- Continuity on the connected interval would force the midpoint value `1 / 2`.
  have hhalf_bounds :
      (1 / 2 : ℝ) ∈ Set.Icc
        (UnitIntervalPower.limit (0 : Set.Icc (0 : ℝ) 1))
        (UnitIntervalPower.limit (1 : Set.Icc (0 : ℝ) 1)) := by
    constructor
    · norm_num [UnitIntervalPower.limit_apply]
    · norm_num [UnitIntervalPower.limit_apply]
  have hhalf_range :
      (1 / 2 : ℝ) ∈ Set.range UnitIntervalPower.limit :=
    intermediate_value_univ
      (0 : Set.Icc (0 : ℝ) 1) (1 : Set.Icc (0 : ℝ) 1) hcontinuous hhalf_bounds
  obtain ⟨x, hx⟩ := hhalf_range
  -- The explicit limit takes only the values zero and one, never their midpoint.
  simp only [UnitIntervalPower.limit_apply] at hx
  split_ifs at hx
  · norm_num at hx
  · norm_num at hx

/-- Helper for Example 46.1: the pointwise limit belongs to the closure, in the product
topology, of the continuous real-valued functions on `[0, 1]`. -/
theorem unitIntervalPowerLimit_mem_closure :
    UnitIntervalPower.limit ∈
      closure {f : Set.Icc (0 : ℝ) 1 → ℝ | Continuous f} := by
  -- A limit of an eventually continuous sequence lies in the corresponding closure.
  refine mem_closure_of_tendsto UnitIntervalPower.tendsto_limit ?_
  exact Filter.Eventually.of_forall continuous_unitIntervalPowerSequence

/-- Example 46.1 (4). The continuous real-valued functions on `[0, 1]` are not closed in
the full function space with its product topology. -/
theorem not_isClosed_continuousFunctions_closedUnitInterval :
    ¬IsClosed {f : Set.Icc (0 : ℝ) 1 → ℝ | Continuous f} := by
  intro hclosed
  -- Closedness would turn closure membership of the limit into continuity.
  have hlimit_member :
      UnitIntervalPower.limit ∈
        {f : Set.Icc (0 : ℝ) 1 → ℝ | Continuous f} := by
    rw [← hclosed.closure_eq]
    exact unitIntervalPowerLimit_mem_closure
  exact not_continuous_unitIntervalPowerLimit hlimit_member
