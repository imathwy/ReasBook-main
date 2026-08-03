module

public import Topology_Munkres_2000.Book.Example_22_1.IntervalFold

public section

namespace IntervalFold

/-- Companion result for Example 22.1: the interval-folding map is surjective. -/
theorem surjective : Function.Surjective map := by
  -- Split the target interval at `1`, using one source component in each case.
  intro y
  by_cases hy : (y : ℝ) ≤ 1
  · have hx_mem : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨y.property.1, hy⟩
    have hx_domain : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∪ Set.Icc 2 3 := Or.inl hx_mem
    let x : Domain := ⟨y, hx_domain⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [coe_map, value_of_mem_left hx_mem]
  · have hy_lower : 1 < (y : ℝ) := lt_of_not_ge hy
    have hx_mem : (y : ℝ) + 1 ∈ Set.Icc (2 : ℝ) 3 := by
      constructor
      · linarith
      · linarith [y.property.2]
    have hx_domain : (y : ℝ) + 1 ∈ Set.Icc (0 : ℝ) 1 ∪ Set.Icc 2 3 := Or.inr hx_mem
    let x : Domain := ⟨(y : ℝ) + 1, hx_domain⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [coe_map, value_of_mem_right hx_mem]
    dsimp [x]
    ring

/-- Helper for Example 22.1: the formula's left branch is the part below `3 / 2`. -/
lemma branchSet_eq_preimage_Iio :
    {x : Domain | (x : ℝ) ∈ Set.Icc (0 : ℝ) 1} =
      Subtype.val ⁻¹' Set.Iio (3 / 2 : ℝ) := by
  -- The gap between the two intervals turns the threshold description into an exact equality.
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio]
  constructor
  · intro hx
    linarith [hx.2]
  · intro hx
    rcases x.property with hx_left | hx_right
    · exact hx_left
    · exfalso
      linarith [hx, hx_right.1]

/-- Helper for Example 22.1: the formula's left branch is both closed and open. -/
lemma isClopen_branchSet : IsClopen {x : Domain | (x : ℝ) ∈ Set.Icc (0 : ℝ) 1} := by
  -- Closedness uses its interval description; openness uses the separated-threshold description.
  constructor
  · exact isClosed_Icc.preimage continuous_subtype_val
  · rw [branchSet_eq_preimage_Iio]
    exact isOpen_Iio.preimage continuous_subtype_val

/-- Companion result for Example 22.1: the interval-folding map is continuous. -/
theorem continuous : Continuous map := by
  -- The two affine formulas are continuous and the clopen branch set has empty frontier.
  classical
  have hvalue : Continuous value := by
    unfold value
    refine continuous_subtype_val.if ?_ (continuous_subtype_val.sub continuous_const)
    intro x hx
    have hx_empty : x ∈ (∅ : Set Domain) := by
      rw [← isClopen_branchSet.frontier_eq]
      exact hx
    exact False.elim hx_empty
  -- Package the continuous real-valued formula into the target subtype.
  exact hvalue.subtype_mk value_mem

/-- Companion result for Example 22.1: the interval-folding map is closed. -/
theorem isClosedMap : IsClosedMap map := by
  -- The source is compact, so continuity into the Hausdorff target implies closedness.
  letI : CompactSpace Domain :=
    isCompact_iff_compactSpace.mp
      ((isCompact_Icc (α := ℝ)).union (isCompact_Icc (α := ℝ)))
  exact continuous.isClosedMap

/-- Example 22.1: The interval-folding map is a quotient map. -/
theorem isQuotientMap : Topology.IsQuotientMap map := by
  -- A continuous, surjective, closed map is a quotient map.
  exact isClosedMap.isQuotientMap continuous surjective

/-- Companion result for Example 22.1: the left component is open in the source subspace. -/
theorem isOpen_leftComponent : IsOpen leftComponent := by
  -- Normalize the named component to the clopen branch set used by the continuity proof.
  rw [leftComponent_eq_preimage_Icc]
  exact isClopen_branchSet.isOpen

/-- Helper for Example 22.1: the left component maps exactly onto the left half of the target. -/
lemma image_leftComponent_eq_preimage_Iic :
    map '' leftComponent = Subtype.val ⁻¹' Set.Iic (1 : ℝ) := by
  -- Compare the two subsets pointwise and use the left-branch computation in both directions.
  ext y
  constructor
  · rintro ⟨x, hx_left, rfl⟩
    rw [leftComponent_eq_preimage_Icc] at hx_left
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [coe_map, value_of_mem_left hx_left]
    exact hx_left.2
  · intro hy
    simp only [Set.mem_preimage, Set.mem_Iic] at hy
    have hy_left : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨y.property.1, hy⟩
    have hy_domain : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∪ Set.Icc 2 3 := Or.inl hy_left
    let x : Domain := ⟨y, hy_domain⟩
    have hx_left : x ∈ leftComponent := by
      rw [leftComponent_eq_preimage_Icc]
      exact hy_left
    refine ⟨x, hx_left, ?_⟩
    apply Subtype.ext
    rw [coe_map, value_of_mem_left hy_left]

/-- Helper for Example 22.1: the left half `[0, 1]` is not open in `[0, 2]`. -/
lemma not_isOpen_leftHalf :
    ¬ IsOpen (Subtype.val ⁻¹' Set.Iic (1 : ℝ) : Set Codomain) := by
  -- At the endpoint `1`, every target-subspace ball contains a point strictly above `1`.
  intro hopen
  have hone_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by norm_num
  let one : Codomain := ⟨1, hone_mem⟩
  have hone_left : one ∈ (Subtype.val ⁻¹' Set.Iic (1 : ℝ) : Set Codomain) := by
    simp [one]
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hopen one hone_left
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hε_pos) (by norm_num)
  have hδ_lt_ε : δ < ε := by
    have hδ_le : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  have hz_mem : 1 + δ ∈ Set.Icc (0 : ℝ) 2 := by
    constructor
    · linarith
    · linarith
  let z : Codomain := ⟨1 + δ, hz_mem⟩
  have hz_ball : z ∈ Metric.ball one ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    dsimp [z, one]
    rw [Real.dist_eq]
    simp only [add_sub_cancel_left, abs_of_pos hδ_pos]
    exact hδ_lt_ε
  have hz_left := hε_ball hz_ball
  simp only [Set.mem_preimage, Set.mem_Iic] at hz_left
  dsimp [z] at hz_left
  linarith

/-- Companion result for Example 22.1:
the image of the left component is not open in the target subspace. -/
theorem not_isOpen_image_leftComponent : ¬ IsOpen (map '' leftComponent) := by
  -- Rewrite the image to the canonical non-open half interval.
  rw [image_leftComponent_eq_preimage_Iic]
  exact not_isOpen_leftHalf

/-- Companion result for Example 22.1: the interval-folding map is not an open map. -/
theorem not_isOpenMap : ¬ IsOpenMap map := by
  -- An open map would send the open left component to an open subset of the target.
  intro hopen
  exact not_isOpen_image_leftComponent (hopen leftComponent isOpen_leftComponent)

end IntervalFold

end
