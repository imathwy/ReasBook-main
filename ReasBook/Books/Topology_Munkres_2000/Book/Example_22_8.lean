module

public import Topology_Munkres_2000.Book.Definition_22_2
public import Topology_Munkres_2000.Book.Example_22_1

public section

namespace IntervalFold.Restriction

/-- The subspace `[0, 1) ∪ [2, 3]` of `IntervalFold.Domain` used in Example 22.8. -/
def domain : Set IntervalFold.Domain :=
  Subtype.val ⁻¹' (Set.Ico (0 : ℝ) 1 ∪ Set.Icc 2 3)

/-- Membership in the restricted domain is membership in `[0, 1) ∪ [2, 3]` on `ℝ`. -/
theorem mem_domain (x : IntervalFold.Domain) :
    x ∈ domain ↔ (x : ℝ) ∈ Set.Ico (0 : ℝ) 1 ∪ Set.Icc 2 3 :=
  Iff.rfl

/-- The restriction of `IntervalFold.map` to `domain` used in Example 22.8. -/
noncomputable abbrev map : domain → IntervalFold.Codomain :=
  domain.restrict IntervalFold.map

/-- The restricted map agrees with `IntervalFold.map` after subtype projection. -/
@[simp]
theorem map_apply (x : domain) :
    map x = IntervalFold.map x.1 := rfl

/-- For Example 22.8, the restricted interval-folding map is continuous. -/
theorem continuous : Continuous map := by
  -- Restriction only precomposes the original continuous map with subtype inclusion.
  exact IntervalFold.continuous.comp continuous_subtype_val

/-- For Example 22.8, the restricted interval-folding map is surjective. -/
theorem surjective : Function.Surjective map := by
  -- Use the unchanged left branch below `1` and the translated right branch at and above `1`.
  intro y
  by_cases hy : (y : ℝ) < 1
  · have hy_left : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨y.property.1, hy.le⟩
    have hy_restricted : (y : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨y.property.1, hy⟩
    have hy_domain : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∪ Set.Icc 2 3 := Or.inl hy_left
    let x : IntervalFold.Domain := ⟨y, hy_domain⟩
    have hx_restricted : x ∈ domain := Or.inl hy_restricted
    let z : domain := ⟨x, hx_restricted⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    rw [map_apply, IntervalFold.coe_map, IntervalFold.value_of_mem_left hy_left]
  · have hy_lower : 1 ≤ (y : ℝ) := le_of_not_gt hy
    have hy_right : (y : ℝ) + 1 ∈ Set.Icc (2 : ℝ) 3 := by
      constructor
      · linarith
      · linarith [y.property.2]
    have hy_domain : (y : ℝ) + 1 ∈ Set.Icc (0 : ℝ) 1 ∪ Set.Icc 2 3 := Or.inr hy_right
    let x : IntervalFold.Domain := ⟨(y : ℝ) + 1, hy_domain⟩
    have hx_restricted : x ∈ domain := Or.inr hy_right
    let z : domain := ⟨x, hx_restricted⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    rw [map_apply, IntervalFold.coe_map, IntervalFold.value_of_mem_right hy_right]
    dsimp [x, z]
    ring

/-- The right component `[2, 3]` in the restricted domain from Example 22.8. -/
def rightComponent : Set domain :=
  fun x ↦ (x.1 : ℝ) ∈ Set.Icc (2 : ℝ) 3

/-- Membership in `rightComponent` is membership in `[2, 3]` on `ℝ`. -/
theorem mem_rightComponent (x : domain) :
    x ∈ rightComponent ↔ (x.1 : ℝ) ∈ Set.Icc (2 : ℝ) 3 :=
  Iff.rfl

/-- The interval `[1, 2]`, regarded as a subset of `IntervalFold.Codomain`. -/
def rightInterval : Set IntervalFold.Codomain :=
  Subtype.val ⁻¹' Set.Icc (1 : ℝ) 2

/-- Membership in `rightInterval` is membership in `[1, 2]` on `ℝ`. -/
theorem mem_rightInterval (y : IntervalFold.Codomain) :
    y ∈ rightInterval ↔ (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 :=
  Iff.rfl

/-- Helper for Example 22.8: the separated right component is exactly the part above `1`. -/
lemma rightComponent_eq_preimage_Ioi :
    rightComponent = (fun x : domain ↦ (x.1 : ℝ)) ⁻¹' Set.Ioi (1 : ℝ) := by
  -- The domain gap makes the threshold `1` distinguish its two components.
  ext x
  rw [mem_rightComponent]
  simp only [Set.mem_preimage, Set.mem_Ioi]
  constructor
  · intro hx
    linarith [hx.1]
  · intro hx
    have hx_domain := (mem_domain x.1).mp x.property
    rcases hx_domain with hx_left | hx_right
    · exfalso
      linarith [hx_left.2]
    · exact hx_right

/-- For Example 22.8, the right component is open in the restricted domain. -/
theorem isOpen_rightComponent : IsOpen rightComponent := by
  -- Pull back the open ray `(1, ∞)` along the two subtype projections.
  rw [rightComponent_eq_preimage_Ioi]
  exact isOpen_Ioi.preimage (continuous_subtype_val.comp continuous_subtype_val)

/-- The right component is the preimage of `[1, 2]` under the restricted map. -/
theorem preimage_rightInterval :
    map ⁻¹' rightInterval = rightComponent := by
  -- Compute the fold separately on the two components of the restricted domain.
  ext x
  simp only [Set.mem_preimage]
  rw [mem_rightInterval, mem_rightComponent, map_apply, IntervalFold.coe_map]
  have hx_domain := (mem_domain x.1).mp x.property
  rcases hx_domain with hx_left | hx_right
  · have hx_left_closed : (x.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx_left.1, hx_left.2.le⟩
    rw [IntervalFold.value_of_mem_left hx_left_closed]
    constructor
    · intro hx
      exfalso
      linarith [hx.1, hx_left.2]
    · intro hx
      exfalso
      linarith [hx.1, hx_left.2]
  · rw [IntervalFold.value_of_mem_right hx_right]
    constructor
    · intro hx
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    · intro hx
      constructor
      · linarith [hx.1]
      · linarith [hx.2]

/-- For Example 22.8, the right component is saturated with respect to the restricted map. -/
theorem isSaturated_rightComponent :
    Set.IsSaturated map rightComponent := by
  -- Rewrite the component as a complete preimage, which is saturated fiberwise.
  rw [← preimage_rightInterval]
  exact Set.isSaturated_preimage map rightInterval

/-- The image of the right component is the interval `[1, 2]` in the codomain. -/
theorem image_rightComponent :
    map '' rightComponent = rightInterval := by
  -- Surjectivity turns the complete-preimage description into the corresponding image equality.
  rw [← preimage_rightInterval]
  exact surjective.image_preimage rightInterval

/-- Helper for Example 22.8: the interval `[1, 2]` is not open in the target `[0, 2]`. -/
lemma not_isOpen_rightInterval : ¬ IsOpen rightInterval := by
  -- Every target-subspace ball at `1` contains a point strictly below `1`.
  intro hopen
  have hone_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by norm_num
  let one : IntervalFold.Codomain := ⟨1, hone_mem⟩
  have hone_right : one ∈ rightInterval := by
    rw [mem_rightInterval]
    dsimp [one]
    norm_num
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hopen one hone_right
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
    exact lt_min (half_pos hε_pos) hhalf_pos
  have hδ_lt_ε : δ < ε := by
    have hδ_le : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  have hz_mem : 1 - δ ∈ Set.Icc (0 : ℝ) 2 := by
    constructor
    · linarith
    · linarith
  let z : IntervalFold.Codomain := ⟨1 - δ, hz_mem⟩
  have hz_ball : z ∈ Metric.ball one ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    dsimp [z, one]
    rw [Real.dist_eq]
    have hdist : |1 - δ - 1| = δ := by
      have harg : 1 - (δ + 1) = -δ := by ring
      rw [sub_sub, harg, abs_neg, abs_of_pos hδ_pos]
    rw [hdist]
    exact hδ_lt_ε
  have hz_right := hε_ball hz_ball
  rw [mem_rightInterval] at hz_right
  dsimp [z] at hz_right
  linarith [hz_right.1, hδ_pos]

/-- For Example 22.8, the image `[1, 2]` is not open in the codomain. -/
theorem not_isOpen_image_rightComponent :
    ¬ IsOpen (map '' rightComponent) := by
  -- Replace the image by the non-open half interval in the target.
  rw [image_rightComponent]
  exact not_isOpen_rightInterval

/-- Example 22.8: The restricted interval-folding map is not a quotient map. -/
theorem not_isQuotientMap :
    ¬ Topology.IsQuotientMap map := by
  -- A quotient map would reflect openness from the saturated component to its image.
  intro hquot
  have hopen_preimage : IsOpen (map ⁻¹' (map '' rightComponent)) := by
    have hpreimage := Set.isSaturated_iff_preimage_image.mp isSaturated_rightComponent
    rw [hpreimage]
    exact isOpen_rightComponent
  exact not_isOpen_image_rightComponent (hquot.isOpen_preimage.mp hopen_preimage)


end IntervalFold.Restriction

end
