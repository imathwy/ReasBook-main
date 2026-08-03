module

public import Topology_Munkres_2000.Book.Example_24_7.SineCurve
public import Topology_Munkres_2000.Book.Lemma_38_1.InducedCompactification

public section

open Set

namespace TopologistsSineCurve

/-- The closed square `[-1, 1]²` containing the topologist's sine curve. -/
abbrev Square := Icc (-1 : ℝ) 1 × Icc (-1 : ℝ) 1

/-- The canonical inclusion of the closed square into the real plane. -/
def squareInclusion : Square → ℝ × ℝ :=
  fun p ↦ (p.1.1, p.2.1)

/-- Helper for Example 38.3: the square inclusion returns the two underlying coordinates. -/
theorem squareInclusion_apply (p : Square) :
    squareInclusion p = (p.1.1, p.2.1) := by
  -- Evaluate the canonical inclusion at the given square point.
  rfl

/-- The first coordinate of the oscillating map lies in `[-1, 1]`. -/
theorem squareEmbedding_first_mem (x : Ioo (0 : ℝ) 1) : x.1 ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · linarith [x.2.1]
  · exact x.2.2.le

/-- The second coordinate of the oscillating map lies in `[-1, 1]`. -/
theorem squareEmbedding_second_mem (x : Ioo (0 : ℝ) 1) :
    Real.sin (1 / x.1) ∈ Icc (-1 : ℝ) 1 := by
  exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- The oscillating map `x ↦ (x, sin (1 / x))` from `(0, 1)` into `[-1, 1]²`. -/
noncomputable def squareEmbedding : Ioo (0 : ℝ) 1 → Square :=
  fun x ↦ (⟨x.1, squareEmbedding_first_mem x⟩,
    ⟨Real.sin (1 / x.1), squareEmbedding_second_mem x⟩)

/-- Helper for Example 38.3: including the square-valued oscillating map recovers its
planar formula. -/
theorem squareInclusion_squareEmbedding (x : Ioo (0 : ℝ) 1) :
    squareInclusion (squareEmbedding x) = (x.1, Real.sin (1 / x.1)) := by
  -- Evaluate both constructions to expose their common planar coordinates.
  rfl

/-- The oscillating map into the closed square is an embedding. -/
theorem isEmbedding_squareEmbedding : Topology.IsEmbedding squareEmbedding := by
  have hreciprocal : Continuous (fun x : Ioo (0 : ℝ) 1 ↦ 1 / (x.1 : ℝ)) :=
    continuous_const.div continuous_subtype_val fun x ↦ ne_of_gt x.2.1
  have hsine : Continuous (fun x : Ioo (0 : ℝ) 1 ↦ Real.sin (1 / x.1)) :=
    Real.continuous_sin.comp hreciprocal
  have hfirst : Continuous
      (fun x : Ioo (0 : ℝ) 1 ↦ (⟨x.1, squareEmbedding_first_mem x⟩ : Icc (-1 : ℝ) 1)) :=
    Continuous.subtype_mk continuous_subtype_val squareEmbedding_first_mem
  have hsecond : Continuous
      (fun x : Ioo (0 : ℝ) 1 ↦
        (⟨Real.sin (1 / x.1), squareEmbedding_second_mem x⟩ : Icc (-1 : ℝ) 1)) :=
    Continuous.subtype_mk hsine squareEmbedding_second_mem
  have hgraph : Topology.IsEmbedding
      (fun x : Ioo (0 : ℝ) 1 ↦ (x, Real.sin (1 / x.1))) :=
    isEmbedding_graph hsine
  have hforgetFirst_eq :
      (fun p : Ioo (0 : ℝ) 1 × ℝ ↦ ((p.1 : ℝ), p.2)) =
        Prod.map Subtype.val (@id ℝ) := by
    funext p
    rcases p with ⟨x, y⟩
    rfl
  have hforgetFirst : Topology.IsEmbedding
      (fun p : Ioo (0 : ℝ) 1 × ℝ ↦ ((p.1 : ℝ), p.2)) := by
    rw [hforgetFirst_eq]
    exact Topology.IsEmbedding.subtypeVal.prodMap
      (Topology.IsEmbedding.id : Topology.IsEmbedding (@id ℝ))
  have hforgetFirst_comp_graph :
      (fun x : Ioo (0 : ℝ) 1 ↦ ((x.1 : ℝ), Real.sin (1 / x.1))) =
        (fun p : Ioo (0 : ℝ) 1 × ℝ ↦ ((p.1 : ℝ), p.2)) ∘
          fun x : Ioo (0 : ℝ) 1 ↦ (x, Real.sin (1 / x.1)) := by
    funext x
    rfl
  have hembedding : Topology.IsEmbedding
      (fun x : Ioo (0 : ℝ) 1 ↦ ((x.1 : ℝ), Real.sin (1 / x.1))) := by
    rw [hforgetFirst_comp_graph]
    exact hforgetFirst.comp hgraph
  have hcomposition : squareInclusion ∘ squareEmbedding =
      fun x : Ioo (0 : ℝ) 1 ↦ ((x.1 : ℝ), Real.sin (1 / x.1)) :=
    funext squareInclusion_squareEmbedding
  -- The square map is an embedding because its planar composite is the graph embedding.
  refine Topology.IsEmbedding.of_comp (f := squareEmbedding) (g := squareInclusion) ?_ ?_ ?_
  · have hsquareEmbedding : squareEmbedding =
        fun x : Ioo (0 : ℝ) 1 ↦
          (⟨x.1, squareEmbedding_first_mem x⟩,
            ⟨Real.sin (1 / x.1), squareEmbedding_second_mem x⟩) := by
      funext x
      rfl
    rw [hsquareEmbedding]
    exact hfirst.prodMk hsecond
  · have hsquareInclusion : squareInclusion =
        fun p : Square ↦ ((p.1 : ℝ), (p.2 : ℝ)) :=
      funext squareInclusion_apply
    rw [hsquareInclusion]
    fun_prop
  · rw [hcomposition]
    exact hembedding

/-- The planar closure of the oscillating map is the topologist's sine curve. -/
theorem closure_range_squareEmbedding :
    closure (range (squareInclusion ∘ squareEmbedding)) = carrier := by
  let graph : ℝ → ℝ × ℝ := fun x ↦ (x, Real.sin (1 / x))
  have hrange : graph '' Ioo (0 : ℝ) 1 = range (squareInclusion ∘ squareEmbedding) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      simpa only [graph, Function.comp_apply] using
        squareInclusion_squareEmbedding ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      refine ⟨x.1, x.2, ?_⟩
      simpa only [graph, Function.comp_apply] using (squareInclusion_squareEmbedding x).symm
  have hone : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo]
    · exact right_mem_Icc.mpr zero_le_one
    · norm_num
  have hgraph_one : ContinuousAt graph 1 := by
    have hreciprocal_one : ContinuousAt (fun x : ℝ ↦ 1 / x) 1 :=
      continuousAt_const.div continuousAt_id one_ne_zero
    dsimp only [graph]
    exact continuousAt_id.prodMk (Real.continuous_sin.continuousAt.comp hreciprocal_one)
  have hendpoint : (1, Real.sin 1) ∈
      closure (range (squareInclusion ∘ squareEmbedding)) := by
    rw [← hrange]
    simpa only [graph, one_div, inv_one] using mem_closure_image hgraph_one hone
  apply Set.Subset.antisymm
  · apply closure_mono
    rintro _ ⟨x, rfl⟩
    refine ⟨x.1, ⟨x.2.1, x.2.2.le⟩, ?_⟩
    exact (squareInclusion_squareEmbedding x).symm
  · apply closure_minimal
    · rintro _ ⟨x, hx, rfl⟩
      by_cases hx_one : x = 1
      · subst x
        simpa only [one_div, inv_one] using hendpoint
      · apply subset_closure
        refine ⟨⟨x, hx.1, lt_of_le_of_ne hx.2 hx_one⟩, ?_⟩
        exact squareInclusion_squareEmbedding _
    · exact isClosed_closure

/-- The compactification of `(0, 1)` induced by the oscillating map. -/
@[expose]
noncomputable def compactification : Compactification (Ioo (0 : ℝ) 1) :=
  InducedCompactification.compactification squareEmbedding isEmbedding_squareEmbedding

/-- The vertical segment added at the left-hand end of the open interval. -/
def leftSegment : Set Square :=
  {p | p.1.1 = 0}

/-- Helper for Example 38.3: membership in the square's left segment means that the first
coordinate vanishes. -/
theorem mem_leftSegment_iff (p : Square) :
    p ∈ leftSegment ↔ p.1.1 = 0 := by
  -- Unfold the defining set predicate for the left segment.
  rfl

/-- The first coordinate of the added right endpoint lies in `[-1, 1]`. -/
theorem rightEndpoint_first_mem : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by
  norm_num

/-- The second coordinate of the added right endpoint lies in `[-1, 1]`. -/
theorem rightEndpoint_second_mem : Real.sin 1 ∈ Icc (-1 : ℝ) 1 := by
  exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- The single point added at the right-hand end of the open interval. -/
noncomputable def rightEndpoint : Square :=
  (⟨1, rightEndpoint_first_mem⟩, ⟨Real.sin 1, rightEndpoint_second_mem⟩)

/-- Helper for Example 38.3: the named right endpoint includes as `(1, sin 1)` in the plane. -/
theorem squareInclusion_rightEndpoint :
    squareInclusion rightEndpoint = (1, Real.sin 1) := by
  -- Evaluate the endpoint and then forget its square-membership proofs.
  rfl

/- Example 38.3 (1): The oscillating map from `(0, 1)` into the square `[-1, 1]²`. -/
#check squareEmbedding

/- Example 38.3 (2): The planar closure of the oscillating map is the topologist's
sine curve. -/
#check closure_range_squareEmbedding

/- Example 38.3 (3): The compactification of `(0, 1)` induced by the oscillating map. -/
#check compactification

/-- Helper for Example 38.3: the canonical inclusion of the square into the plane is an
embedding. -/
private lemma isEmbedding_squareInclusion :
    Topology.IsEmbedding squareInclusion := by
  -- View the inclusion as the product of the two standard subtype inclusions.
  have hinclusion :
      squareInclusion = fun p : Square ↦ ((p.1 : ℝ), (p.2 : ℝ)) :=
    funext squareInclusion_apply
  rw [hinclusion]
  exact
    (Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (fun x : Icc (-1 : ℝ) 1 ↦ (x : ℝ))).prodMap
        (Topology.IsEmbedding.subtypeVal :
          Topology.IsEmbedding (fun x : Icc (-1 : ℝ) 1 ↦ (x : ℝ)))

/-- Helper for Example 38.3: the embedded open graph is the sine curve with its right
endpoint removed. -/
private lemma range_squareInclusion_comp_squareEmbedding :
    range (squareInclusion ∘ squareEmbedding) =
      curve \ ({(1, Real.sin 1)} : Set (ℝ × ℝ)) := by
  -- Compare the two parameter intervals pointwise, accounting for the deleted endpoint.
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · refine ⟨x.1, ⟨x.2.1, x.2.2.le⟩, ?_⟩
      simpa only [Function.comp_apply] using (squareInclusion_squareEmbedding x).symm
    · intro hendpoint
      rw [Function.comp_apply, squareInclusion_squareEmbedding] at hendpoint
      have hx : x.1 = 1 := congrArg Prod.fst hendpoint
      exact (ne_of_lt x.2.2) hx
  · rintro ⟨⟨x, hx, rfl⟩, hnot_endpoint⟩
    have hx_ne : x ≠ 1 := by
      intro hx_one
      apply hnot_endpoint
      simp only [mem_singleton_iff]
      subst x
      norm_num
    refine ⟨⟨x, hx.1, lt_of_le_of_ne hx.2 hx_ne⟩, ?_⟩
    simpa only [Function.comp_apply] using squareInclusion_squareEmbedding _

/-- Helper for Example 38.3: a closure point in the square maps into the planar
topologist's sine curve. -/
private lemma squareInclusion_mem_carrier (p : Square)
    (hp : p ∈ closure (range squareEmbedding)) :
    squareInclusion p ∈ carrier := by
  -- Continuity transports the closure point, after which the established closure identity applies.
  rw [← closure_range_squareEmbedding, Set.range_comp]
  exact mem_closure_image isEmbedding_squareInclusion.continuous.continuousAt hp

/-- Helper for Example 38.3: inside the sine-curve carrier, the complement of the
punctured graph is the vertical segment together with the right endpoint. -/
private lemma not_mem_curve_sdiff_endpoint_iff (z : ℝ × ℝ) (hz : z ∈ carrier) :
    z ∉ curve \ ({(1, Real.sin 1)} : Set (ℝ × ℝ)) ↔
      z ∈ vertical ∨ z = (1, Real.sin 1) := by
  classical
  -- Decompose the carrier into its graph and vertical parts, then classify the deleted graph point.
  rw [carrier_eq_curve_union_vertical] at hz
  constructor
  · intro hnot
    rcases hz with hcurve | hvertical
    · right
      by_contra hne
      have hnot_singleton : z ∉ ({(1, Real.sin 1)} : Set (ℝ × ℝ)) := by
        simpa only [mem_singleton_iff] using hne
      exact hnot ⟨hcurve, hnot_singleton⟩
    · exact Or.inl hvertical
  · rintro (hzvertical | rfl)
    · intro hpunctured
      rcases hpunctured.1 with ⟨x, hx, rfl⟩
      rw [mem_vertical_iff] at hzvertical
      exact (ne_of_gt hx.1) hzvertical.1
    · intro hpunctured
      have hendpoint_mem :
          (1, Real.sin 1) ∈ ({(1, Real.sin 1)} : Set (ℝ × ℝ)) := by
        simp only [mem_singleton_iff]
      exact hpunctured.2 hendpoint_mem

/-- Helper for Example 38.3: the planar vertical segment and right endpoint correspond
to the named boundary subsets of the square. -/
private lemma squareInclusion_boundary_iff (p : Square) :
    (squareInclusion p ∈ vertical ∨ squareInclusion p = (1, Real.sin 1)) ↔
      p ∈ leftSegment ∨ p = rightEndpoint := by
  -- Read the planar alternatives in square coordinates, using injectivity at the endpoint.
  constructor
  · rintro (hzvertical | hendpoint)
    · left
      have hfirst : (squareInclusion p).1 = p.1.1 :=
        congrArg Prod.fst (squareInclusion_apply p)
      apply (mem_leftSegment_iff p).2
      calc
        p.1.1 = (squareInclusion p).1 := hfirst.symm
        _ = 0 := ((mem_vertical_iff _).1 hzvertical).1
    · right
      apply isEmbedding_squareInclusion.injective
      exact hendpoint.trans squareInclusion_rightEndpoint.symm
  · rintro (hleft | rfl)
    · left
      have hfirst : (squareInclusion p).1 = p.1.1 :=
        congrArg Prod.fst (squareInclusion_apply p)
      have hsecond : (squareInclusion p).2 = p.2.1 :=
        congrArg Prod.snd (squareInclusion_apply p)
      apply (mem_vertical_iff _).2
      constructor
      · calc
          (squareInclusion p).1 = p.1.1 := hfirst
          _ = 0 := (mem_leftSegment_iff p).1 hleft
      · rw [hsecond]
        exact p.2.property
    · right
      exact squareInclusion_rightEndpoint

/-- Example 38.3 (4): A point of the induced compactification is outside the embedded
copy of `(0, 1)` exactly when it lies on the left vertical segment or is the right endpoint. -/
theorem remainder_iff (y : InducedCompactification squareEmbedding) :
    y ∉ range (InducedCompactification.ofMap squareEmbedding) ↔
      InducedCompactification.inclusion squareEmbedding y ∈ leftSegment ∨
        InducedCompactification.inclusion squareEmbedding y = rightEndpoint := by
  -- First identify range membership before and after applying the injective square inclusion.
  have hrange :
      y ∈ range (InducedCompactification.ofMap squareEmbedding) ↔
        squareInclusion (InducedCompactification.inclusion squareEmbedding y) ∈
          range (squareInclusion ∘ squareEmbedding) := by
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simp only [Function.comp_apply, InducedCompactification.inclusion_ofMap]
    · rintro ⟨x, hx⟩
      refine ⟨x, Subtype.ext ?_⟩
      exact isEmbedding_squareInclusion.injective hx
  have hcarrier :
      squareInclusion (InducedCompactification.inclusion squareEmbedding y) ∈ carrier :=
    squareInclusion_mem_carrier
      (InducedCompactification.inclusion squareEmbedding y) y.property
  -- Normalize the range, classify its complement in the carrier, and return to square coordinates.
  calc
    y ∉ range (InducedCompactification.ofMap squareEmbedding) ↔
        squareInclusion (InducedCompactification.inclusion squareEmbedding y) ∉
          range (squareInclusion ∘ squareEmbedding) := not_congr hrange
    _ ↔ squareInclusion (InducedCompactification.inclusion squareEmbedding y) ∉
          curve \ ({(1, Real.sin 1)} : Set (ℝ × ℝ)) := by
      rw [range_squareInclusion_comp_squareEmbedding]
    _ ↔ squareInclusion (InducedCompactification.inclusion squareEmbedding y) ∈ vertical ∨
          squareInclusion (InducedCompactification.inclusion squareEmbedding y) =
            (1, Real.sin 1) :=
      not_mem_curve_sdiff_endpoint_iff _ hcarrier
    _ ↔ InducedCompactification.inclusion squareEmbedding y ∈ leftSegment ∨
          InducedCompactification.inclusion squareEmbedding y = rightEndpoint :=
      squareInclusion_boundary_iff _

end TopologistsSineCurve

end
