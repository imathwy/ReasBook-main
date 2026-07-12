import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeDifferentiability

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: the image of the explicit keyhole contour is the union of
its four source-facing pieces. This isolates the `Path.trans_range` bookkeeping needed later for
the wedge-annulus frontier comparison. -/
theorem positiveAxisKeyhole_range_eq_four_piece_union (R ε : ℝ) :
    Set.range (positiveAxisKeyhole R ε) =
      let upper := positiveAxisKeyholeUpperAngle R ε
      let lower := positiveAxisKeyholeLowerAngle R ε
      let upperLip : Path (circleMap 0 R upper) (circleMap 0 ε upper) :=
        Path.segment (circleMap 0 R upper) (circleMap 0 ε upper)
      let innerArc : Path (circleMap 0 ε upper) (circleMap 0 ε lower) :=
        (Path.segment upper lower).map (continuous_circleMap 0 ε)
      let lowerLip : Path (circleMap 0 ε lower)
          (circleMap 0 R lower) :=
        Path.segment (circleMap 0 ε lower) (circleMap 0 R lower)
      let outerArc : Path (circleMap 0 R lower) (circleMap 0 R upper) :=
        (Path.segment lower upper).map (continuous_circleMap 0 R)
      Set.range upperLip ∪ Set.range innerArc ∪ Set.range lowerLip ∪ Set.range outerArc := by
  -- Expand the keyhole contour into its four explicit pieces before comparing images.
  rw [positiveAxisKeyhole_def]
  simp only [Path.trans_range]

/-- Helper for Remark III.6-extra-7: the upper slit lip is exactly the geometric image of the
radius interval `Set.uIcc R ε` under the fixed-angle circle map. -/
lemma positiveAxisKeyhole_upper_lip_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeUpperAngle R ε)) '' Set.uIcc R ε := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap R ε (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines a radius in the closed interval between `R` and `ε`.
      simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ R ε t.2
    · -- Along the upper lip only the radius changes, not the angle.
      simpa [Path.segment_apply] using
        (positiveAxisKeyhole_lineMap_circleMap_same_angle
          R ε (positiveAxisKeyholeUpperAngle R ε) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ R ε := by
      -- Reinterpret the closed radius interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric radius parameter back through the path parameter.
    simpa [Path.segment_apply] using
      positiveAxisKeyhole_lineMap_circleMap_same_angle
        R ε (positiveAxisKeyholeUpperAngle R ε) t

/-- Helper for Remark III.6-extra-7: the clockwise inner arc is exactly the image of the angular
interval between the two slit-boundary angles under `circleMap 0 ε`. -/
lemma positiveAxisKeyhole_inner_arc_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (((Path.segment
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)).map
              (continuous_circleMap 0 ε))) =
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (positiveAxisKeyholeUpperAngle R ε)
        (positiveAxisKeyholeLowerAngle R ε)
        (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines an angle between the two slit-boundary angles.
      simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε)
          t.2
    · -- The mapped segment is exactly the circle image of that affine angle parameter.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      -- Reinterpret the closed angle interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric angle parameter through the mapped path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

/-- Helper for Remark III.6-extra-7: the lower slit lip is exactly the geometric image of the
radius interval `Set.uIcc ε R` under the lower boundary angle. -/
lemma positiveAxisKeyhole_lower_lip_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (Path.segment
          (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε)) '' Set.uIcc ε R := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap ε R (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines a radius in the closed interval between `ε` and `R`.
      simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ ε R t.2
    · -- Along the lower lip only the radius changes, not the angle.
      simpa [Path.segment_apply] using
        (positiveAxisKeyhole_lineMap_circleMap_same_angle
          ε R (positiveAxisKeyholeLowerAngle R ε) (t : ℝ)).symm
  · rintro ⟨ρ, hρ, rfl⟩
    have hseg : ρ ∈ segment ℝ ε R := by
      -- Reinterpret the closed radius interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hρ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric radius parameter back through the path parameter.
    simpa [Path.segment_apply] using
      positiveAxisKeyhole_lineMap_circleMap_same_angle
        ε R (positiveAxisKeyholeLowerAngle R ε) t

/-- Helper for Remark III.6-extra-7: the outer arc is exactly the image of the angular interval
between the lower and upper slit-boundary angles under `circleMap 0 R`. -/
lemma positiveAxisKeyhole_outer_arc_range_eq_geometric
    (R ε : ℝ) :
    Set.range
        (((Path.segment
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)).map
              (continuous_circleMap 0 R))) =
      (fun φ : ℝ ↦ circleMap 0 R φ) ''
        Set.uIcc (positiveAxisKeyholeLowerAngle R ε) (positiveAxisKeyholeUpperAngle R ε) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨AffineMap.lineMap
        (positiveAxisKeyholeLowerAngle R ε)
        (positiveAxisKeyholeUpperAngle R ε)
        (t : ℝ), ?_, ?_⟩
    · -- The segment parameter determines an angle between the two slit-boundary angles.
      simpa [segment_eq_uIcc] using
        lineMap_mem_segment ℝ
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε)
          t.2
    · -- The mapped segment is exactly the circle image of that affine angle parameter.
      simp [Path.map_coe, Function.comp_apply, Path.segment_apply]
  · rintro ⟨φ, hφ, rfl⟩
    have hseg :
        φ ∈ segment ℝ
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε) := by
      -- Reinterpret the closed angle interval as the corresponding real segment.
      simpa [segment_eq_uIcc] using hφ
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    -- Repackage the geometric angle parameter through the mapped outer path.
    simp [Path.map_coe, Function.comp_apply, Path.segment_apply]

/-- Helper for Remark III.6-extra-7: the range of the positive-axis keyhole contour is the union
of the four geometric pieces from the source proof: upper lip, inner circle, lower lip, and outer
circle. -/
theorem positiveAxisKeyhole_range_eq_geometric_piece_union
    (R ε : ℝ) :
    Set.range (positiveAxisKeyhole R ε) =
      (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeUpperAngle R ε)) '' Set.uIcc R ε ∪
        (fun φ : ℝ ↦ circleMap 0 ε φ) ''
          Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) ∪
        (fun ρ : ℝ ↦ circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε)) '' Set.uIcc ε R ∪
        (fun φ : ℝ ↦ circleMap 0 R φ) ''
          Set.uIcc (positiveAxisKeyholeLowerAngle R ε) (positiveAxisKeyholeUpperAngle R ε) := by
  -- Rewrite the contour range into the four canonical path pieces before converting each one to
  -- its radius/angle image.
  rw [positiveAxisKeyhole_range_eq_four_piece_union]
  dsimp
  -- Route correction: normalize the contour image to the source geometric pieces before any
  -- frontier or simplicity argument.
  rw [positiveAxisKeyhole_upper_lip_range_eq_geometric,
    positiveAxisKeyhole_inner_arc_range_eq_geometric,
    positiveAxisKeyhole_lower_lip_range_eq_geometric,
    positiveAxisKeyhole_outer_arc_range_eq_geometric]

/-- Helper for Remark III.6-extra-7: a radial segment along a fixed argument stays inside the
closed annulus `{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}` once both endpoint radii lie in `[ε, R]`. -/
lemma positiveAxisKeyhole_radial_segment_range_subset_closed_annulus_of_angle
    {ρ₀ ρ₁ φ R ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ₀ : ρ₀ ∈ Set.Icc ε R) (hρ₁ : ρ₁ ∈ Set.Icc ε R) :
    Set.range (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  rintro z ⟨t, rfl⟩
  have hρt : AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) ∈ Set.Icc ε R := by
    -- Convexity of the closed interval keeps the interpolated radius between `ε` and `R`.
    exact (convex_Icc ε R).lineMap_mem hρ₀ hρ₁ t.2
  have hsegment_eq :
      (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) t =
        circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ (t : ℝ)) φ := by
    -- A straight interpolation between two points on the same ray only changes the radius.
    rw [Complex.ext_iff]
    constructor <;>
      simp [Path.segment_apply, circleMap_zero_re, circleMap_zero_im,
        AffineMap.lineMap_apply_module, smul_eq_mul, add_mul] <;>
      ring
  have hnorm :
      ‖(Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) t‖ =
        AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) := by
    rw [hsegment_eq, norm_circleMap_zero, abs_of_nonneg (le_trans hε hρt.1)]
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    exact hρt.1
  · rw [hnorm]
    exact hρt.2

/-- Helper for Remark III.6-extra-7: a circular arc with fixed radius in `[ε, R]` stays inside the
same closed annulus. -/
lemma positiveAxisKeyhole_circle_arc_range_subset_closed_annulus_of_radius_bounds
    {ρ α β R ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ : ρ ∈ Set.Icc ε R) :
    Set.range (((Path.segment α β).map (continuous_circleMap 0 ρ))) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  rintro z ⟨t, rfl⟩
  have hnorm :
      ‖(((Path.segment α β).map (continuous_circleMap 0 ρ)) t)‖ = ρ := by
    -- The circle map has constant norm equal to its radius.
    rw [Path.map_coe, Function.comp_apply, norm_circleMap_zero, abs_of_nonneg (le_trans hε hρ.1)]
  refine ⟨?_, ?_⟩
  · rw [hnorm]
    exact hρ.1
  · rw [hnorm]
    exact hρ.2

/-- Helper for Remark III.6-extra-7: every point of the explicit positive-axis keyhole contour
stays in the closed annulus `{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}`. This isolates the radial control before the
later wedge-frontier comparison. -/
lemma positiveAxisKeyhole_range_subset_closed_annulus
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    Set.range (positiveAxisKeyhole R ε) ⊆ {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hupper :
      Set.range
          (Path.segment
            (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The upper slit lip interpolates between the two allowed radii `R` and `ε`.
    exact positiveAxisKeyhole_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := R) (ρ₁ := ε)
      (φ := positiveAxisKeyholeUpperAngle R ε)
      (R := R) (ε := ε)
      ⟨le_of_lt hεR, le_rfl⟩
      ⟨le_rfl, le_of_lt hεR⟩
  have hinner :
      Set.range
          (((Path.segment
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)).map
                (continuous_circleMap 0 ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The inner arc has constant radius exactly `ε`.
    exact positiveAxisKeyhole_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := ε)
      (α := positiveAxisKeyholeUpperAngle R ε)
      (β := positiveAxisKeyholeLowerAngle R ε)
      (R := R) (ε := ε)
      ⟨le_rfl, le_of_lt hεR⟩
  have hlower :
      Set.range
          (Path.segment
            (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
            (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The lower slit lip uses the same two radii with the opposite orientation.
    exact positiveAxisKeyhole_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := ε) (ρ₁ := R)
      (φ := positiveAxisKeyholeLowerAngle R ε)
      (R := R) (ε := ε)
      ⟨le_rfl, le_of_lt hεR⟩
      ⟨le_of_lt hεR, le_rfl⟩
  have houter :
      Set.range
          (((Path.segment
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)).map
                (continuous_circleMap 0 R))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
    -- The outer arc has constant radius exactly `R`.
    exact positiveAxisKeyhole_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := R)
      (α := positiveAxisKeyholeLowerAngle R ε)
      (β := positiveAxisKeyholeUpperAngle R ε)
      (R := R) (ε := ε)
      ⟨le_of_lt hεR, le_rfl⟩
  -- Decompose the contour into its four canonical pieces and apply the corresponding annulus
  -- bound piecewise.
  rw [positiveAxisKeyhole_range_eq_four_piece_union]
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hupper hz
      · exact hinner hz
    · exact hlower hz
  · exact houter hz

/-- Helper for Remark III.6-extra-7: the singleton closed-path family attached to
`positiveAxisKeyhole` has union equal to the actual contour range. This is the stable interface
between the explicit path formula and the later `IsOrientedBoundaryOf` family API. -/
lemma positiveAxisKeyhole_singleton_iUnion_range (R ε : ℝ) :
    (⋃ i : Unit,
        Set.range ((((fun _ : Unit ↦ (positiveAxisKeyhole R ε).toClosedPath) i).toPath))) =
      Set.range (positiveAxisKeyhole R ε) := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    cases i
    simpa [Path.toClosedPath] using hi
  · intro hz
    refine Set.mem_iUnion.mpr ?_
    refine ⟨(), ?_⟩
    simpa [Path.toClosedPath] using hz
