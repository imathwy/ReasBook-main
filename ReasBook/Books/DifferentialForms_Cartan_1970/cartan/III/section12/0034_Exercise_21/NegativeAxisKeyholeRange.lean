import DifferentialForms_Cartan_1970.III.section12.«0034_Exercise_21».NegativeAxisKeyholeRegularParameters

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

lemma exercise21_radial_segment_range_subset_slitPlane_of_angle
    {ρ₀ ρ₁ φ : ℝ}
    (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi) :
    Set.range (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) ⊆ Complex.slitPlane := by
  rintro z ⟨t, rfl⟩
  -- The segment only changes the radius, and the interpolated radius stays positive.
  have hρt : 0 < AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) := by
    exact (convex_Ioi (0 : ℝ)).lineMap_mem hρ₀ hρ₁ t.2
  have hsegment_eq :
      (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) t =
        circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ (t : ℝ)) φ := by
    -- A straight interpolation along a fixed ray only interpolates the radius.
    rw [Complex.ext_iff]
    constructor <;>
      simp [Path.segment_apply, circleMap_zero_re, circleMap_zero_im,
        AffineMap.lineMap_apply_module, smul_eq_mul, add_mul] <;>
      ring
  simpa [hsegment_eq] using
    (exercise21_mem_slitPlane_circleMap_of_angle
      (ρ := AffineMap.lineMap ρ₀ ρ₁ (t : ℝ)) (φ := φ) hρt hφ.1 hφ.2)

/-- Helper for Exercise 21: a circular arc obtained by varying the angle between two admissible
endpoints stays inside `Complex.slitPlane`. -/
lemma exercise21_circle_arc_range_subset_slitPlane_of_endpoints
    {ρ α β : ℝ}
    (hρ : 0 < ρ) (hα : α ∈ Set.Ioo (-Real.pi) Real.pi) (hβ : β ∈ Set.Ioo (-Real.pi) Real.pi) :
    Set.range (((Path.segment α β).map (continuous_circleMap 0 ρ))) ⊆ Complex.slitPlane := by
  rintro z ⟨t, rfl⟩
  -- The affine angle parameter stays in `(-π, π)` because both endpoints do.
  have hangle : AffineMap.lineMap α β (t : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
    exact (convex_Ioo (-Real.pi) Real.pi).lineMap_mem hα hβ t.2
  simpa only [Path.map_coe, Function.comp_apply, Path.segment_apply] using
    (exercise21_mem_slitPlane_circleMap_of_angle
      (ρ := ρ) (φ := AffineMap.lineMap α β (t : ℝ)) hρ hangle.1 hangle.2)

/-- Helper for Exercise 21: the image of `exercise21Delta` is the union of its upper lip, inner
arc, lower lip, and outer arc. -/
theorem exercise21Delta_range_eq_four_piece_union (r ε : ℝ) :
    Set.range (exercise21Delta r ε) =
      let θ := Real.arctan (ε / r)
      let upper : Path (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) :=
        Path.segment (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ))
      let inner : Path (circleMap 0 ε (Real.pi - θ)) (circleMap 0 ε (-Real.pi + θ)) :=
        (Path.segment (Real.pi - θ) (-Real.pi + θ)).map (continuous_circleMap 0 ε)
      let lower : Path (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ)) :=
        Path.segment (circleMap 0 ε (-Real.pi + θ)) (circleMap 0 r (-Real.pi + θ))
      let outer : Path (circleMap 0 r (-Real.pi + θ)) (circleMap 0 r (Real.pi - θ)) :=
        (Path.segment (-Real.pi + θ) (Real.pi - θ)).map (continuous_circleMap 0 r)
      Set.range upper ∪ Set.range inner ∪ Set.range lower ∪ Set.range outer := by
  -- Expand the concatenation once so later proofs can work with the four canonical pieces.
  rw [exercise21Delta_def]
  simp [Path.trans_range]

/-- Helper for Exercise 21: a radial segment along a fixed argument stays inside the closed annulus
`{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r}` as soon as both endpoint radii lie in `[ε, r]`. -/
lemma exercise21_radial_segment_range_subset_closed_annulus_of_angle
    {ρ₀ ρ₁ φ r ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ₀ : ρ₀ ∈ Set.Icc ε r) (hρ₁ : ρ₁ ∈ Set.Icc ε r) :
    Set.range (Path.segment (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ)) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
  rintro z ⟨t, rfl⟩
  have hρt : AffineMap.lineMap ρ₀ ρ₁ (t : ℝ) ∈ Set.Icc ε r := by
    -- Convexity of the closed interval keeps the interpolated radius between `ε` and `r`.
    exact (convex_Icc ε r).lineMap_mem hρ₀ hρ₁ t.2
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

/-- Helper for Exercise 21: a circular arc with fixed radius inside `[ε, r]` stays in the same
closed annulus. -/
lemma exercise21_circle_arc_range_subset_closed_annulus_of_radius_bounds
    {ρ α β r ε : ℝ}
    (hε : 0 ≤ ε)
    (hρ : ρ ∈ Set.Icc ε r) :
    Set.range (((Path.segment α β).map (continuous_circleMap 0 ρ))) ⊆
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
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

/-- Helper for Exercise 21: every point of the textbook keyhole contour stays in the closed annulus
`{z | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r}`. This isolates the radial control from the later slit-boundary
arguments. -/
lemma exercise21Delta_range_subset_closed_annulus
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Set.range (exercise21Delta r ε) ⊆ {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hupper :
      Set.range
          (Path.segment (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The upper slit lip interpolates between the two allowed radii `r` and `ε`.
    exact exercise21_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := r) (ρ₁ := ε)
      (φ := Real.pi - Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_of_lt hεr, le_rfl⟩
      ⟨le_rfl, le_of_lt hεr⟩
  have hinner :
      Set.range
          (((Path.segment (Real.pi - Real.arctan (ε / r))
              (-Real.pi + Real.arctan (ε / r))).map (continuous_circleMap 0 ε))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The inner arc has constant radius exactly `ε`.
    exact exercise21_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := ε) (α := Real.pi - Real.arctan (ε / r))
      (β := -Real.pi + Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_rfl, le_of_lt hεr⟩
  have hlower :
      Set.range
          (Path.segment (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The lower slit lip uses the same two radii with the opposite orientation.
    exact exercise21_radial_segment_range_subset_closed_annulus_of_angle
      hε_nonneg
      (ρ₀ := ε) (ρ₁ := r)
      (φ := -Real.pi + Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_rfl, le_of_lt hεr⟩
      ⟨le_of_lt hεr, le_rfl⟩
  have houter :
      Set.range
          (((Path.segment (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r))).map (continuous_circleMap 0 r))) ⊆
        {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ r} := by
    -- The outer arc has constant radius exactly `r`.
    exact exercise21_circle_arc_range_subset_closed_annulus_of_radius_bounds
      hε_nonneg
      (ρ := r) (α := -Real.pi + Real.arctan (ε / r))
      (β := Real.pi - Real.arctan (ε / r))
      (r := r) (ε := ε)
      ⟨le_of_lt hεr, le_rfl⟩
  -- Decompose the contour into its four canonical pieces and apply the corresponding annulus bound.
  rw [exercise21Delta_range_eq_four_piece_union]
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hupper hz
      · exact hinner hz
    · exact hlower hz
  · exact houter hz

/-- Helper for Exercise 21: every point of the textbook keyhole contour `δ(r, ε)` stays in
`Complex.slitPlane`, so the principal branch of `Complex.log` is available all along the contour. -/
lemma exercise21Delta_range_subset_slitPlane
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) :
    Set.range (exercise21Delta r ε) ⊆ Complex.slitPlane := by
  -- Route correction: the stable Lean interface is `Set.range`, not path-extension formulas.
  -- Decompose the contour once, then prove each of the four canonical pieces stays in the slit.
  have hr : 0 < r := lt_trans hε hεr
  have hθ :
      0 < Real.arctan (ε / r) ∧ Real.arctan (ε / r) < Real.pi / 2 :=
    exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
  have hupperAngle : Real.pi - Real.arctan (ε / r) ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · nlinarith [hθ.2, Real.pi_pos]
    · nlinarith [hθ.1]
  have hlowerAngle : -Real.pi + Real.arctan (ε / r) ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor
    · nlinarith [hθ.1]
    · nlinarith [hθ.2, Real.pi_pos]
  have hupper :
      Set.range
          (Path.segment (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))) ⊆ Complex.slitPlane := by
    -- The upper slit lip is a radial segment on the admissible ray `arg = π - θ`.
    exact exercise21_radial_segment_range_subset_slitPlane_of_angle hr hε hupperAngle
  have hinner :
      Set.range
          (((Path.segment (Real.pi - Real.arctan (ε / r))
              (-Real.pi + Real.arctan (ε / r))).map (continuous_circleMap 0 ε))) ⊆
        Complex.slitPlane := by
    -- The inner circular arc keeps its angle strictly between `-π` and `π`.
    exact exercise21_circle_arc_range_subset_slitPlane_of_endpoints hε hupperAngle hlowerAngle
  have hlower :
      Set.range
          (Path.segment (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))) ⊆ Complex.slitPlane := by
    -- The lower slit lip is the same radial argument with the opposite orientation.
    exact exercise21_radial_segment_range_subset_slitPlane_of_angle hε hr hlowerAngle
  have houter :
      Set.range
          (((Path.segment (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r))).map (continuous_circleMap 0 r))) ⊆
        Complex.slitPlane := by
    -- The outer circular arc also stays away from the forbidden angle `π`.
    exact exercise21_circle_arc_range_subset_slitPlane_of_endpoints hr hlowerAngle hupperAngle
  rw [exercise21Delta_range_eq_four_piece_union]
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · rcases hz with hz | hz
      · exact hupper hz
      · exact hinner hz
    · exact hlower hz
  · exact houter hz

/-- Helper for Exercise 21: the singleton closed-path family attached to `exercise21Delta` has
union equal to the actual contour range. This is the stable interface between the explicit path
formula and the `IsOrientedBoundaryOf` family API. -/
lemma exercise21Delta_singleton_iUnion_range (r ε : ℝ) :
    (⋃ i : Unit,
        Set.range ((((fun _ : Unit ↦ (exercise21Delta r ε).toClosedPath) i).toPath))) =
      Set.range (exercise21Delta r ε) := by
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

