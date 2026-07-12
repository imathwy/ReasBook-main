import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeSegments

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: affine interpolation between two points on the same ray only
changes the radius, so the angular coordinate stays fixed. This is the transport-stable
normalization used when a branch proof should reason by radius and angle rather than by raw
complex affine formulas. -/
lemma positiveAxisKeyhole_lineMap_circleMap_same_angle (ρ₀ ρ₁ φ c : ℝ) :
    AffineMap.lineMap (circleMap 0 ρ₀ φ) (circleMap 0 ρ₁ φ) c =
      circleMap 0 (AffineMap.lineMap ρ₀ ρ₁ c) φ := by
  -- Compare real and imaginary parts separately; on a fixed ray, affine interpolation is purely
  -- radial.
  rw [Complex.ext_iff]
  constructor <;>
    simp [circleMap_zero_re, circleMap_zero_im, AffineMap.lineMap_apply_module, smul_eq_mul,
      add_mul] <;>
    ring

/-- Helper for Remark III.6-extra-7: the opening angle `θ = arctan (ε / R)` of the positive-axis
keyhole contour lies in `(0, π / 2)` whenever `0 < ε < R`. -/
lemma positiveAxisKeyhole_angle_bounds {R ε : ℝ}
    (hε : 0 < ε) (hεR : ε < R) :
    0 < positiveAxisKeyholeAngle R ε ∧ positiveAxisKeyholeAngle R ε < Real.pi / 2 := by
  have hR : 0 < R := lt_trans hε hεR
  -- The keyhole opening is acute because the slope `ε / R` is positive.
  constructor
  · simpa [positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  · simpa [positiveAxisKeyholeAngle] using Real.arctan_lt_pi_div_two (ε / R)

/-- Helper for Remark III.6-extra-7: an interior point of the upper slit lip is a point on the
upper boundary ray with radius strictly between `ε` and `R`. -/
lemma positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) :
    ∃ ρ ∈ Set.Ioo ε R,
      positiveAxisKeyhole R ε t =
        circleMap 0 ρ (positiveAxisKeyholeAngle R ε) := by
  let ρ : ℝ := AffineMap.lineMap R ε (8 * (t : ℝ))
  have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε R := by
    have hseg : ρ ∈ openSegment ℝ R ε := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) R ε hparam
    have hRe : (R : ℝ) ≠ ε := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hRe] at hseg
    simpa [ρ, min_eq_right (le_of_lt hεR), max_eq_left (le_of_lt hεR)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open upper branch using the radial parameter supplied by `lineMap`.
  calc
    positiveAxisKeyhole R ε t =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (t : ℝ)) := by
            exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
              positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (positiveAxisKeyholeAngle R ε) := by
          rw [positiveAxisKeyhole_lineMap_circleMap_same_angle]

/-- Helper for Remark III.6-extra-7: an interior point of the inner arc stays on the circle of
radius `ε` with angle strictly between the two slit-boundary angles. -/
lemma positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) :
    ∃ α ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε),
      positiveAxisKeyhole R ε t = circleMap 0 ε α := by
  let α : ℝ :=
    AffineMap.lineMap
      (positiveAxisKeyholeUpperAngle R ε)
      (positiveAxisKeyholeLowerAngle R ε)
      (8 * (t : ℝ) - 1)
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
    have hseg :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε)
          hparam
    have hneq :
        positiveAxisKeyholeUpperAngle R ε ≠ positiveAxisKeyholeLowerAngle R ε := by
      exact ne_of_lt horder.1
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    simpa [min_eq_left (le_of_lt horder.1), max_eq_right (le_of_lt horder.1)] using hseg
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open inner branch to its explicit angular parameter.
  exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
    positive_axis_keyhole_eq_on_inner_arc R ε (Set.Ioo_subset_Icc_self ht)

/-- Helper for Remark III.6-extra-7: an interior point of the lower slit lip is a point on the
lower boundary ray with radius strictly between `ε` and `R`. -/
lemma positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) :
    ∃ ρ ∈ Set.Ioo ε R,
      positiveAxisKeyhole R ε t =
        circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) := by
  let ρ : ℝ := AffineMap.lineMap ε R (4 * (t : ℝ) - 1)
  have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hρopen : ρ ∈ Set.Ioo ε R := by
    have hseg : ρ ∈ openSegment ℝ ε R := by
      simpa [ρ] using lineMap_mem_openSegment (𝕜 := ℝ) ε R hparam
    have hRe : (ε : ℝ) ≠ R := by linarith
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hRe] at hseg
    simpa [ρ, min_eq_left (le_of_lt hεR), max_eq_right (le_of_lt hεR)] using hseg
  refine ⟨ρ, hρopen, ?_⟩
  -- Rewrite the open lower branch using the corresponding radial parameter.
  calc
    positiveAxisKeyhole R ε t =
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * (t : ℝ) - 1) := by
            exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
              positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self ht)
    _ = circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) := by
          rw [positiveAxisKeyhole_lineMap_circleMap_same_angle]

/-- Helper for Remark III.6-extra-7: an interior point of the outer arc stays on the circle of
radius `R` with angle strictly between the two slit-boundary angles. -/
lemma positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)) :
    ∃ α ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε),
      positiveAxisKeyhole R ε t = circleMap 0 R α := by
  let α : ℝ :=
    AffineMap.lineMap
      (positiveAxisKeyholeLowerAngle R ε)
      (positiveAxisKeyholeUpperAngle R ε)
      (2 * (t : ℝ) - 1)
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαopen :
      α ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
    have hseg :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε)
          hparam
    have hneq :
        positiveAxisKeyholeLowerAngle R ε ≠ positiveAxisKeyholeUpperAngle R ε := by
      exact (ne_of_lt horder.1).symm
    rw [openSegment_eq_Ioo' (𝕜 := ℝ) hneq] at hseg
    simpa [min_eq_right (le_of_lt horder.1), max_eq_left (le_of_lt horder.1)] using hseg
  refine ⟨α, hαopen, ?_⟩
  -- Reduce the open outer branch to its explicit angular parameter.
  exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
    positive_axis_keyhole_eq_on_outer_arc R ε (Set.Ioo_subset_Icc_self ht)

/-- Helper for Remark III.6-extra-7: after correcting the source-facing keyhole contour, the inner
arc runs only through the angle window from `θ` to `-θ`. This records the non-overwinding geometry
needed by the simple-loop/oriented-boundary package. -/
lemma positiveAxisKeyhole_inner_arc_angle_window
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ∀ {t : I}, t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) →
      ∃ α ∈ Set.Ioo (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε),
        positiveAxisKeyhole R ε t = circleMap 0 ε α := by
  intro t ht
  exact positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR ht
