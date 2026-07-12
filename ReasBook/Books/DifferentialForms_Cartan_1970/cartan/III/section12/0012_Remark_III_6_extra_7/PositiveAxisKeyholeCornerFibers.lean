import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeBranchInjective

open Filter MeasureTheory Bornology

open scoped unitInterval

noncomputable section


/-- Helper for Remark III.6-extra-7: the upper outer corner of the keyhole contour is hit only at the two
identified endpoint parameters `0` and `1`. This is the first exact breakpoint fiber needed for
the later simple-loop proof. -/
lemma positiveAxisKeyhole_eq_upper_outer_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) ↔
      t = (0 : I) ∨ t = (1 : I) := by
  have hr : 0 < R := lt_trans hε hεR
  have hθpos : 0 < Real.arctan (ε / R) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / R) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / R)
  have hEndsNe :
      circleMap 0 R (positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · -- The initial parameter is one endpoint of the closed loop.
      exact Or.inl (Subtype.ext hzero)
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := by
        -- On the open upper lip, the contour is the radial segment parameterized by `8 t`.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        -- Interior upper-lip parameters land in the open segment, so they cannot be a corner.
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 R (positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 ε (positiveAxisKeyholeAngle R ε))).mp hcorner
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      exact (hεR.ne hnorm.symm).elim
    · rcases
        positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo
          R ε hε hεR hinner with ⟨α, hαmemIoo, hpath⟩
      let _ := hαmemIoo
      -- The inner arc has constant radius `ε`, so it cannot hit the outer corner.
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      exact (hεR.ne hnorm.symm).elim
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := by
        -- The open lower lip is the radial segment on the lower boundary ray.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hlower)
      have hρ :
          0 <
            AffineMap.lineMap ε R (4 * (t : ℝ) - 1) := by
        -- The lower-lip radius stays in the closed interval `[ε, R]`, hence remains positive.
        have hparamI : 4 * (t : ℝ) - 1 ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap ε R (4 * (t : ℝ) - 1) ∈ Set.Icc ε R := by
          exact (convex_Icc ε R).lineMap_mem
            ⟨le_rfl, le_of_lt hεR⟩
            ⟨le_of_lt hεR, le_rfl⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hlower_im :
          (positiveAxisKeyhole R ε t).im < 0 := by
        -- Rewrite the lower lip as a fixed-angle circle point, then use the lower-ray sign.
        rw [hpath, positiveAxisKeyhole_lineMap_circleMap_same_angle]
        have hline :=
          positiveAxisKeyhole_lower_lip_line
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap ε R (4 * (t : ℝ) - 1))
        have hre :=
          positiveAxisKeyhole_lower_lip_re_pos
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap ε R (4 * (t : ℝ) - 1))
            hρ
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The target corner lies on the upper lip, hence above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper outer corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower outer corner lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases
        positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo
          R ε hε hεR houter with ⟨α, hαmemIoo, hpath⟩
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      have hαmem :
          α ∈ Set.Ico
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε) := by
        exact Set.Ioo_subset_Ico_self hαmemIoo
      have hendmem :
          positiveAxisKeyholeUpperAngle R ε ∈
            Set.Ico
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, horder.1⟩
      have hlen :
          positiveAxisKeyholeLowerAngle R ε - positiveAxisKeyholeUpperAngle R ε ≤
            2 * Real.pi := by
        linarith [horder.2]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := R)
          (a := positiveAxisKeyholeUpperAngle R ε)
          (b := positiveAxisKeyholeLowerAngle R ε)
          (by linarith : R ≠ 0) hlen
      have hcircle :
          circleMap 0 R α = circleMap 0 R (positiveAxisKeyholeUpperAngle R ε) := by
        calc
          circleMap 0 R α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 R (positiveAxisKeyholeUpperAngle R ε) := by
                simpa [positiveAxisKeyholeUpperAngle] using ht
      have hαeq : α = positiveAxisKeyholeUpperAngle R ε := hinj hαmem hendmem hcircle
      exact False.elim ((ne_of_gt hαmemIoo.1) hαeq)
    · -- The terminal parameter is the second endpoint of the closed loop.
      exact Or.inr (Subtype.ext hone)
  · rintro (rfl | rfl)
    · exact (positive_axis_keyhole_breakpoint_values R ε).1
    · exact (positive_axis_keyhole_breakpoint_values R ε).2.2.2.2

/-- Helper for Remark III.6-extra-7: the upper inner corner of the keyhole contour is hit exactly at the
first interior breakpoint `t = 1/8`. This is the second exact breakpoint fiber needed for the
later simple-loop proof. -/
lemma positiveAxisKeyhole_eq_upper_inner_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) ↔
      t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < R := lt_trans hε hεR
  have hθpos : 0 < Real.arctan (ε / R) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / R) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / R)
  have hEndsNe :
      circleMap 0 R (positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := by
        -- On the open upper lip, the contour is the open radial segment between the two corners.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        -- Interior upper-lip parameters cannot land on either endpoint of the segment.
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 ε (positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 ε (positiveAxisKeyholeAngle R ε))).mp hcorner
    · exact Subtype.ext honeEight
    · rcases
        positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo
          R ε hε hεR hinner with ⟨α, hαmemIoo, hpath⟩
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      have hαmem :
          α ∈ Set.Ico
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε) := by
        exact Set.Ioo_subset_Ico_self hαmemIoo
      have htargetmem :
          positiveAxisKeyholeUpperAngle R ε ∈
            Set.Ico
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, horder.1⟩
      have hlen :
          positiveAxisKeyholeLowerAngle R ε - positiveAxisKeyholeUpperAngle R ε ≤
            2 * Real.pi := by
        linarith [horder.2]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := ε)
          (a := positiveAxisKeyholeUpperAngle R ε)
          (b := positiveAxisKeyholeLowerAngle R ε)
          (by linarith : ε ≠ 0) hlen
      have hcircle :
          circleMap 0 ε α = circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε) := by
        calc
          circleMap 0 ε α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε) := by
                simpa [positiveAxisKeyholeUpperAngle] using ht
      have hαeq : α = positiveAxisKeyholeUpperAngle R ε := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_gt hαmemIoo.1) hαeq)
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper inner corner lies above the real axis on the upper slit boundary.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower inner corner is on the opposite slit lip, hence below the axis.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := by
        -- Lower-lip interior points stay strictly below the real axis.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hlower)
      have hρ :
          0 <
            AffineMap.lineMap ε R (4 * (t : ℝ) - 1) := by
        have hparamI : 4 * (t : ℝ) - 1 ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap ε R (4 * (t : ℝ) - 1) ∈ Set.Icc ε R := by
          exact (convex_Icc ε R).lineMap_mem
            ⟨le_rfl, le_of_lt hεR⟩
            ⟨le_of_lt hεR, le_rfl⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hlower_im :
          (positiveAxisKeyhole R ε t).im < 0 := by
        -- Convert the affine lower-lip point back to a fixed-angle circle point.
        rw [hpath, positiveAxisKeyhole_lineMap_circleMap_same_angle]
        have hline :=
          positiveAxisKeyhole_lower_lip_line
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap ε R (4 * (t : ℝ) - 1))
        have hre :=
          positiveAxisKeyhole_lower_lip_re_pos
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap ε R (4 * (t : ℝ) - 1))
            hρ
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The target corner lies on the upper slit boundary.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The target corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower outer corner still lies below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases
        positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo
          R ε hε hεR houter with ⟨α, hαmemIoo, hpath⟩
      let _ := α
      let _ := hαmemIoo
      -- The outer arc has radius `R`, so it cannot hit a corner on the inner circle.
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (positive_axis_keyhole_breakpoint_values R ε).2.1

/-- Helper for Remark III.6-extra-7: the lower inner corner of the keyhole contour is hit exactly at the
second interior breakpoint `t = 1/4`. This closes the third exact breakpoint fiber needed for
the later simple-loop proof. -/
lemma positiveAxisKeyhole_eq_lower_inner_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ↔
      t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < R := lt_trans hε hεR
  have hθpos : 0 < Real.arctan (ε / R) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / R) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / R)
  have hEndsNe :
      circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := by
        -- Upper-lip interior points stay above the real axis, unlike the lower inner corner.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hupper)
      have hρ :
          0 <
            AffineMap.lineMap R ε (8 * (t : ℝ)) := by
        have hparamI : 8 * (t : ℝ) ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap R ε (8 * (t : ℝ)) ∈ Set.Icc ε R := by
          exact (convex_Icc ε R).lineMap_mem
            ⟨le_of_lt hεR, le_rfl⟩
            ⟨le_rfl, le_of_lt hεR⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hupper_im :
          0 < (positiveAxisKeyhole R ε t).im := by
        -- Convert the affine upper-lip point back to a fixed-angle circle point.
        rw [hpath, positiveAxisKeyhole_lineMap_circleMap_same_angle]
        have hline :=
          positiveAxisKeyhole_upper_lip_line
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap R ε (8 * (t : ℝ)))
        have hre :=
          positiveAxisKeyhole_upper_lip_re_pos
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap R ε (8 * (t : ℝ)))
            hρ
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target corner lies on the lower slit boundary.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper inner corner is above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target corner is below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases
        positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo
          R ε hε hεR hinner with ⟨α, hαmemIoo, hpath⟩
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      have hαmem :
          α ∈ Set.uIoc
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε) := by
        rw [Set.uIoc_of_le (le_of_lt horder.1)]
        exact Set.Ioo_subset_Ioc_self hαmemIoo
      have htargetmem :
          positiveAxisKeyholeLowerAngle R ε ∈
            Set.uIoc
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε) := by
        rw [Set.uIoc_of_le (le_of_lt horder.1)]
        exact Set.mem_Ioc.mpr ⟨horder.1, le_rfl⟩
      have hlen :
          |positiveAxisKeyholeUpperAngle R ε - positiveAxisKeyholeLowerAngle R ε| ≤
            2 * Real.pi := by
        have hnonpos :
            positiveAxisKeyholeUpperAngle R ε - positiveAxisKeyholeLowerAngle R ε ≤ 0 := by
          linarith [horder.1]
        rw [abs_of_nonpos hnonpos]
        linarith [horder.2]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := ε)
          (a := positiveAxisKeyholeUpperAngle R ε)
          (b := positiveAxisKeyholeLowerAngle R ε)
          (by linarith : ε ≠ 0) hlen
      have hcircle :
          circleMap 0 ε α = circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε) := by
        calc
          circleMap 0 ε α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := ht
          _ = circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε) := by
                simpa using
                  (positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R ε ε).symm
      have hαeq : α = positiveAxisKeyholeLowerAngle R ε := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_lt hαmemIoo.2) hαeq)
    · exact Subtype.ext honeQuarter
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := by
        -- On the open lower lip, the target is the excluded left endpoint.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 R (-positiveAxisKeyholeAngle R ε))).mp hcorner
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · rcases
        positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo
          R ε hε hεR houter with ⟨α, hαmemIoo, hpath⟩
      let _ := α
      let _ := hαmemIoo
      -- The outer arc has radius `R`, so it cannot hit the inner lower corner.
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (positive_axis_keyhole_breakpoint_values R ε).2.2.1

/-- Helper for Remark III.6-extra-7: the lower outer corner of the keyhole contour is hit exactly at the
third interior breakpoint `t = 1/2`. This is the last exact breakpoint fiber needed before the
simple-loop dispatcher can close. -/
lemma positiveAxisKeyhole_eq_lower_outer_corner_iff
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {t : I} :
    positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) ↔
      t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < R := lt_trans hε hεR
  have hθpos : 0 < Real.arctan (ε / R) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / R) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / R)
  have hEndsNe :
      circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ≠
        circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases positive_axis_keyhole_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The initial upper outer corner lies above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target corner is below the real axis on the lower slit boundary.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := by
        -- Upper-lip interior points stay above the real axis, unlike the target corner.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hupper)
      have hρ :
          0 <
            AffineMap.lineMap R ε (8 * (t : ℝ)) := by
        have hparamI : 8 * (t : ℝ) ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap R ε (8 * (t : ℝ)) ∈ Set.Icc ε R := by
          exact (convex_Icc ε R).lineMap_mem
            ⟨le_of_lt hεR, le_rfl⟩
            ⟨le_rfl, le_of_lt hεR⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hupper_im :
          0 < (positiveAxisKeyhole R ε t).im := by
        -- Convert the affine upper-lip point to a fixed-angle circle point.
        rw [hpath, positiveAxisKeyhole_lineMap_circleMap_same_angle]
        have hline :=
          positiveAxisKeyhole_upper_lip_line
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap R ε (8 * (t : ℝ)))
        have hre :=
          positiveAxisKeyhole_upper_lip_re_pos
            (R := R) (ε := ε)
            (ρ := AffineMap.lineMap R ε (8 * (t : ℝ)))
            hρ
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The lower outer corner lies below the axis.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 ε (positiveAxisKeyholeAngle R ε)).im := by
        -- The upper inner corner is still above the real axis.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := ε)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target corner is below the real axis.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · rcases
        positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo
          R ε hε hεR hinner with ⟨α, hαmemIoo, hpath⟩
      let _ := α
      let _ := hαmemIoo
      -- The inner arc has radius `ε`, so it cannot hit a corner on the outer circle.
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          positiveAxisKeyhole R ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := by
        -- On the open lower lip, the target is the excluded right endpoint.
        exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
          positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          positiveAxisKeyhole R ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            hparam)
      have hcorner :
          circleMap 0 R (-positiveAxisKeyholeAngle R ε) ∈
            openSegment ℝ
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε)) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (y := circleMap 0 R (-positiveAxisKeyholeAngle R ε))).mp hcorner
    · exact Subtype.ext hhalf
    · rcases
        positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo
          R ε hε hεR houter with ⟨α, hαmemIoo, hpath⟩
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      have hαmem :
          α ∈ Set.uIoc
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε) := by
        rw [Set.uIoc_of_le (le_of_lt horder.1)]
        exact Set.Ioo_subset_Ioc_self hαmemIoo
      have htargetmem :
          positiveAxisKeyholeLowerAngle R ε ∈
            Set.uIoc
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε) := by
        rw [Set.uIoc_of_le (le_of_lt horder.1)]
        exact Set.mem_Ioc.mpr ⟨horder.1, le_rfl⟩
      have hlen :
          |positiveAxisKeyholeUpperAngle R ε - positiveAxisKeyholeLowerAngle R ε| ≤
            2 * Real.pi := by
        have hnonpos :
            positiveAxisKeyholeUpperAngle R ε - positiveAxisKeyholeLowerAngle R ε ≤ 0 := by
          linarith [horder.1]
        rw [abs_of_nonpos hnonpos]
        linarith [horder.2]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := R)
          (a := positiveAxisKeyholeUpperAngle R ε)
          (b := positiveAxisKeyholeLowerAngle R ε)
          (by linarith : R ≠ 0) hlen
      have hcircle :
          circleMap 0 R α = circleMap 0 R (positiveAxisKeyholeLowerAngle R ε) := by
        calc
          circleMap 0 R α = positiveAxisKeyhole R ε t := hpath.symm
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := ht
          _ = circleMap 0 R (positiveAxisKeyholeLowerAngle R ε) := by
                simpa using
                  (positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R ε R).symm
      have hαeq : α = positiveAxisKeyholeLowerAngle R ε := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_lt hαmemIoo.2) hαeq)
    · have hbreak := positive_axis_keyhole_breakpoint_values R ε
      have hupper_im :
          0 < (circleMap 0 R (positiveAxisKeyholeAngle R ε)).im := by
        -- The terminal upper outer corner lies above the axis.
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε)).im < 0 := by
        -- The target corner remains below the axis.
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := R)
        have hre := positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := R) hr
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        simpa [htEq] using hbreak.2.2.2.2
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
  · rintro rfl
    exact (positive_axis_keyhole_breakpoint_values R ε).2.2.2.1
