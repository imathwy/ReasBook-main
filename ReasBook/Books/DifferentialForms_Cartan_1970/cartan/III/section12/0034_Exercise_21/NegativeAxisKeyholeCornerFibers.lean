import DifferentialForms_Cartan_1970.cartan.III.section12.«0034_Exercise_21».NegativeAxisKeyholeBranchGeometry

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

/-- Helper for Exercise 21: the upper outer corner of the keyhole contour is hit only at the two
identified endpoint parameters `0` and `1`. This is the first exact breakpoint fiber needed for
the later simple-loop proof. -/
lemma exercise21Delta_eq_upper_outer_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) ↔
      t = (0 : I) ∨ t = (1 : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 r (Real.pi - Real.arctan (ε / r)) ≠
        circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · -- The initial parameter is one endpoint of the closed loop.
      exact Or.inl (Subtype.ext hzero)
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- On the open upper lip, the contour is the radial segment parameterized by `8 t`.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        -- Interior upper-lip parameters land in the open segment, so they cannot be a corner.
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 r (Real.pi - Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (y := circleMap 0 ε (Real.pi - Real.arctan (ε / r)))).mp hcorner
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      exact (hεr.ne hnorm.symm).elim
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 ε
              (AffineMap.lineMap
                (Real.pi - Real.arctan (ε / r))
                (-Real.pi + Real.arctan (ε / r))
                (8 * (t : ℝ) - 1)) := by
        -- The inner arc has constant radius `ε`, so it cannot hit the outer corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      exact (hεr.ne hnorm.symm).elim
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- The open lower lip is the radial segment on the lower boundary ray.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hρ :
          0 <
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) := by
        -- The lower-lip radius stays in the closed interval `[ε, r]`, hence remains positive.
        have hparamI : 4 * (t : ℝ) - 1 ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_rfl, le_of_lt hεr⟩
            ⟨le_of_lt hεr, le_rfl⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hlower_im :
          (exercise21Delta r ε t).im < 0 := by
        -- Rewrite the lower lip as a fixed-angle circle point, then use the lower-ray sign.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_lower_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
        have hre :=
          exercise21Delta_lower_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The target corner lies on the upper lip, hence above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper outer corner lies above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower outer corner lies below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · let α : ℝ :=
        AffineMap.lineMap
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          (2 * (t : ℝ) - 1)
      have hpath : exercise21Delta r ε t = circleMap 0 r α := by
        -- The outer arc uses the admissible angular window `(-π + θ, π - θ)`.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [houter.1, houter.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        -- The branch parameter stays strictly inside the outer-arc angle window.
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.uIoc
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_le hAngleOrder.le]
        exact Set.Ioo_subset_Ioc_self hαmemIoo
      have hendmem :
          Real.pi - Real.arctan (ε / r) ∈
            Set.uIoc
              (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_le hAngleOrder.le]
        exact Set.mem_Ioc.mpr ⟨hAngleOrder, le_rfl⟩
      have hlen :
          |(-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r))| ≤
            2 * Real.pi := by
        have hnonpos :
            (-Real.pi + Real.arctan (ε / r)) - (Real.pi - Real.arctan (ε / r)) ≤ 0 := by
          nlinarith [hθlt, Real.pi_pos]
        rw [abs_of_nonpos hnonpos]
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := r)
          (a := -Real.pi + Real.arctan (ε / r))
          (b := Real.pi - Real.arctan (ε / r))
          (by linarith : r ≠ 0) hlen
      have hcircle : circleMap 0 r α = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        calc
          circleMap 0 r α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := ht
      have hαeq : α = Real.pi - Real.arctan (ε / r) := hinj hαmem hendmem hcircle
      exact False.elim ((ne_of_lt hαmemIoo.2) hαeq)
    · -- The terminal parameter is the second endpoint of the closed loop.
      exact Or.inr (Subtype.ext hone)
  · rintro (rfl | rfl)
    · exact (exercise21Delta_breakpoint_values r ε).1
    · exact (exercise21Delta_breakpoint_values r ε).2.2.2.2

/-- Helper for Exercise 21: the upper inner corner of the keyhole contour is hit exactly at the
first interior breakpoint `t = 1/8`. This is the second exact breakpoint fiber needed for the
later simple-loop proof. -/
lemma exercise21Delta_eq_upper_inner_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) ↔
      t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 r (Real.pi - Real.arctan (ε / r)) ≠
        circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- On the open upper lip, the contour is the open radial segment between the two corners.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        -- Interior upper-lip parameters cannot land on either endpoint of the segment.
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
            (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 ε (Real.pi - Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 r (Real.pi - Real.arctan (ε / r)))
          (y := circleMap 0 ε (Real.pi - Real.arctan (ε / r)))).mp hcorner
    · exact Subtype.ext honeEight
    · let α : ℝ :=
        AffineMap.lineMap
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          (8 * (t : ℝ) - 1)
      have hpath :
          exercise21Delta r ε t = circleMap 0 ε α := by
        -- On the inner arc, only the initial angle can hit the upper inner corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hinner.1, hinner.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r)) := by
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.uIoc
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_ge hAngleOrder.le]
        exact Set.Ioo_subset_Ioc_self hαmemIoo
      have htargetmem :
          Real.pi - Real.arctan (ε / r) ∈
            Set.uIoc
              (Real.pi - Real.arctan (ε / r))
              (-Real.pi + Real.arctan (ε / r)) := by
        rw [Set.uIoc_of_ge hAngleOrder.le]
        exact Set.mem_Ioc.mpr ⟨hAngleOrder, le_rfl⟩
      have hlen :
          |(Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r))| ≤
            2 * Real.pi := by
        have hnonneg :
            0 ≤ (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) := by
          nlinarith [hθlt, Real.pi_pos]
        rw [abs_of_nonneg hnonneg]
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le
          (c := 0) (R := ε)
          (a := Real.pi - Real.arctan (ε / r))
          (b := -Real.pi + Real.arctan (ε / r))
          (by linarith : ε ≠ 0) hlen
      have hcircle : circleMap 0 ε α = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        calc
          circleMap 0 ε α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := ht
      have hαeq : α = Real.pi - Real.arctan (ε / r) := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_lt hαmemIoo.2) hαeq)
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper inner corner lies above the real axis on the upper slit boundary.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower inner corner is on the opposite slit lip, hence below the axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- Lower-lip interior points stay strictly below the real axis.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hρ :
          0 <
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) := by
        have hparamI : 4 * (t : ℝ) - 1 ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap ε r (4 * (t : ℝ) - 1) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_rfl, le_of_lt hεr⟩
            ⟨le_of_lt hεr, le_rfl⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hlower_im :
          (exercise21Delta r ε t).im < 0 := by
        -- Convert the affine lower-lip point back to a fixed-angle circle point.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_lower_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
        have hre :=
          exercise21Delta_lower_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap ε r (4 * (t : ℝ) - 1))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The target corner lies on the upper slit boundary.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The target corner lies above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower outer corner still lies below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 r
              (AffineMap.lineMap
                (-Real.pi + Real.arctan (ε / r))
                (Real.pi - Real.arctan (ε / r))
                (2 * (t : ℝ) - 1)) := by
        -- The outer arc has radius `r`, so it cannot hit a corner on the inner circle.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (exercise21Delta_breakpoint_values r ε).2.1

/-- Helper for Exercise 21: the lower inner corner of the keyhole contour is hit exactly at the
second interior breakpoint `t = 1/4`. This closes the third exact breakpoint fiber needed for
the later simple-loop proof. -/
lemma exercise21Delta_eq_lower_inner_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ↔
      t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ≠
        circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- Upper-lip interior points stay above the real axis, unlike the lower inner corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hρ :
          0 <
            AffineMap.lineMap r ε (8 * (t : ℝ)) := by
        have hparamI : 8 * (t : ℝ) ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap r ε (8 * (t : ℝ)) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_of_lt hεr, le_rfl⟩
            ⟨le_rfl, le_of_lt hεr⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hupper_im :
          0 < (exercise21Delta r ε t).im := by
        -- Convert the affine upper-lip point back to a fixed-angle circle point.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_upper_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
        have hre :=
          exercise21Delta_upper_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner lies on the lower slit boundary.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper inner corner is above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 ε (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner is below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · let α : ℝ :=
        AffineMap.lineMap
          (Real.pi - Real.arctan (ε / r))
          (-Real.pi + Real.arctan (ε / r))
          (8 * (t : ℝ) - 1)
      have hpath :
          exercise21Delta r ε t = circleMap 0 ε α := by
        -- The inner arc reaches the lower inner corner only at its terminal parameter.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hparam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hinner.1, hinner.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          Real.pi - Real.arctan (ε / r) ≠ -Real.pi + Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r)) := by
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (Real.pi - Real.arctan (ε / r))
            (-Real.pi + Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.Ico
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        exact Set.Ioo_subset_Ico_self hαmemIoo
      have htargetmem :
          -Real.pi + Real.arctan (ε / r) ∈
            Set.Ico
              (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r)) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, hAngleOrder⟩
      have hlen :
          (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) ≤
            2 * Real.pi := by
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := ε)
          (a := -Real.pi + Real.arctan (ε / r))
          (b := Real.pi - Real.arctan (ε / r))
          (by linarith : ε ≠ 0) hlen
      have hcircle : circleMap 0 ε α = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        calc
          circleMap 0 ε α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := ht
      have hαeq : α = -Real.pi + Real.arctan (ε / r) := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_gt hαmemIoo.1) hαeq)
    · exact Subtype.ext honeQuarter
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- On the open lower lip, the target is the excluded left endpoint.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (left_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (y := circleMap 0 r (-Real.pi + Real.arctan (ε / r)))).mp hcorner
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hhalf
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 r
              (AffineMap.lineMap
                (-Real.pi + Real.arctan (ε / r))
                (Real.pi - Real.arctan (ε / r))
                (2 * (t : ℝ) - 1)) := by
        -- The outer arc has radius `r`, so it cannot hit the inner lower corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.2
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
  · rintro rfl
    exact (exercise21Delta_breakpoint_values r ε).2.2.1

/-- Helper for Exercise 21: the lower outer corner of the keyhole contour is hit exactly at the
third interior breakpoint `t = 1/2`. This is the last exact breakpoint fiber needed before the
simple-loop dispatcher can close. -/
lemma exercise21Delta_eq_lower_outer_corner_iff
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t : I} :
    exercise21Delta r ε t = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) ↔
      t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := by
  have hr : 0 < r := lt_trans hε hεr
  have hθpos : 0 < Real.arctan (ε / r) := Real.arctan_pos.mpr (div_pos hε hr)
  have hθlt : Real.arctan (ε / r) < Real.pi / 2 := Real.arctan_lt_pi_div_two (ε / r)
  have hEndsNe :
      circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) ≠
        circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
    intro hEq
    have hnorm := congrArg norm hEq
    simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
    linarith
  constructor
  · intro ht
    rcases exercise21Delta_parameter_cases t with
      hzero | hupper | honeEight | hinner | honeQuarter | hlower | hhalf | houter | hone
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The initial upper outer corner lies above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner is below the real axis on the lower slit boundary.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (0 : I) := Subtype.ext hzero
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hparam : 8 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hupper.1, hupper.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 r (Real.pi - Real.arctan (ε / r)))
              (circleMap 0 ε (Real.pi - Real.arctan (ε / r)))
              (8 * (t : ℝ)) := by
        -- Upper-lip interior points stay above the real axis, unlike the target corner.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_upper_lip r ε (Set.Ioo_subset_Icc_self hupper)
      have hρ :
          0 <
            AffineMap.lineMap r ε (8 * (t : ℝ)) := by
        have hparamI : 8 * (t : ℝ) ∈ I := ⟨le_of_lt hparam.1, le_of_lt hparam.2⟩
        have hρmem :
            AffineMap.lineMap r ε (8 * (t : ℝ)) ∈ Set.Icc ε r := by
          exact (convex_Icc ε r).lineMap_mem
            ⟨le_of_lt hεr, le_rfl⟩
            ⟨le_rfl, le_of_lt hεr⟩
            hparamI
        exact lt_of_lt_of_le hε hρmem.1
      have hupper_im :
          0 < (exercise21Delta r ε t).im := by
        -- Convert the affine upper-lip point to a fixed-angle circle point.
        rw [hpath, exercise21_lineMap_circleMap_same_angle]
        have hline :=
          exercise21Delta_upper_lip_line
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
        have hre :=
          exercise21Delta_upper_lip_re_neg
            (r := r) (ε := ε)
            (ρ := AffineMap.lineMap r ε (8 * (t : ℝ)))
            hρ
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The lower outer corner lies below the axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have him := congrArg Complex.im ht
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 ε (Real.pi - Real.arctan (ε / r))).im := by
        -- The upper inner corner is still above the real axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := ε)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner is below the real axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext honeEight
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.1
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
    · have hpath :
          exercise21Delta r ε t =
            circleMap 0 ε
              (AffineMap.lineMap
                (Real.pi - Real.arctan (ε / r))
                (-Real.pi + Real.arctan (ε / r))
                (8 * (t : ℝ) - 1)) := by
        -- The inner arc has radius `ε`, so it cannot hit a corner on the outer circle.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_inner_arc r ε (Set.Ioo_subset_Icc_self hinner)
      have hnorm := congrArg norm (ht.symm.trans hpath)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext honeQuarter
      have hcorner :
          exercise21Delta r ε t = circleMap 0 ε (-Real.pi + Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.1
      have hnorm := congrArg norm (ht.symm.trans hcorner)
      simp [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] at hnorm
      linarith
    · have hparam : 4 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hlower.1, hlower.2]
      have hpath :
          exercise21Delta r ε t =
            AffineMap.lineMap
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
              (4 * (t : ℝ) - 1) := by
        -- On the open lower lip, the target is the excluded right endpoint.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_lower_lip r ε (Set.Ioo_subset_Icc_self hlower)
      have hopen :
          exercise21Delta r ε t ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [hpath] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
            (circleMap 0 r (-Real.pi + Real.arctan (ε / r)))
            hparam)
      have hcorner :
          circleMap 0 r (-Real.pi + Real.arctan (ε / r)) ∈
            openSegment ℝ
              (circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
              (circleMap 0 r (-Real.pi + Real.arctan (ε / r))) := by
        simpa [ht] using hopen
      exact False.elim <| hEndsNe <|
        (right_mem_openSegment_iff
          (𝕜 := ℝ)
          (x := circleMap 0 ε (-Real.pi + Real.arctan (ε / r)))
          (y := circleMap 0 r (-Real.pi + Real.arctan (ε / r)))).mp hcorner
    · exact Subtype.ext hhalf
    · let α : ℝ :=
        AffineMap.lineMap
          (-Real.pi + Real.arctan (ε / r))
          (Real.pi - Real.arctan (ε / r))
          (2 * (t : ℝ) - 1)
      have hpath :
          exercise21Delta r ε t = circleMap 0 r α := by
        -- The outer arc hits the lower outer corner only at its initial angle.
        exact (Path.extend_apply (exercise21Delta r ε) t.2).symm.trans <|
          exercise21Delta_eq_on_outer_arc r ε (Set.Ioo_subset_Icc_self houter)
      have hparam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [houter.1, houter.2]
      have hAngleOrder :
          -Real.pi + Real.arctan (ε / r) < Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hAnglesNe :
          -Real.pi + Real.arctan (ε / r) ≠ Real.pi - Real.arctan (ε / r) := by
        nlinarith [hθlt, Real.pi_pos]
      have hαmemOpen :
          α ∈ openSegment ℝ
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        simpa [α] using
          (lineMap_mem_openSegment (𝕜 := ℝ)
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r))
            hparam)
      have hαmemIoo :
          α ∈ Set.Ioo
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
        simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
      have hαmem :
          α ∈ Set.Ico
            (-Real.pi + Real.arctan (ε / r))
            (Real.pi - Real.arctan (ε / r)) := by
        exact Set.Ioo_subset_Ico_self hαmemIoo
      have htargetmem :
          -Real.pi + Real.arctan (ε / r) ∈
            Set.Ico
              (-Real.pi + Real.arctan (ε / r))
              (Real.pi - Real.arctan (ε / r)) := by
        exact Set.mem_Ico.mpr ⟨le_rfl, hAngleOrder⟩
      have hlen :
          (Real.pi - Real.arctan (ε / r)) - (-Real.pi + Real.arctan (ε / r)) ≤
            2 * Real.pi := by
        nlinarith [hθpos, Real.pi_pos]
      have hinj :=
        injOn_circleMap_of_abs_sub_le'
          (c := 0) (R := r)
          (a := -Real.pi + Real.arctan (ε / r))
          (b := Real.pi - Real.arctan (ε / r))
          (by linarith : r ≠ 0) hlen
      have hcircle : circleMap 0 r α = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := by
        calc
          circleMap 0 r α = exercise21Delta r ε t := hpath.symm
          _ = circleMap 0 r (-Real.pi + Real.arctan (ε / r)) := ht
      have hαeq : α = -Real.pi + Real.arctan (ε / r) := hinj hαmem htargetmem hcircle
      exact False.elim ((ne_of_gt hαmemIoo.1) hαeq)
    · have hbreak := exercise21Delta_breakpoint_values r ε
      have hupper_im :
          0 < (circleMap 0 r (Real.pi - Real.arctan (ε / r))).im := by
        -- The terminal upper outer corner lies above the axis.
        have hline := exercise21Delta_upper_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have hlower_im :
          (circleMap 0 r (-Real.pi + Real.arctan (ε / r))).im < 0 := by
        -- The target corner remains below the axis.
        have hline := exercise21Delta_lower_lip_line (r := r) (ε := ε) (ρ := r)
        have hre := exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr
        have hratio : 0 < ε / r := div_pos hε hr
        rw [hline]
        nlinarith
      have htEq : t = (1 : I) := Subtype.ext hone
      have hcorner :
          exercise21Delta r ε t = circleMap 0 r (Real.pi - Real.arctan (ε / r)) := by
        simpa [htEq] using hbreak.2.2.2.2
      have him := congrArg Complex.im (ht.symm.trans hcorner)
      linarith
  · rintro rfl
    exact (exercise21Delta_breakpoint_values r ε).2.2.2.1

