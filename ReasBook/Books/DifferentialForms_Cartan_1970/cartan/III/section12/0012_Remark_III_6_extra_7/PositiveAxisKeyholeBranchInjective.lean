import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeRange

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: equality on one open branch of the positive-axis keyhole
forces equality of the corresponding parameters. This isolates the branchwise injectivity package
needed later by the simple-loop proof from the breakpoint bookkeeping. -/
lemma positiveAxisKeyhole_same_branch_injective
    (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) {s t : I}
    (hbranch :
      (s.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∧ t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8)) ∨
        (s.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∧ t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4)) ∨
        (s.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∧ t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) ∨
        (s.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) ∧ t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ)))
    (hst : positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t) :
    s = t := by
  have hR : 0 < R := lt_trans hε hεR
  have hθ := positiveAxisKeyhole_angle_bounds (R := R) (ε := ε) hε hεR
  rcases hbranch with hupper | hinner | hlower | houter
  · rcases hupper with ⟨hs, ht⟩
    -- On the upper lip, the keyhole is a nonconstant affine interpolation in the radius.
    have hsPath :
        positiveAxisKeyhole R ε s =
          AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (s : ℝ)) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        positiveAxisKeyhole R ε t =
          AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (t : ℝ)) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_upper_lip R ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (s : ℝ)) =
          AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (t : ℝ)) := by
      calc
        AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * (s : ℝ)) =
            positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * (t : ℝ)) := htPath
    have hEndsNe :
        circleMap 0 R (positiveAxisKeyholeAngle R ε) ≠
          circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    have hst' : 8 * (s : ℝ) = 8 * (t : ℝ) := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 R (positiveAxisKeyholeAngle R ε))
        (p₁ := circleMap 0 ε (positiveAxisKeyholeAngle R ε))
        (c₁ := 8 * (s : ℝ)) (c₂ := 8 * (t : ℝ))).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Recover the subtype equality from the affine radial parameter.
    exact Subtype.ext (by linarith)
  · rcases hinner with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (positiveAxisKeyholeUpperAngle R ε)
        (positiveAxisKeyholeLowerAngle R ε)
        (8 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (positiveAxisKeyholeUpperAngle R ε)
        (positiveAxisKeyholeLowerAngle R ε)
        (8 * (t : ℝ) - 1)
    -- On the inner circle, injectivity comes from the angular window of length `< 2π`.
    have hsPath : positiveAxisKeyhole R ε s = circleMap 0 ε α := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_inner_arc R ε (Set.Ioo_subset_Icc_self hs)
    have htPath : positiveAxisKeyhole R ε t = circleMap 0 ε β := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_inner_arc R ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 ε α = circleMap 0 ε β := by
      calc
        circleMap 0 ε α = positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ = circleMap 0 ε β := htPath
    have hsParam : 8 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 8 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
    have hAngleOrder :
        positiveAxisKeyholeUpperAngle R ε < positiveAxisKeyholeLowerAngle R ε := horder.1
    have hAnglesNe :
        positiveAxisKeyholeUpperAngle R ε ≠ positiveAxisKeyholeLowerAngle R ε :=
      ne_of_lt horder.1
    have hαmemOpen :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε)
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε)
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_left hAngleOrder.le, max_eq_right hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      rw [Set.uIoc_of_le hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |positiveAxisKeyholeUpperAngle R ε - positiveAxisKeyholeLowerAngle R ε| ≤ 2 * Real.pi := by
      have hnonpos :
          positiveAxisKeyholeUpperAngle R ε - positiveAxisKeyholeLowerAngle R ε ≤ 0 := by
        linarith
      rw [abs_of_nonpos hnonpos]
      nlinarith [horder.2, hθ.1, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := ε)
        (a := positiveAxisKeyholeUpperAngle R ε)
        (b := positiveAxisKeyholeLowerAngle R ε)
        (by linarith : ε ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)
            (8 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)
            (8 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 8 * (s : ℝ) - 1 = 8 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := positiveAxisKeyholeUpperAngle R ε)
        (p₁ := positiveAxisKeyholeLowerAngle R ε)
        (c₁ := 8 * (s : ℝ) - 1) (c₂ := 8 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          exact hAnglesNe hEq
        exact this.elim
      · exact hEq
    -- The affine angle parameter is injective because the two angular endpoints differ.
    exact Subtype.ext (by linarith)
  · rcases hlower with ⟨hs, ht⟩
    -- The lower lip is the same affine radial model, with the opposite orientation.
    have hsPath :
        positiveAxisKeyhole R ε s =
          AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (s : ℝ) - 1) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self hs)
    have htPath :
        positiveAxisKeyhole R ε t =
          AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (t : ℝ) - 1) := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_lower_lip R ε (Set.Ioo_subset_Icc_self ht)
    have hparam :
        AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (t : ℝ) - 1) := by
      calc
        AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * (s : ℝ) - 1) =
            positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ =
            AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * (t : ℝ) - 1) := htPath
    have hEndsNe :
        circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ≠
          circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
      intro hEq
      have hnorm := congrArg norm hEq
      simp [norm_circleMap_zero, abs_of_pos hR, abs_of_pos hε] at hnorm
      linarith
    have hst' : 4 * (s : ℝ) - 1 = 4 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
        (p₁ := circleMap 0 R (-positiveAxisKeyholeAngle R ε))
        (c₁ := 4 * (s : ℝ) - 1) (c₂ := 4 * (t : ℝ) - 1)).mp hparam with hEq | hEq
      · exact (hEndsNe hEq).elim
      · exact hEq
    -- Again the subtype equality is read off from the affine radial coordinate.
    exact Subtype.ext (by linarith)
  · rcases houter with ⟨hs, ht⟩
    let α : ℝ :=
      AffineMap.lineMap
        (positiveAxisKeyholeLowerAngle R ε)
        (positiveAxisKeyholeUpperAngle R ε)
        (2 * (s : ℝ) - 1)
    let β : ℝ :=
      AffineMap.lineMap
        (positiveAxisKeyholeLowerAngle R ε)
        (positiveAxisKeyholeUpperAngle R ε)
        (2 * (t : ℝ) - 1)
    -- The outer circle uses the same injective angular strip as the inner arc.
    have hsPath : positiveAxisKeyhole R ε s = circleMap 0 R α := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) s.2).symm.trans <|
        positive_axis_keyhole_eq_on_outer_arc R ε (Set.Ioo_subset_Icc_self hs)
    have htPath : positiveAxisKeyhole R ε t = circleMap 0 R β := by
      exact (Path.extend_apply (positiveAxisKeyhole R ε) t.2).symm.trans <|
        positive_axis_keyhole_eq_on_outer_arc R ε (Set.Ioo_subset_Icc_self ht)
    have hcircle : circleMap 0 R α = circleMap 0 R β := by
      calc
        circleMap 0 R α = positiveAxisKeyhole R ε s := hsPath.symm
        _ = positiveAxisKeyhole R ε t := hst
        _ = circleMap 0 R β := htPath
    have hsParam : 2 * (s : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have htParam : 2 * (t : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
    have hAngleOrder :
        positiveAxisKeyholeUpperAngle R ε < positiveAxisKeyholeLowerAngle R ε := horder.1
    have hAnglesNe :
        positiveAxisKeyholeLowerAngle R ε ≠ positiveAxisKeyholeUpperAngle R ε :=
      (ne_of_lt horder.1).symm
    have hαmemOpen :
        α ∈ openSegment ℝ
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε) := by
      simpa [α] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε)
          hsParam
    have hβmemOpen :
        β ∈ openSegment ℝ
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε) := by
      simpa [β] using
        lineMap_mem_openSegment (𝕜 := ℝ)
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε)
          htParam
    have hαmemIoo :
        α ∈ Set.Ioo
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hαmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hαmemOpen
    have hβmemIoo :
        β ∈ Set.Ioo
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε) := by
      rw [openSegment_eq_Ioo' (𝕜 := ℝ) hAnglesNe] at hβmemOpen
      simpa [min_eq_right hAngleOrder.le, max_eq_left hAngleOrder.le] using hβmemOpen
    have hαmem :
        α ∈ Set.uIoc
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hαmemIoo
    have hβmem :
        β ∈ Set.uIoc
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε) := by
      rw [Set.uIoc_of_ge hAngleOrder.le]
      exact Set.Ioo_subset_Ioc_self hβmemIoo
    have hlen :
        |positiveAxisKeyholeLowerAngle R ε - positiveAxisKeyholeUpperAngle R ε| ≤ 2 * Real.pi := by
      have hnonneg :
          0 ≤ positiveAxisKeyholeLowerAngle R ε - positiveAxisKeyholeUpperAngle R ε := by
        linarith
      rw [abs_of_nonneg hnonneg]
      nlinarith [horder.2, hθ.1, Real.pi_pos]
    have hinj :=
      injOn_circleMap_of_abs_sub_le
        (c := 0) (R := R)
        (a := positiveAxisKeyholeLowerAngle R ε)
        (b := positiveAxisKeyholeUpperAngle R ε)
        (by linarith : R ≠ 0) hlen
    have hαβ : α = β := hinj hαmem hβmem hcircle
    have hαβ_explicit :
        AffineMap.lineMap
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)
            (2 * (s : ℝ) - 1) =
          AffineMap.lineMap
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)
            (2 * (t : ℝ) - 1) := by
      simpa [α, β] using hαβ
    have hst' : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff
        (p₀ := positiveAxisKeyholeLowerAngle R ε)
        (p₁ := positiveAxisKeyholeUpperAngle R ε)
        (c₁ := 2 * (s : ℝ) - 1) (c₂ := 2 * (t : ℝ) - 1)).mp hαβ_explicit with hEq | hEq
      · have : False := by
          exact hAnglesNe hEq
        exact this.elim
      · exact hEq
    -- The outer-arc affine angle parameter is likewise injective.
    exact Subtype.ext (by linarith)
