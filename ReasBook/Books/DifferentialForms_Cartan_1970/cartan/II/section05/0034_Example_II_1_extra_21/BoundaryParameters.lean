import DifferentialForms_Cartan_1970.II.section05.«0034_Example_II_1_extra_21».BoundaryGeometry

open scoped unitInterval

noncomputable section

/-- Helper for Example II.1-extra-21: on the open bottom-side parameter interval, the boundary
path has constant imaginary part `z.im` and strictly increasing real part between `z.re` and
`w.re`. -/
lemma axis_parallel_rectangle_boundary_path_bottom_coordinates
    (z w : ℂ) (hRe : z.re < w.re) {t : I} (ht : t.1 ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    (axisParallelRectangleBoundaryPath z w t).im = z.im ∧
      (axisParallelRectangleBoundaryPath z w t).re ∈ Set.Ioo z.re w.re := by
  -- Rewrite the path by the explicit affine parametrization of the bottom edge.
  have hside :
      (axisParallelRectangleBoundaryPath z w).extend (t : ℝ) =
        AffineMap.lineMap z (Complex.mk w.re z.im) (2 * (t : ℝ)) :=
    axisParallelRectangleBoundaryPath_eqOn_bottom_side z w (Set.Ioo_subset_Icc_self ht)
  have hpath :
      axisParallelRectangleBoundaryPath z w t =
        AffineMap.lineMap z (Complex.mk w.re z.im) (2 * (t : ℝ)) := by
    simpa using hside
  have hre :
      (axisParallelRectangleBoundaryPath z w t).re =
        AffineMap.lineMap z.re w.re (2 * (t : ℝ)) := by
    simpa [AffineMap.lineMap_apply] using congrArg Complex.re hpath
  constructor
  · simpa [AffineMap.lineMap_apply] using congrArg Complex.im hpath
  · have ht' : 2 * (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hmem : AffineMap.lineMap z.re w.re (2 * (t : ℝ)) ∈ Set.Ioo z.re w.re := by
      simpa [openSegment_eq_Ioo hRe] using
        (lineMap_mem_openSegment ℝ z.re w.re ht')
    exact hre.symm ▸ hmem

/-- Helper for Example II.1-extra-21: on the open right-side parameter interval, the boundary
path has constant real part `w.re` and strictly increasing imaginary part between `z.im` and
`w.im`. -/
lemma axis_parallel_rectangle_boundary_path_right_coordinates
    (z w : ℂ) (hIm : z.im < w.im) {t : I} (ht : t.1 ∈ Set.Ioo (1 / 2) (3 / 4)) :
    (axisParallelRectangleBoundaryPath z w t).re = w.re ∧
      (axisParallelRectangleBoundaryPath z w t).im ∈ Set.Ioo z.im w.im := by
  -- Rewrite the path by the explicit affine parametrization of the right edge.
  have hside :
      (axisParallelRectangleBoundaryPath z w).extend (t : ℝ) =
        AffineMap.lineMap (Complex.mk w.re z.im) w (4 * (t : ℝ) - 2) :=
    axisParallelRectangleBoundaryPath_eqOn_right_side z w (Set.Ioo_subset_Icc_self ht)
  have hpath :
      axisParallelRectangleBoundaryPath z w t =
        AffineMap.lineMap (Complex.mk w.re z.im) w (4 * (t : ℝ) - 2) := by
    simpa using hside
  have him :
      (axisParallelRectangleBoundaryPath z w t).im =
        AffineMap.lineMap z.im w.im (4 * (t : ℝ) - 2) := by
    simpa [AffineMap.lineMap_apply] using congrArg Complex.im hpath
  constructor
  · simpa [AffineMap.lineMap_apply] using congrArg Complex.re hpath
  · have ht' : 4 * (t : ℝ) - 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hmem : AffineMap.lineMap z.im w.im (4 * (t : ℝ) - 2) ∈ Set.Ioo z.im w.im := by
      simpa [openSegment_eq_Ioo hIm] using
        (lineMap_mem_openSegment ℝ z.im w.im ht')
    exact him.symm ▸ hmem

/-- Helper for Example II.1-extra-21: on the open top-side parameter interval, the boundary path
has constant imaginary part `w.im` and real part strictly between `z.re` and `w.re`. -/
lemma axis_parallel_rectangle_boundary_path_top_coordinates
    (z w : ℂ) (hRe : z.re < w.re) {t : I} (ht : t.1 ∈ Set.Ioo (3 / 4) (7 / 8)) :
    (axisParallelRectangleBoundaryPath z w t).im = w.im ∧
      (axisParallelRectangleBoundaryPath z w t).re ∈ Set.Ioo z.re w.re := by
  -- Rewrite the path by the explicit affine parametrization of the top edge.
  have hside :
      (axisParallelRectangleBoundaryPath z w).extend (t : ℝ) =
        AffineMap.lineMap w (Complex.mk z.re w.im) (8 * (t : ℝ) - 6) :=
    axisParallelRectangleBoundaryPath_eqOn_top_side z w (Set.Ioo_subset_Icc_self ht)
  have hpath :
      axisParallelRectangleBoundaryPath z w t =
        AffineMap.lineMap w (Complex.mk z.re w.im) (8 * (t : ℝ) - 6) := by
    simpa using hside
  have hre :
      (axisParallelRectangleBoundaryPath z w t).re =
        AffineMap.lineMap w.re z.re (8 * (t : ℝ) - 6) := by
    simpa [AffineMap.lineMap_apply] using congrArg Complex.re hpath
  constructor
  · simpa [AffineMap.lineMap_apply] using congrArg Complex.im hpath
  · have ht' : 8 * (t : ℝ) - 6 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hmem : AffineMap.lineMap w.re z.re (8 * (t : ℝ) - 6) ∈ Set.Ioo z.re w.re := by
      simpa [openSegment_eq_Ioo hRe, openSegment_symm ℝ w.re z.re] using
        (lineMap_mem_openSegment ℝ w.re z.re ht')
    exact hre.symm ▸ hmem

/-- Helper for Example II.1-extra-21: on the open left-side parameter interval, the boundary path
has constant real part `z.re` and imaginary part strictly between `z.im` and `w.im`. -/
lemma axis_parallel_rectangle_boundary_path_left_coordinates
    (z w : ℂ) (hIm : z.im < w.im) {t : I} (ht : t.1 ∈ Set.Ioo (7 / 8) (1 : ℝ)) :
    (axisParallelRectangleBoundaryPath z w t).re = z.re ∧
      (axisParallelRectangleBoundaryPath z w t).im ∈ Set.Ioo z.im w.im := by
  -- Rewrite the path by the explicit affine parametrization of the left edge.
  have hside :
      (axisParallelRectangleBoundaryPath z w).extend (t : ℝ) =
        AffineMap.lineMap (Complex.mk z.re w.im) z (8 * (t : ℝ) - 7) :=
    axisParallelRectangleBoundaryPath_eqOn_left_side z w (Set.Ioo_subset_Icc_self ht)
  have hpath :
      axisParallelRectangleBoundaryPath z w t =
        AffineMap.lineMap (Complex.mk z.re w.im) z (8 * (t : ℝ) - 7) := by
    simpa using hside
  have him :
      (axisParallelRectangleBoundaryPath z w t).im =
        AffineMap.lineMap w.im z.im (8 * (t : ℝ) - 7) := by
    simpa [AffineMap.lineMap_apply] using congrArg Complex.im hpath
  constructor
  · simpa [AffineMap.lineMap_apply] using congrArg Complex.re hpath
  · have ht' : 8 * (t : ℝ) - 7 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hmem : AffineMap.lineMap w.im z.im (8 * (t : ℝ) - 7) ∈ Set.Ioo z.im w.im := by
      simpa [openSegment_eq_Ioo hIm, openSegment_symm ℝ w.im z.im] using
        (lineMap_mem_openSegment ℝ w.im z.im ht')
    exact him.symm ▸ hmem

/-- Helper for Example II.1-extra-21: the breakpoint `1/2` lies in the unit interval. -/
lemma half_mem_unitInterval : (1 / 2 : ℝ) ∈ (Set.Icc (0 : ℝ) 1) := by
  constructor <;> norm_num

/-- Helper for Example II.1-extra-21: the breakpoint `3/4` lies in the unit interval. -/
lemma three_quarters_mem_unitInterval : (3 / 4 : ℝ) ∈ (Set.Icc (0 : ℝ) 1) := by
  constructor <;> norm_num

/-- Helper for Example II.1-extra-21: the breakpoint `7/8` lies in the unit interval. -/
lemma seven_eighths_mem_unitInterval : (7 / 8 : ℝ) ∈ (Set.Icc (0 : ℝ) 1) := by
  constructor <;> norm_num

/-- Helper for Example II.1-extra-21: the rectangle boundary path starts at the lower-left
corner. -/
lemma axis_parallel_rectangle_boundary_path_zero (z w : ℂ) :
    axisParallelRectangleBoundaryPath z w (0 : I) = z := by
  -- The first path segment starts at the lower-left corner.
  simp [axisParallelRectangleBoundaryPath]

/-- Helper for Example II.1-extra-21: the first breakpoint is the lower-right corner. -/
lemma axis_parallel_rectangle_boundary_path_half (z w : ℂ) :
    axisParallelRectangleBoundaryPath z w
      (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) = Complex.mk w.re z.im := by
  -- Evaluate the bottom-side affine formula at its endpoint.
  have ht : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    constructor <;> norm_num
  have happly :
      (axisParallelRectangleBoundaryPath z w).extend (1 / 2 : ℝ) =
        axisParallelRectangleBoundaryPath z w
          (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := by
    simpa using
      (Path.extend_apply (axisParallelRectangleBoundaryPath z w) half_mem_unitInterval)
  calc
    axisParallelRectangleBoundaryPath z w (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) =
        (axisParallelRectangleBoundaryPath z w).extend (1 / 2 : ℝ) := by
      simpa using happly.symm
    _ =
        AffineMap.lineMap z (Complex.mk w.re z.im) (2 * (1 / 2 : ℝ)) :=
      axisParallelRectangleBoundaryPath_eqOn_bottom_side z w ht
    _ = AffineMap.lineMap z (Complex.mk w.re z.im) (1 : ℝ) := by
      congr 1
      ring
    _ = Complex.mk w.re z.im := by simp

/-- Helper for Example II.1-extra-21: the second breakpoint is the upper-right corner. -/
lemma axis_parallel_rectangle_boundary_path_three_quarters (z w : ℂ) :
    axisParallelRectangleBoundaryPath z w
      (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) = w := by
  -- Evaluate the right-side affine formula at its endpoint.
  have ht : (3 / 4 : ℝ) ∈ Set.Icc (1 / 2) (3 / 4) := by
    constructor <;> norm_num
  have happly :
      (axisParallelRectangleBoundaryPath z w).extend (3 / 4 : ℝ) =
        axisParallelRectangleBoundaryPath z w
          (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := by
    simpa using
      (Path.extend_apply (axisParallelRectangleBoundaryPath z w) three_quarters_mem_unitInterval)
  calc
    axisParallelRectangleBoundaryPath z w
        (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) =
        (axisParallelRectangleBoundaryPath z w).extend (3 / 4 : ℝ) := by
      simpa using happly.symm
    _ =
        AffineMap.lineMap (Complex.mk w.re z.im) w (4 * (3 / 4 : ℝ) - 2) :=
      axisParallelRectangleBoundaryPath_eqOn_right_side z w ht
    _ = AffineMap.lineMap (Complex.mk w.re z.im) w (1 : ℝ) := by
      congr 1
      ring
    _ = w := by simp

/-- Helper for Example II.1-extra-21: the third breakpoint is the upper-left corner. -/
lemma axis_parallel_rectangle_boundary_path_seven_eighths (z w : ℂ) :
    axisParallelRectangleBoundaryPath z w
      (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) = Complex.mk z.re w.im := by
  -- Evaluate the top-side affine formula at its endpoint.
  have ht : (7 / 8 : ℝ) ∈ Set.Icc (3 / 4) (7 / 8) := by
    constructor <;> norm_num
  have happly :
      (axisParallelRectangleBoundaryPath z w).extend (7 / 8 : ℝ) =
        axisParallelRectangleBoundaryPath z w
          (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := by
    simpa using
      (Path.extend_apply (axisParallelRectangleBoundaryPath z w) seven_eighths_mem_unitInterval)
  calc
    axisParallelRectangleBoundaryPath z w
        (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) =
        (axisParallelRectangleBoundaryPath z w).extend (7 / 8 : ℝ) := by
      simpa using happly.symm
    _ =
        AffineMap.lineMap w (Complex.mk z.re w.im) (8 * (7 / 8 : ℝ) - 6) :=
      axisParallelRectangleBoundaryPath_eqOn_top_side z w ht
    _ = AffineMap.lineMap w (Complex.mk z.re w.im) (1 : ℝ) := by
      congr 1
      ring
    _ = Complex.mk z.re w.im := by simp

/-- Helper for Example II.1-extra-21: the path closes up at the lower-left corner when
`t = 1`. -/
lemma axis_parallel_rectangle_boundary_path_one (z w : ℂ) :
    axisParallelRectangleBoundaryPath z w (1 : I) = z := by
  -- Evaluate the left-side affine formula at its endpoint.
  have ht : (1 : ℝ) ∈ Set.Icc (7 / 8) (1 : ℝ) := by
    constructor <;> norm_num
  have hside :
      axisParallelRectangleBoundaryPath z w (1 : I) =
        AffineMap.lineMap (Complex.mk z.re w.im) z (1 : ℝ) := by
    simpa using axisParallelRectangleBoundaryPath_eqOn_left_side z w ht
  simpa using hside

/-- Helper for Example II.1-extra-21: every parameter in `I` lies on exactly one open side
interval or is one of the five distinguished corner parameters `0`, `1/2`, `3/4`, `7/8`, `1`. -/
lemma axis_parallel_rectangle_boundary_parameter_cases (t : I) :
    t.1 = 0 ∨
      t.1 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨
      t.1 = 1 / 2 ∨
      t.1 ∈ Set.Ioo (1 / 2) (3 / 4) ∨
      t.1 = 3 / 4 ∨
      t.1 ∈ Set.Ioo (3 / 4) (7 / 8) ∨
      t.1 = 7 / 8 ∨
      t.1 ∈ Set.Ioo (7 / 8) (1 : ℝ) ∨
      t.1 = 1 := by
  -- Split first into the global endpoints `0`, `1`, or the open interval `(0, 1)`.
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.2 with ht0 | ht1 | ht
  · exact Or.inl ht0
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ht1
  · by_cases hhalf : t.1 < 1 / 2
    · exact Or.inr <| Or.inl ⟨ht.1, hhalf⟩
    · have hhalf' : 1 / 2 ≤ t.1 := le_of_not_gt hhalf
      by_cases h34 : t.1 < 3 / 4
      · rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨hhalf', le_of_lt h34⟩ with hEq | hEq | hmem
        · exact Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
      · have h34' : 3 / 4 ≤ t.1 := le_of_not_gt h34
        by_cases h78 : t.1 < 7 / 8
        · rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h34', le_of_lt h78⟩ with hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
        · have h78' : 7 / 8 ≤ t.1 := le_of_not_gt h78
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h78', ht.2.le⟩ with hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem

/-- Helper for Example II.1-extra-21: equality of two points on the rectangle boundary path
lying on the same open side forces equality of the parameters. -/
lemma axis_parallel_rectangle_boundary_path_same_side_injective
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {s t : I}
    (hside :
      (s.1 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧ t.1 ∈ Set.Ioo (0 : ℝ) (1 / 2)) ∨
        (s.1 ∈ Set.Ioo (1 / 2) (3 / 4) ∧ t.1 ∈ Set.Ioo (1 / 2) (3 / 4)) ∨
        (s.1 ∈ Set.Ioo (3 / 4) (7 / 8) ∧ t.1 ∈ Set.Ioo (3 / 4) (7 / 8)) ∨
        (s.1 ∈ Set.Ioo (7 / 8) (1 : ℝ) ∧ t.1 ∈ Set.Ioo (7 / 8) (1 : ℝ)))
    (hst : axisParallelRectangleBoundaryPath z w s = axisParallelRectangleBoundaryPath z w t) :
    s = t := by
  rcases hside with hbottom | hright | htop | hleft
  · rcases hbottom with ⟨hs, ht⟩
    -- On the bottom edge, the real coordinate is a nonconstant affine parameter.
    have hsre :
        (axisParallelRectangleBoundaryPath z w s).re =
          AffineMap.lineMap z.re w.re (2 * (s : ℝ)) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w s =
            AffineMap.lineMap z (Complex.mk w.re z.im) (2 * (s : ℝ)) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_bottom_side z w
          (Set.Ioo_subset_Icc_self hs)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.re hside'
    have htre :
        (axisParallelRectangleBoundaryPath z w t).re =
          AffineMap.lineMap z.re w.re (2 * (t : ℝ)) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w t =
            AffineMap.lineMap z (Complex.mk w.re z.im) (2 * (t : ℝ)) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_bottom_side z w
          (Set.Ioo_subset_Icc_self ht)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.re hside'
    have hparam :
        AffineMap.lineMap z.re w.re (2 * (s : ℝ)) =
          AffineMap.lineMap z.re w.re (2 * (t : ℝ)) := by
      simpa [hsre, htre] using congrArg Complex.re hst
    have hst' : 2 * (s : ℝ) = 2 * (t : ℝ) := by
      rcases (AffineMap.lineMap_eq_lineMap_iff (p₀ := z.re) (p₁ := w.re)
        (c₁ := 2 * (s : ℝ)) (c₂ := 2 * (t : ℝ))).mp hparam with hEq | hEq
      · exact (hRe.ne hEq).elim
      · exact hEq
    apply Subtype.ext
    linarith
  · rcases hright with ⟨hs, ht⟩
    -- On the right edge, the imaginary coordinate is a nonconstant affine parameter.
    have hsim :
        (axisParallelRectangleBoundaryPath z w s).im =
          AffineMap.lineMap z.im w.im (4 * (s : ℝ) - 2) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w s =
            AffineMap.lineMap (Complex.mk w.re z.im) w (4 * (s : ℝ) - 2) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_right_side z w
          (Set.Ioo_subset_Icc_self hs)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.im hside'
    have htim :
        (axisParallelRectangleBoundaryPath z w t).im =
          AffineMap.lineMap z.im w.im (4 * (t : ℝ) - 2) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w t =
            AffineMap.lineMap (Complex.mk w.re z.im) w (4 * (t : ℝ) - 2) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_right_side z w
          (Set.Ioo_subset_Icc_self ht)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.im hside'
    have hparam :
        AffineMap.lineMap z.im w.im (4 * (s : ℝ) - 2) =
          AffineMap.lineMap z.im w.im (4 * (t : ℝ) - 2) := by
      simpa [hsim, htim] using congrArg Complex.im hst
    have hst' : 4 * (s : ℝ) - 2 = 4 * (t : ℝ) - 2 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff (p₀ := z.im) (p₁ := w.im)
        (c₁ := 4 * (s : ℝ) - 2) (c₂ := 4 * (t : ℝ) - 2)).mp hparam with hEq | hEq
      · exact (hIm.ne hEq).elim
      · exact hEq
    apply Subtype.ext
    linarith
  · rcases htop with ⟨hs, ht⟩
    -- On the top edge, the real coordinate is again a nonconstant affine parameter.
    have hsre :
        (axisParallelRectangleBoundaryPath z w s).re =
          AffineMap.lineMap w.re z.re (8 * (s : ℝ) - 6) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w s =
            AffineMap.lineMap w (Complex.mk z.re w.im) (8 * (s : ℝ) - 6) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_top_side z w
          (Set.Ioo_subset_Icc_self hs)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.re hside'
    have htre :
        (axisParallelRectangleBoundaryPath z w t).re =
          AffineMap.lineMap w.re z.re (8 * (t : ℝ) - 6) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w t =
            AffineMap.lineMap w (Complex.mk z.re w.im) (8 * (t : ℝ) - 6) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_top_side z w
          (Set.Ioo_subset_Icc_self ht)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.re hside'
    have hparam :
        AffineMap.lineMap w.re z.re (8 * (s : ℝ) - 6) =
          AffineMap.lineMap w.re z.re (8 * (t : ℝ) - 6) := by
      simpa [hsre, htre] using congrArg Complex.re hst
    have hst' : 8 * (s : ℝ) - 6 = 8 * (t : ℝ) - 6 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff (p₀ := w.re) (p₁ := z.re)
        (c₁ := 8 * (s : ℝ) - 6) (c₂ := 8 * (t : ℝ) - 6)).mp hparam with hEq | hEq
      · exact (hRe.ne hEq.symm).elim
      · exact hEq
    apply Subtype.ext
    linarith
  · rcases hleft with ⟨hs, ht⟩
    -- On the left edge, the imaginary coordinate is the strictly monotone parameter.
    have hsim :
        (axisParallelRectangleBoundaryPath z w s).im =
          AffineMap.lineMap w.im z.im (8 * (s : ℝ) - 7) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w s =
            AffineMap.lineMap (Complex.mk z.re w.im) z (8 * (s : ℝ) - 7) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_left_side z w
          (Set.Ioo_subset_Icc_self hs)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.im hside'
    have htim :
        (axisParallelRectangleBoundaryPath z w t).im =
          AffineMap.lineMap w.im z.im (8 * (t : ℝ) - 7) := by
      have hside' :
          axisParallelRectangleBoundaryPath z w t =
            AffineMap.lineMap (Complex.mk z.re w.im) z (8 * (t : ℝ) - 7) := by
        simpa using axisParallelRectangleBoundaryPath_eqOn_left_side z w
          (Set.Ioo_subset_Icc_self ht)
      simpa [AffineMap.lineMap_apply] using congrArg Complex.im hside'
    have hparam :
        AffineMap.lineMap w.im z.im (8 * (s : ℝ) - 7) =
          AffineMap.lineMap w.im z.im (8 * (t : ℝ) - 7) := by
      simpa [hsim, htim] using congrArg Complex.im hst
    have hst' : 8 * (s : ℝ) - 7 = 8 * (t : ℝ) - 7 := by
      rcases (AffineMap.lineMap_eq_lineMap_iff (p₀ := w.im) (p₁ := z.im)
        (c₁ := 8 * (s : ℝ) - 7) (c₂ := 8 * (t : ℝ) - 7)).mp hparam with hEq | hEq
      · exact (hIm.ne hEq.symm).elim
      · exact hEq
    apply Subtype.ext
    linarith

/-- Helper for Example II.1-extra-21: the four rectangle corners occur on the boundary path only
at the distinguished corner parameters, with `z` appearing at both endpoints. -/
lemma axis_parallel_rectangle_boundary_path_corner_fibers
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t : I} :
    (axisParallelRectangleBoundaryPath z w t = z ↔ t = (0 : I) ∨ t = (1 : I)) ∧
      (axisParallelRectangleBoundaryPath z w t = Complex.mk w.re z.im ↔
        t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I)) ∧
      (axisParallelRectangleBoundaryPath z w t = w ↔
        t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I)) ∧
      (axisParallelRectangleBoundaryPath z w t = Complex.mk z.re w.im ↔
        t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I)) := by
  constructor
  · constructor
    · intro ht
      -- Split the parameter into the open-side and corner cases and rule out the non-endpoint ones.
      rcases axis_parallel_rectangle_boundary_parameter_cases t with
        ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
      · exact Or.inl <| Subtype.ext ht0
      · have hcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
        have hre : z.re ∈ Set.Ioo z.re w.re := by
          simpa [ht] using hcoord.2
        linarith [hre.1]
      · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
        have hcorner :
            axisParallelRectangleBoundaryPath z w t = Complex.mk w.re z.im := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_half z w
        have hEq : Complex.mk w.re z.im = z := by simpa [hcorner] using ht
        have hre : w.re = z.re := by simpa using congrArg Complex.re hEq
        exact (hRe.ne hre.symm).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
        have hre : z.re = w.re := by
          simpa [ht] using hcoord.1
        exact (hRe.ne hre).elim
      · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
        have hcorner : axisParallelRectangleBoundaryPath z w t = w := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
        have hEq : w = z := by simpa [hcorner] using ht
        have him : w.im = z.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him.symm).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
        have him : z.im = w.im := by
          simpa [ht] using hcoord.1
        exact (hIm.ne him).elim
      · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
        have hcorner :
            axisParallelRectangleBoundaryPath z w t = Complex.mk z.re w.im := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
        have hEq : Complex.mk z.re w.im = z := by simpa [hcorner] using ht
        have him : w.im = z.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him.symm).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
        have him : z.im ∈ Set.Ioo z.im w.im := by
          simpa [ht] using hcoord.2
        linarith [him.1]
      · exact Or.inr <| Subtype.ext ht1
    · intro ht
      rcases ht with ht0 | ht1
      · simpa [ht0] using axis_parallel_rectangle_boundary_path_zero z w
      · simpa [ht1] using axis_parallel_rectangle_boundary_path_one z w
  constructor
  · constructor
    · intro ht
      -- The lower-right corner is excluded on each open side by a strict coordinate inequality.
      rcases axis_parallel_rectangle_boundary_parameter_cases t with
        ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
      · have ht' : t = (0 : I) := Subtype.ext ht0
        have hz : axisParallelRectangleBoundaryPath z w t = z := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
        have hEq : z = Complex.mk w.re z.im := by simpa [hz] using ht
        have hre : z.re = w.re := by simpa using congrArg Complex.re hEq
        exact (hRe.ne hre).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
        have hre : w.re ∈ Set.Ioo z.re w.re := by
          simpa [ht] using hcoord.2
        linarith [hre.2]
      · exact Subtype.ext hthalf
      · have hcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
        have him : z.im ∈ Set.Ioo z.im w.im := by
          simpa [ht] using hcoord.2
        linarith [him.1]
      · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
        have hw : axisParallelRectangleBoundaryPath z w t = w := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
        have hEq : w = Complex.mk w.re z.im := by simpa [hw] using ht
        have him : w.im = z.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him.symm).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
        have him : z.im = w.im := by simpa [ht] using hcoord.1
        exact (hIm.ne him).elim
      · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
        have hcorner :
            axisParallelRectangleBoundaryPath z w t = Complex.mk z.re w.im := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
        have hEq : Complex.mk z.re w.im = Complex.mk w.re z.im := by simpa [hcorner] using ht
        have hre : z.re = w.re := by simpa using congrArg Complex.re hEq
        exact (hRe.ne hre).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
        have hre : w.re = z.re := by simpa [ht] using hcoord.1
        exact (hRe.ne hre.symm).elim
      · have ht' : t = (1 : I) := Subtype.ext ht1
        have hz : axisParallelRectangleBoundaryPath z w t = z := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
        have hEq : z = Complex.mk w.re z.im := by simpa [hz] using ht
        have hre : z.re = w.re := by simpa using congrArg Complex.re hEq
        exact (hRe.ne hre).elim
    · intro ht
      simpa [ht] using axis_parallel_rectangle_boundary_path_half z w
  constructor
  · constructor
    · intro ht
      -- The upper-right corner is excluded on each non-corner case by one coordinate.
      rcases axis_parallel_rectangle_boundary_parameter_cases t with
        ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
      · have ht' : t = (0 : I) := Subtype.ext ht0
        have hz : axisParallelRectangleBoundaryPath z w t = z := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
        have hEq : z = w := by simpa [hz] using ht
        have him : z.im = w.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
        have him : w.im = z.im := by simpa [ht] using hcoord.1
        exact (hIm.ne him.symm).elim
      · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
        have hcorner :
            axisParallelRectangleBoundaryPath z w t = Complex.mk w.re z.im := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_half z w
        have hEq : Complex.mk w.re z.im = w := by simpa [hcorner] using ht
        have him : z.im = w.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
        have him : w.im ∈ Set.Ioo z.im w.im := by
          simpa [ht] using hcoord.2
        linarith [him.2]
      · exact Subtype.ext ht34
      · have hcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
        have hre : w.re ∈ Set.Ioo z.re w.re := by
          simpa [ht] using hcoord.2
        linarith [hre.2]
      · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
        have hcorner :
            axisParallelRectangleBoundaryPath z w t = Complex.mk z.re w.im := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
        have hEq : Complex.mk z.re w.im = w := by simpa [hcorner] using ht
        have hre : z.re = w.re := by simpa using congrArg Complex.re hEq
        exact (hRe.ne hre).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
        have hre : w.re = z.re := by simpa [ht] using hcoord.1
        exact (hRe.ne hre.symm).elim
      · have ht' : t = (1 : I) := Subtype.ext ht1
        have hz : axisParallelRectangleBoundaryPath z w t = z := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
        have hEq : z = w := by simpa [hz] using ht
        have him : z.im = w.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him).elim
    · intro ht
      simpa [ht] using axis_parallel_rectangle_boundary_path_three_quarters z w
  · constructor
    · intro ht
      -- The upper-left corner is excluded on each non-corner case by one coordinate.
      rcases axis_parallel_rectangle_boundary_parameter_cases t with
        ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
      · have ht' : t = (0 : I) := Subtype.ext ht0
        have hz : axisParallelRectangleBoundaryPath z w t = z := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
        have hEq : z = Complex.mk z.re w.im := by simpa [hz] using ht
        have him : z.im = w.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
        have him : w.im = z.im := by simpa [ht] using hcoord.1
        exact (hIm.ne him.symm).elim
      · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
        have hcorner :
            axisParallelRectangleBoundaryPath z w t = Complex.mk w.re z.im := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_half z w
        have hEq : Complex.mk w.re z.im = Complex.mk z.re w.im := by simpa [hcorner] using ht
        have hre : w.re = z.re := by simpa using congrArg Complex.re hEq
        exact (hRe.ne hre.symm).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
        have hre : z.re = w.re := by simpa [ht] using hcoord.1
        exact (hRe.ne hre).elim
      · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
        have hw : axisParallelRectangleBoundaryPath z w t = w := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
        have hEq : w = Complex.mk z.re w.im := by simpa [hw] using ht
        have hre : w.re = z.re := by simpa using congrArg Complex.re hEq
        exact (hRe.ne hre.symm).elim
      · have hcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
        have hre : z.re ∈ Set.Ioo z.re w.re := by
          simpa [ht] using hcoord.2
        linarith [hre.1]
      · exact Subtype.ext ht78
      · have hcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
        have him : w.im ∈ Set.Ioo z.im w.im := by
          simpa [ht] using hcoord.2
        linarith [him.2]
      · have ht' : t = (1 : I) := Subtype.ext ht1
        have hz : axisParallelRectangleBoundaryPath z w t = z := by
          simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
        have hEq : z = Complex.mk z.re w.im := by simpa [hz] using ht
        have him : z.im = w.im := by simpa using congrArg Complex.im hEq
        exact (hIm.ne him).elim
    · intro ht
      simpa [ht] using axis_parallel_rectangle_boundary_path_seven_eighths z w

