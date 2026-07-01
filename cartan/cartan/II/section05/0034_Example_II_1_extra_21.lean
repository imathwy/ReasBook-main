import Mathlib
import cartan.II.section05.«0033_Definition_II_1_extra_20»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

/-- The boundary path of the axis-parallel rectangle with opposite corners `z` and `w`, traversed
through the four affine sides `z → (w.re, z.im) → w → (z.re, w.im) → z`. -/
def axisParallelRectangleBoundaryPath (z w : ℂ) : Path z z :=
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  (Path.segment z zw).trans
    ((Path.segment zw w).trans
      ((Path.segment w wz).trans
        (Path.segment wz z)))

/-- Every real affine reparametrization is `C^1` on any set. -/
lemma contDiffOn_affine_reparam (m c : ℝ) (s : Set ℝ) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ m * t + c) s := by
  -- Real affine functions are built from the identity by multiplication and addition.
  simpa using
    ((contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ m) s).mul contDiffOn_id).add
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ c) s)

/-- Composing a line segment with a `C^1` parameter change that stays inside `I` preserves
`C^1`-regularity on the source set. -/
lemma contDiffOn_lineMap_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ 1 f s) (hI : Set.MapsTo f s I) :
    ContDiffOn ℝ 1 (fun t ↦ AffineMap.lineMap a b (f t)) s := by
  -- Compose the smooth segment parametrization with the smooth affine time change.
  simpa [ContinuousAffineMap.coe_lineMap_eq] using
    (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) a b)).contDiffOn.comp hf hI

/-- On the first time interval, the rectangle boundary path is the bottom side segment. -/
lemma axisParallelRectangleBoundaryPath_eqOn_bottom_side (z w : ℂ) :
    Set.EqOn (axisParallelRectangleBoundaryPath z w).extend
      (fun t ↦ AffineMap.lineMap z (Complex.mk w.re z.im) (2 * t))
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro t ht
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  -- On the first half of the parameter interval, the outer concatenation follows the first side.
  have htrans :
      (axisParallelRectangleBoundaryPath z w).extend t = (Path.segment z zw).extend (2 * t) := by
    dsimp [axisParallelRectangleBoundaryPath, zw, wz]
    exact Path.extend_trans_of_le_half (γ₁ := Path.segment z zw)
      (γ₂ := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))) ht.2
  rw [htrans]
  -- A straight segment agrees with its affine line-map parametrization on `I`.
  have hI : 2 * t ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  simpa [zw] using Path.eqOn_extend_segment z zw hI

/-- On the second time interval, the rectangle boundary path is the right side segment. -/
lemma axisParallelRectangleBoundaryPath_eqOn_right_side (z w : ℂ) :
    Set.EqOn (axisParallelRectangleBoundaryPath z w).extend
      (fun t ↦ AffineMap.lineMap (Complex.mk w.re z.im) w (4 * t - 2))
      (Set.Icc (1 / 2) (3 / 4)) := by
  intro t ht
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  let γ₂ : Path zw z := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))
  -- After the first break point, the remaining nested path controls the motion.
  have houter :
      (axisParallelRectangleBoundaryPath z w).extend t = γ₂.extend (2 * t - 1) := by
    dsimp [axisParallelRectangleBoundaryPath, zw, wz, γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment z zw) (γ₂ := γ₂) (by linarith [ht.1])
  -- On this interval, that remaining path is still in the first half of its own parameter.
  have hinner :
      γ₂.extend (2 * t - 1) = (Path.segment zw w).extend (2 * (2 * t - 1)) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_le_half (γ₁ := Path.segment zw w)
      (γ₂ := (Path.segment w wz).trans (Path.segment wz z)) (by linarith [ht.1, ht.2])
  rw [houter, hinner]
  have hI : 2 * (2 * t - 1) ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hseg := Path.eqOn_extend_segment zw w hI
  calc
    (Path.segment zw w).extend (2 * (2 * t - 1))
        = AffineMap.lineMap zw w (2 * (2 * t - 1)) := hseg
    _ = AffineMap.lineMap zw w (4 * t - 2) := by
      congr 1
      ring

/-- On the third time interval, the rectangle boundary path is the top side segment. -/
lemma axisParallelRectangleBoundaryPath_eqOn_top_side (z w : ℂ) :
    Set.EqOn (axisParallelRectangleBoundaryPath z w).extend
      (fun t ↦ AffineMap.lineMap w (Complex.mk z.re w.im) (8 * t - 6))
      (Set.Icc (3 / 4) (7 / 8)) := by
  intro t ht
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  let γ₂ : Path zw z := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))
  let γ₃ : Path w z := (Path.segment w wz).trans (Path.segment wz z)
  -- First pass through the outer concatenation to the remaining three sides.
  have houter :
      (axisParallelRectangleBoundaryPath z w).extend t = γ₂.extend (2 * t - 1) := by
    dsimp [axisParallelRectangleBoundaryPath, zw, wz, γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment z zw) (γ₂ := γ₂) (by linarith [ht.1])
  -- Then pass through the second side to the final two sides.
  have hmid :
      γ₂.extend (2 * t - 1) = γ₃.extend (2 * (2 * t - 1) - 1) := by
    dsimp [γ₂, γ₃]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment zw w) (γ₂ := γ₃)
      (by linarith [ht.1, ht.2])
  -- On this interval, the last nested concatenation is still on its first half.
  have hinner :
      γ₃.extend (2 * (2 * t - 1) - 1) =
        (Path.segment w wz).extend (2 * (2 * (2 * t - 1) - 1)) := by
    dsimp [γ₃]
    exact Path.extend_trans_of_le_half (γ₁ := Path.segment w wz) (γ₂ := Path.segment wz z)
      (by linarith [ht.1, ht.2])
  rw [houter, hmid, hinner]
  have hI : 2 * (2 * (2 * t - 1) - 1) ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hseg := Path.eqOn_extend_segment w wz hI
  calc
    (Path.segment w wz).extend (2 * (2 * (2 * t - 1) - 1))
        = AffineMap.lineMap w wz (2 * (2 * (2 * t - 1) - 1)) := hseg
    _ = AffineMap.lineMap w wz (8 * t - 6) := by
      congr 1
      ring

/-- On the final time interval, the rectangle boundary path is the left side segment. -/
lemma axisParallelRectangleBoundaryPath_eqOn_left_side (z w : ℂ) :
    Set.EqOn (axisParallelRectangleBoundaryPath z w).extend
      (fun t ↦ AffineMap.lineMap (Complex.mk z.re w.im) z (8 * t - 7))
      (Set.Icc (7 / 8) (1 : ℝ)) := by
  intro t ht
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  let γ₂ : Path zw z := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))
  let γ₃ : Path w z := (Path.segment w wz).trans (Path.segment wz z)
  -- First pass through the outer concatenation to the remaining three sides.
  have houter :
      (axisParallelRectangleBoundaryPath z w).extend t = γ₂.extend (2 * t - 1) := by
    dsimp [axisParallelRectangleBoundaryPath, zw, wz, γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment z zw) (γ₂ := γ₂) (by linarith [ht.1])
  -- Then pass through the second side to the final two sides.
  have hmid :
      γ₂.extend (2 * t - 1) = γ₃.extend (2 * (2 * t - 1) - 1) := by
    dsimp [γ₂, γ₃]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment zw w) (γ₂ := γ₃)
      (by linarith [ht.1, ht.2])
  -- On the final interval, the last nested concatenation is on its second half.
  have hinner :
      γ₃.extend (2 * (2 * t - 1) - 1) =
        (Path.segment wz z).extend (2 * (2 * (2 * t - 1) - 1) - 1) := by
    dsimp [γ₃]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment w wz) (γ₂ := Path.segment wz z)
      (by linarith [ht.1, ht.2])
  rw [houter, hmid, hinner]
  have hI : 2 * (2 * (2 * t - 1) - 1) - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hseg := Path.eqOn_extend_segment wz z hI
  calc
    (Path.segment wz z).extend (2 * (2 * (2 * t - 1) - 1) - 1)
        = AffineMap.lineMap wz z (2 * (2 * (2 * t - 1) - 1) - 1) := hseg
    _ = AffineMap.lineMap wz z (8 * t - 7) := by
      congr 1
      ring

/-- The canonical boundary path of the axis-parallel rectangle is piecewise differentiable. -/
theorem axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable (z w : ℂ) :
    (axisParallelRectangleBoundaryPath z w).IsPiecewiseDifferentiable := by
  let subdiv : Fin (3 + 2) → ℝ := ![0, 1 / 2, 3 / 4, 7 / 8, 1]
  -- The nested concatenation changes side exactly at the three break points.
  refine ⟨3, subdiv, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [subdiv] at hij ⊢ <;> linarith
  · simp [subdiv]
  · simp [subdiv]
  · intro i
    fin_cases i
    · -- On the first subinterval, the path is an affine parametrization of the bottom side.
      have hparam :
          ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t) (Set.Icc (0 : ℝ) (1 / 2)) := by
        simpa using contDiffOn_affine_reparam 2 0 (Set.Icc (0 : ℝ) (1 / 2))
      have hI : Set.MapsTo (fun t : ℝ ↦ 2 * t) (Set.Icc (0 : ℝ) (1 / 2)) I := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2]
      have hside :
          ContDiffOn ℝ 1
            (fun t ↦ AffineMap.lineMap z (Complex.mk w.re z.im) (2 * t))
            (Set.Icc (0 : ℝ) (1 / 2)) :=
        contDiffOn_lineMap_comp_affine hparam hI
      simpa [subdiv] using
        hside.congr (fun t ht => axisParallelRectangleBoundaryPath_eqOn_bottom_side z w ht)
    · -- On the second subinterval, the path is an affine parametrization of the right side.
      have hparam :
          ContDiffOn ℝ 1 (fun t : ℝ ↦ 4 * t - 2) (Set.Icc (1 / 2) (3 / 4)) := by
        simpa [sub_eq_add_neg] using contDiffOn_affine_reparam 4 (-2) (Set.Icc (1 / 2) (3 / 4))
      have hI : Set.MapsTo (fun t : ℝ ↦ 4 * t - 2) (Set.Icc (1 / 2) (3 / 4)) I := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2]
      have hside :
          ContDiffOn ℝ 1
            (fun t : ℝ ↦ AffineMap.lineMap (Complex.mk w.re z.im) w (4 * t - 2))
            (Set.Icc (1 / 2) (3 / 4)) :=
        contDiffOn_lineMap_comp_affine hparam hI
      simpa [subdiv] using
        hside.congr (fun t ht => axisParallelRectangleBoundaryPath_eqOn_right_side z w ht)
    · -- On the third subinterval, the path is an affine parametrization of the top side.
      have hparam :
          ContDiffOn ℝ 1 (fun t : ℝ ↦ 8 * t - 6) (Set.Icc (3 / 4) (7 / 8)) := by
        simpa [sub_eq_add_neg] using contDiffOn_affine_reparam 8 (-6) (Set.Icc (3 / 4) (7 / 8))
      have hI : Set.MapsTo (fun t : ℝ ↦ 8 * t - 6) (Set.Icc (3 / 4) (7 / 8)) I := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2]
      have hside :
          ContDiffOn ℝ 1
            (fun t : ℝ ↦ AffineMap.lineMap w (Complex.mk z.re w.im) (8 * t - 6))
            (Set.Icc (3 / 4) (7 / 8)) :=
        contDiffOn_lineMap_comp_affine hparam hI
      simpa [subdiv] using
        hside.congr (fun t ht => axisParallelRectangleBoundaryPath_eqOn_top_side z w ht)
    · -- On the last subinterval, the path is an affine parametrization of the left side.
      have hparam :
          ContDiffOn ℝ 1 (fun t : ℝ ↦ 8 * t - 7) (Set.Icc (7 / 8) (1 : ℝ)) := by
        simpa [sub_eq_add_neg] using contDiffOn_affine_reparam 8 (-7) (Set.Icc (7 / 8) (1 : ℝ))
      have hI : Set.MapsTo (fun t : ℝ ↦ 8 * t - 7) (Set.Icc (7 / 8) (1 : ℝ)) I := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2]
      have hside :
          ContDiffOn ℝ 1
            (fun t ↦ AffineMap.lineMap (Complex.mk z.re w.im) z (8 * t - 7))
            (Set.Icc (7 / 8) (1 : ℝ)) :=
        contDiffOn_lineMap_comp_affine hparam hI
      simpa [subdiv] using
        hside.congr (fun t ht => axisParallelRectangleBoundaryPath_eqOn_left_side z w ht)

/-- Helper for Example II.1-extra-21: the range of a horizontal complex segment is the
corresponding real interval at fixed imaginary part. -/
lemma range_segment_horizontal (a b c : ℝ) :
    Set.range (Path.segment (Complex.mk a c) (Complex.mk b c)) =
      Set.uIcc a b ×ℂ ({c} : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    -- Read the segment point coordinatewise.
    rw [Complex.mem_reProdIm]
    constructor
    · simpa [Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, Set.uIcc] using
        (lineMap_mem_segment ℝ a b t.2)
    · simp [Path.segment, AffineMap.lineMap_apply]
  · intro hx
    rw [Complex.mem_reProdIm] at hx
    have hcont :
        ContinuousOn (fun t : ℝ ↦ AffineMap.lineMap a b t) (Set.Icc (0 : ℝ) 1) := by
      simpa [ContinuousAffineMap.coe_lineMap_eq] using
        (ContinuousAffineMap.continuous (ContinuousAffineMap.lineMap (R := ℝ) a b)).continuousOn
    have hsurj : Set.SurjOn (AffineMap.lineMap a b) (Set.Icc (0 : ℝ) 1) (Set.uIcc a b) :=
      by
        simpa using hcont.surjOn_uIcc (a := (0 : ℝ)) (b := (1 : ℝ))
          (by constructor <;> norm_num) (by constructor <;> norm_num)
    rcases hsurj hx.1 with ⟨t, ht, hline⟩
    -- Choose the parameter whose real coordinate is the requested point.
    have hxc : x.im = c := by simpa using hx.2
    have hline' : t * (b - a) + a = x.re := by
      simpa [AffineMap.lineMap_apply] using hline
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Complex.ext <;> simp [Path.segment, AffineMap.lineMap_apply, hline', hxc]

/-- Helper for Example II.1-extra-21: the range of a vertical complex segment is the
corresponding real interval at fixed real part. -/
lemma range_segment_vertical (a b c : ℝ) :
    Set.range (Path.segment (Complex.mk c a) (Complex.mk c b)) =
      ({c} : Set ℝ) ×ℂ Set.uIcc a b := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    -- Read the segment point coordinatewise.
    rw [Complex.mem_reProdIm]
    constructor
    · simp [Path.segment, AffineMap.lineMap_apply]
    · simpa [Path.segment, AffineMap.lineMap_apply, segment_eq_uIcc, Set.uIcc] using
        (lineMap_mem_segment ℝ a b t.2)
  · intro hx
    rw [Complex.mem_reProdIm] at hx
    have hcont :
        ContinuousOn (fun t : ℝ ↦ AffineMap.lineMap a b t) (Set.Icc (0 : ℝ) 1) := by
      simpa [ContinuousAffineMap.coe_lineMap_eq] using
        (ContinuousAffineMap.continuous (ContinuousAffineMap.lineMap (R := ℝ) a b)).continuousOn
    have hsurj : Set.SurjOn (AffineMap.lineMap a b) (Set.Icc (0 : ℝ) 1) (Set.uIcc a b) :=
      by
        simpa using hcont.surjOn_uIcc (a := (0 : ℝ)) (b := (1 : ℝ))
          (by constructor <;> norm_num) (by constructor <;> norm_num)
    rcases hsurj hx.2 with ⟨t, ht, hline⟩
    -- Choose the parameter whose imaginary coordinate is the requested point.
    have hxc : x.re = c := by simpa using hx.1
    have hline' : t * (b - a) + a = x.im := by
      simpa [AffineMap.lineMap_apply] using hline
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Complex.ext <;> simp [Path.segment, AffineMap.lineMap_apply, hline', hxc]

/-- Helper for Example II.1-extra-21: the frontier of an axis-parallel rectangle is the union of
its four closed sides. -/
lemma complex_rectangle_frontier_eq_edge_union (z w : ℂ) :
    frontier (Complex.Rectangle z w) =
      (Set.uIcc z.re w.re ×ℂ ({z.im} : Set ℝ)) ∪
        (({w.re} : Set ℝ) ×ℂ Set.uIcc z.im w.im) ∪
          ((Set.uIcc z.re w.re ×ℂ ({w.im} : Set ℝ)) ∪
            (({z.re} : Set ℝ) ×ℂ Set.uIcc z.im w.im)) := by
  rcases le_total z.re w.re with hre | hre
  · rcases le_total z.im w.im with him | him
    · ext x
      -- With ordered coordinates, the product frontier splits into the four closed edges.
      constructor <;> intro hx <;>
        simp [Complex.Rectangle, Complex.frontier_reProdIm, Complex.mem_reProdIm, Set.uIcc, hre,
          him] at hx ⊢ <;>
        tauto
    · ext x
      -- The same computation works after reversing the imaginary interval endpoints.
      constructor <;> intro hx <;>
        simp [Complex.Rectangle, Complex.frontier_reProdIm, Complex.mem_reProdIm, Set.uIcc, hre,
          him] at hx ⊢ <;>
        tauto
  · rcases le_total z.im w.im with him | him
    · ext x
      -- The same computation works after reversing the real interval endpoints.
      constructor <;> intro hx <;>
        simp [Complex.Rectangle, Complex.frontier_reProdIm, Complex.mem_reProdIm, Set.uIcc, hre,
          him] at hx ⊢ <;>
        tauto
    · ext x
      -- Reversing both coordinates still yields the same four geometric edges.
      constructor <;> intro hx <;>
        simp [Complex.Rectangle, Complex.frontier_reProdIm, Complex.mem_reProdIm, Set.uIcc, hre,
          him] at hx ⊢ <;>
        tauto

-- Proof sketch: use `Path.trans_range` repeatedly to write the image of the boundary path as the
-- union of the four side segments, identify each segment image with `Path.range_segment`, and then
-- compare this union with the explicit description of `frontier (Complex.Rectangle z w)`.
theorem axisParallelRectangleBoundaryPath_range_eq_frontier (z w : ℂ) :
    Set.range (axisParallelRectangleBoundaryPath z w) =
      frontier (Complex.Rectangle z w) :=
    by
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  -- Expand the concatenation into the four oriented sides.
  rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
  rw [range_segment_horizontal z.re w.re z.im]
  rw [range_segment_vertical z.im w.im w.re]
  rw [range_segment_horizontal w.re z.re w.im]
  rw [range_segment_vertical w.im z.im z.re]
  -- The four side ranges are exactly the four edge pieces of the frontier.
  rw [complex_rectangle_frontier_eq_edge_union z w]
  ext x
  simp [Set.uIcc, min_comm, max_comm, or_assoc]

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

/-- Helper for Example II.1-extra-21: equality of two points on the rectangle boundary path
forces equality of the parameters, except for the endpoint identification `0 ~ 1`. -/
lemma axis_parallel_rectangle_boundary_path_simple_eq_or_endpoints
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {s t : I}
    (hst : axisParallelRectangleBoundaryPath z w s = axisParallelRectangleBoundaryPath z w t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  let br : ℂ := Complex.mk w.re z.im
  let tl : ℂ := Complex.mk z.re w.im
  have hsFib := axis_parallel_rectangle_boundary_path_corner_fibers z w hRe hIm (t := s)
  have htFib := axis_parallel_rectangle_boundary_path_corner_fibers z w hRe hIm (t := t)
  have hs_z : axisParallelRectangleBoundaryPath z w s = z ↔ s = (0 : I) ∨ s = (1 : I) := hsFib.1
  have ht_z : axisParallelRectangleBoundaryPath z w t = z ↔ t = (0 : I) ∨ t = (1 : I) := htFib.1
  have hs_br :
      axisParallelRectangleBoundaryPath z w s = br ↔
        s = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := by
    simpa [br] using hsFib.2.1
  have ht_br :
      axisParallelRectangleBoundaryPath z w t = br ↔
        t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := by
    simpa [br] using htFib.2.1
  have hs_w : axisParallelRectangleBoundaryPath z w s = w ↔
      s = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := hsFib.2.2.1
  have ht_w : axisParallelRectangleBoundaryPath z w t = w ↔
      t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := htFib.2.2.1
  have hs_tl :
      axisParallelRectangleBoundaryPath z w s = tl ↔
        s = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := by
    simpa [tl] using hsFib.2.2.2
  have ht_tl :
      axisParallelRectangleBoundaryPath z w t = tl ↔
        t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := by
    simpa [tl] using htFib.2.2.2
  -- Separate the boundary parameters into endpoint, corner, and open-side cases.
  rcases axis_parallel_rectangle_boundary_parameter_cases s with
    hs0 | hsbottom | hshalf | hsright | hs34 | hstop | hs78 | hsleft | hs1
  · have hs' : s = (0 : I) := Subtype.ext hs0
    have htz : axisParallelRectangleBoundaryPath z w t = z := by
      have hsz : axisParallelRectangleBoundaryPath z w s = z := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_zero z w
      calc
        axisParallelRectangleBoundaryPath z w t = axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = z := hsz
    rcases ht_z.mp htz with ht0 | ht1
    · exact Or.inl <| by simpa [hs', ht0]
    · exact Or.inr <| Or.inl <| by simp [hs', ht1]
  · have hscoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe hsbottom
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        simpa [hsEq] using hscoord.2
      linarith [hre.1]
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        simpa [br, hsEq] using hscoord.2
      linarith [hre.2]
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have him : w.im = z.im := by simpa [hsEq] using hscoord.1
      exact (hIm.ne him.symm).elim
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have him : w.im = z.im := by simpa [tl, hsEq] using hscoord.1
      exact (hIm.ne him.symm).elim
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inl ⟨hsbottom, htbottom⟩) hst
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = w.re := htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
      have him : z.im = w.im := by
        calc
          z.im = (axisParallelRectangleBoundaryPath z w s).im := by simpa using hscoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w t).im := by
            simpa using congrArg Complex.im hst
          _ = w.im := htcoord.1
      exact (hIm.ne him).elim
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = z.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = z.re := htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.1]
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hshalf
    have hstbr : axisParallelRectangleBoundaryPath z w t = br := by
      have hsbr : axisParallelRectangleBoundaryPath z w s = br := by
        simpa [br, hs'] using axis_parallel_rectangle_boundary_path_half z w
      calc
        axisParallelRectangleBoundaryPath z w t = axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = br := hsbr
    exact Or.inl <| by simpa [hs', ht_br.mp hstbr]
  · have hscoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm hsright
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have hre : z.re = w.re := by simpa [hsEq] using hscoord.1
      exact (hRe.ne hre).elim
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have him : z.im ∈ Set.Ioo z.im w.im := by
        simpa [br, hsEq] using hscoord.2
      linarith [him.1]
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have him : w.im ∈ Set.Ioo z.im w.im := by
        simpa [hsEq] using hscoord.2
      linarith [him.2]
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have hre : z.re = w.re := by simpa [tl, hsEq] using hscoord.1
      exact (hRe.ne hre).elim
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w t).re =
                (axisParallelRectangleBoundaryPath z w s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = w.re := hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inr <| Or.inl ⟨hsright, htright⟩) hst
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w t).re =
                (axisParallelRectangleBoundaryPath z w s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = w.re := hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
      have hre : z.re = w.re := by
        calc
          z.re = (axisParallelRectangleBoundaryPath z w t).re := by simpa using htcoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w s).re := by
            simpa using congrArg Complex.re hst.symm
          _ = w.re := hscoord.1
      exact (hRe.ne hre).elim
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext hs34
    have hstw : axisParallelRectangleBoundaryPath z w t = w := by
      have hsw : axisParallelRectangleBoundaryPath z w s = w := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      calc
        axisParallelRectangleBoundaryPath z w t = axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = w := hsw
    exact Or.inl <| by simpa [hs', ht_w.mp hstw]
  · have hscoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe hstop
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have him : z.im = w.im := by simpa [hsEq] using hscoord.1
      exact (hIm.ne him).elim
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have him : z.im = w.im := by simpa [br, hsEq] using hscoord.1
      exact (hIm.ne him).elim
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        simpa [hsEq] using hscoord.2
      linarith [hre.2]
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        simpa [tl, hsEq] using hscoord.2
      linarith [hre.1]
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
      have him : z.im = w.im := by
        calc
          z.im = (axisParallelRectangleBoundaryPath z w t).im := by simpa using htcoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w s).im := by
            simpa using congrArg Complex.im hst.symm
          _ = w.im := hscoord.1
      exact (hIm.ne him).elim
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
      have hre : w.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = w.re := htcoord.1
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = w.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = w.re := htre
        simpa [hsre] using hscoord.2
      linarith [hre.2]
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inr <| Or.inr <| Or.inl ⟨hstop, httop⟩) hst
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm htleft
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        have hsre : (axisParallelRectangleBoundaryPath z w s).re = z.re := by
          calc
            (axisParallelRectangleBoundaryPath z w s).re =
                (axisParallelRectangleBoundaryPath z w t).re := by
                  simpa using congrArg Complex.re hst
            _ = z.re := htcoord.1
        simpa [hsre] using hscoord.2
      linarith [hre.1]
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext hs78
    have hsttl : axisParallelRectangleBoundaryPath z w t = tl := by
      have hstl : axisParallelRectangleBoundaryPath z w s = tl := by
        simpa [tl, hs'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      calc
        axisParallelRectangleBoundaryPath z w t = axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = tl := hstl
    exact Or.inl <| by simpa [hs', ht_tl.mp hsttl]
  · have hscoord := axis_parallel_rectangle_boundary_path_left_coordinates z w hIm hsleft
    have hs_ne_z : axisParallelRectangleBoundaryPath z w s ≠ z := by
      intro hsEq
      have him : z.im ∈ Set.Ioo z.im w.im := by
        simpa [hsEq] using hscoord.2
      linarith [him.1]
    have hs_ne_br : axisParallelRectangleBoundaryPath z w s ≠ br := by
      intro hsEq
      have hre : w.re = z.re := by simpa [br, hsEq] using hscoord.1
      exact (hRe.ne hre.symm).elim
    have hs_ne_w : axisParallelRectangleBoundaryPath z w s ≠ w := by
      intro hsEq
      have hre : w.re = z.re := by simpa [hsEq] using hscoord.1
      exact (hRe.ne hre.symm).elim
    have hs_ne_tl : axisParallelRectangleBoundaryPath z w s ≠ tl := by
      intro hsEq
      have him : w.im ∈ Set.Ioo z.im w.im := by
        simpa [tl, hsEq] using hscoord.2
      linarith [him.2]
    rcases axis_parallel_rectangle_boundary_parameter_cases t with
      ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
    · have ht' : t = (0 : I) := Subtype.ext ht0
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_zero z w
      exact (hs_ne_z (hst.trans htz)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_bottom_coordinates z w hRe htbottom
      have hre : z.re ∈ Set.Ioo z.re w.re := by
        have htre : (axisParallelRectangleBoundaryPath z w t).re = z.re := by
          calc
            (axisParallelRectangleBoundaryPath z w t).re =
                (axisParallelRectangleBoundaryPath z w s).re := by
                  simpa using congrArg Complex.re hst.symm
            _ = z.re := hscoord.1
        simpa [htre] using htcoord.2
      linarith [hre.1]
    · have ht' : t = (⟨(1 / 2 : ℝ), half_mem_unitInterval⟩ : I) := Subtype.ext hthalf
      have htbr : axisParallelRectangleBoundaryPath z w t = br := by
        simpa [br, ht'] using axis_parallel_rectangle_boundary_path_half z w
      exact (hs_ne_br (hst.trans htbr)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_right_coordinates z w hIm htright
      have hre : z.re = w.re := by
        calc
          z.re = (axisParallelRectangleBoundaryPath z w s).re := by simpa using hscoord.1.symm
          _ = (axisParallelRectangleBoundaryPath z w t).re := by
            simpa using congrArg Complex.re hst
          _ = w.re := htcoord.1
      exact (hRe.ne hre).elim
    · have ht' : t = (⟨(3 / 4 : ℝ), three_quarters_mem_unitInterval⟩ : I) := Subtype.ext ht34
      have htw : axisParallelRectangleBoundaryPath z w t = w := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_three_quarters z w
      exact (hs_ne_w (hst.trans htw)).elim
    · have htcoord := axis_parallel_rectangle_boundary_path_top_coordinates z w hRe httop
      have him : w.im ∈ Set.Ioo z.im w.im := by
        have htim : (axisParallelRectangleBoundaryPath z w t).im = w.im := htcoord.1
        have hsim : (axisParallelRectangleBoundaryPath z w s).im = w.im := by
          calc
            (axisParallelRectangleBoundaryPath z w s).im =
                (axisParallelRectangleBoundaryPath z w t).im := by
                  simpa using congrArg Complex.im hst
            _ = w.im := htim
        simpa [hsim] using hscoord.2
      linarith [him.2]
    · have ht' : t = (⟨(7 / 8 : ℝ), seven_eighths_mem_unitInterval⟩ : I) := Subtype.ext ht78
      have httl : axisParallelRectangleBoundaryPath z w t = tl := by
        simpa [tl, ht'] using axis_parallel_rectangle_boundary_path_seven_eighths z w
      exact (hs_ne_tl (hst.trans httl)).elim
    · exact Or.inl <|
        axis_parallel_rectangle_boundary_path_same_side_injective z w hRe hIm
          (Or.inr <| Or.inr <| Or.inr ⟨hsleft, htleft⟩) hst
    · have ht' : t = (1 : I) := Subtype.ext ht1
      have htz : axisParallelRectangleBoundaryPath z w t = z := by
        simpa [ht'] using axis_parallel_rectangle_boundary_path_one z w
      exact (hs_ne_z (hst.trans htz)).elim
  · have hs' : s = (1 : I) := Subtype.ext hs1
    have htz : axisParallelRectangleBoundaryPath z w t = z := by
      have hsz : axisParallelRectangleBoundaryPath z w s = z := by
        simpa [hs'] using axis_parallel_rectangle_boundary_path_one z w
      calc
        axisParallelRectangleBoundaryPath z w t = axisParallelRectangleBoundaryPath z w s := hst.symm
        _ = z := hsz
    rcases ht_z.mp htz with ht0 | ht1
    · exact Or.inr <| Or.inr <| by simp [hs', ht0]
    · exact Or.inl <| by simpa [hs', ht1]

/-- Helper for Example II.1-extra-21: the lower-right corner is a genuine corner of the boundary
path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
lemma axis_parallel_rectangle_boundary_not_differentiable_at_half
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) :
    ¬ DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  sorry
  /-
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
  let d : Plane := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    simpa [d] using hdiff.hasDerivWithinAt
  have hleftMain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · exact ht.1
    · linarith [ht.2]
  have hrightMain : HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  let bottom : ℝ → Plane := fun t ↦ (AffineMap.lineMap z.re w.re (2 * t), z.im)
  let right : ℝ → Plane := fun t ↦ (w.re, AffineMap.lineMap z.im w.im (4 * t - 2))
  have hbottomEq :
      Set.EqOn γ bottom (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap z (Complex.mk w.re z.im) (2 * t) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_bottom_side z w ht
    ext
    · simpa [γ, bottom, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, bottom, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hrightEq :
      Set.EqOn γ right (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk w.re z.im) w (4 * t - 2) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_right_side z w ht
    ext
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hbottomDeriv :
      HasDerivWithinAt bottom ((2 * (w.re - z.re), 0) : Plane)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap z.re w.re (2 * t))
          (2 * (w.re - z.re)) (1 / 2 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := z.re) (b := w.re) (x := 2 * (1 / 2 : ℝ))).comp
          (1 / 2 : ℝ) ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2) using 1
      · ext t
        simp [two_mul]
      · ring
    simpa [bottom] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (1 / 2 : ℝ) z.im).hasDerivWithinAt
  have hrightDeriv :
      HasDerivWithinAt right (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap z.im w.im (4 * t - 2))
          (4 * (w.im - z.im)) (1 / 2 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := z.im) (b := w.im) (x := 4 * (1 / 2 : ℝ) - 2)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 4).sub_const 2) using 1
      · ext t
        ring
      · ring
    simpa [right] using
      (hasDerivAt_const (1 / 2 : ℝ) w.re).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have hbottomγ :
      HasDerivWithinAt γ ((2 * (w.re - z.re), 0) : Plane)
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply hbottomDeriv.congr hbottomEq
    exact hbottomEq (1 / 2 : ℝ) (by constructor <;> norm_num)
  have hrightγ :
      HasDerivWithinAt γ (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    apply hrightDeriv.congr hrightEq
    exact hrightEq (1 / 2 : ℝ) (by constructor <;> norm_num)
  have hleftUD :
      UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (0 : ℝ) (1 / 2 : ℝ)) ?_ ?_
    · refine ⟨1 / 4, ?_⟩
      simp
    · exact subset_closure (by constructor <;> norm_num)
  have hrightUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) ?_ ?_
    · refine ⟨5 / 8, ?_⟩
      simp
    · exact subset_closure (by constructor <;> norm_num)
  have hcompare : (2 * (w.re - z.re), 0 : Plane) = (0, 4 * (w.im - z.im) : Plane) := by
    calc
      (2 * (w.re - z.re), 0 : Plane)
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact hbottomγ.derivWithin hleftUD
      _ = d := hleftMain.derivWithin hleftUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact hrightMain.derivWithin hrightUD
      _ = (0, 4 * (w.im - z.im) : Plane) := hrightγ.derivWithin hrightUD
  have hre : 2 * (w.re - z.re) = 0 := by
    simpa using congrArg Prod.fst hcompare
  have him : 4 * (w.im - z.im) = 0 := by
    simpa using congrArg Prod.snd hcompare
  linarith
-/

/-- Helper for Example II.1-extra-21: the upper-right corner is a genuine corner of the boundary
path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
lemma axis_parallel_rectangle_boundary_not_differentiable_at_three_quarters
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) :
    ¬ DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (3 / 4 : ℝ) := by
  sorry
  /-
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
  let d : Plane := derivWithin γ (Set.Icc (0 : ℝ) 1) (3 / 4 : ℝ)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (3 / 4 : ℝ) := by
    simpa [d] using hdiff.hasDerivWithinAt
  have hrightMain : HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have htopMain : HasDerivWithinAt γ d (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  let right : ℝ → Plane := fun t ↦ (w.re, AffineMap.lineMap z.im w.im (4 * t - 2))
  let top : ℝ → Plane := fun t ↦ (AffineMap.lineMap w.re z.re (8 * t - 6), w.im)
  have hrightEq :
      Set.EqOn γ right (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk w.re z.im) w (4 * t - 2) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_right_side z w ht
    ext
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, right, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have htopEq :
      Set.EqOn γ top (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap w (Complex.mk z.re w.im) (8 * t - 6) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_top_side z w ht
    ext
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hrightDeriv :
      HasDerivWithinAt right (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap z.im w.im (4 * t - 2))
          (4 * (w.im - z.im)) (3 / 4 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := z.im) (b := w.im) (x := 4 * (3 / 4 : ℝ) - 2)).comp
          (3 / 4 : ℝ) (((hasDerivAt_id (3 / 4 : ℝ)).const_mul 4).sub_const 2) using 1
      · ext t
        ring
      · ring
    simpa [right] using
      (hasDerivAt_const (3 / 4 : ℝ) w.re).hasDerivWithinAt.prodMk hsnd.hasDerivWithinAt
  have htopDeriv :
      HasDerivWithinAt top (8 * (z.re - w.re), 0 : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap w.re z.re (8 * t - 6))
          (8 * (z.re - w.re)) (3 / 4 : ℝ) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using
        (AffineMap.hasDerivAt_lineMap (a := w.re) (b := z.re) (x := 8 * (3 / 4 : ℝ) - 6)).comp
          (3 / 4 : ℝ) (((hasDerivAt_id (3 / 4 : ℝ)).const_mul 8).sub_const 6)
    simpa [top] using hfst.hasDerivWithinAt.prod (hasDerivAt_const (3 / 4 : ℝ) w.im).hasDerivWithinAt
  have hrightγ :
      HasDerivWithinAt γ (((0 : ℝ), 4 * (w.im - z.im)) : Plane)
        (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    apply hrightDeriv.congr hrightEq
    exact hrightEq (3 / 4 : ℝ) (by constructor <;> norm_num)
  have htopγ :
      HasDerivWithinAt γ (8 * (z.re - w.re), 0 : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    apply htopDeriv.congr htopEq
    exact htopEq (3 / 4 : ℝ) (by constructor <;> norm_num)
  have hrightUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) ?_ ?_
    · refine ⟨5 / 8, ?_⟩
      simp
    · exact subset_closure (by constructor <;> norm_num)
  have htopUD :
      UniqueDiffWithinAt ℝ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) ?_ ?_
    · refine ⟨13 / 16, ?_⟩
      simp
    · exact subset_closure (by constructor <;> norm_num)
  have hcompare : (0, 4 * (w.im - z.im) : Plane) = (8 * (z.re - w.re), 0 : Plane) := by
    calc
      (0, 4 * (w.im - z.im) : Plane)
          = derivWithin γ (Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ)) (3 / 4 : ℝ) := by
            symm
            exact hrightγ.derivWithin hrightUD
      _ = d := hrightMain.derivWithin hrightUD
      _ = derivWithin γ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (3 / 4 : ℝ) := by
            symm
            exact htopMain.derivWithin htopUD
      _ = (8 * (z.re - w.re), 0 : Plane) := htopγ.derivWithin htopUD
  have hre : 8 * (z.re - w.re) = 0 := by
    simpa using congrArg Prod.fst hcompare
  have him : 4 * (w.im - z.im) = 0 := by
    simpa using congrArg Prod.snd hcompare
  linarith
-/

/-- Helper for Example II.1-extra-21: the upper-left corner is a genuine corner of the boundary
path, so the real-plane parametrization is not differentiable there within `[0, 1]`. -/
lemma axis_parallel_rectangle_boundary_not_differentiable_at_seven_eighths
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) :
    ¬ DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (7 / 8 : ℝ) := by
  sorry
  /-
  intro hdiff
  let γ : ℝ → Plane := ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
  let d : Plane := derivWithin γ (Set.Icc (0 : ℝ) 1) (7 / 8 : ℝ)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (7 / 8 : ℝ) := by
    simpa [d] using hdiff.hasDerivWithinAt
  have htopMain : HasDerivWithinAt γ d (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hleftMain : HasDerivWithinAt γ d (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · exact ht.2
  let top : ℝ → Plane := fun t ↦ (AffineMap.lineMap w.re z.re (8 * t - 6), w.im)
  let left : ℝ → Plane := fun t ↦ (z.re, AffineMap.lineMap w.im z.im (8 * t - 7))
  have htopEq :
      Set.EqOn γ top (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap w (Complex.mk z.re w.im) (8 * t - 6) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_top_side z w ht
    ext
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, top, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have hleftEq :
      Set.EqOn γ left (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) := by
    intro t ht
    have hside :
        (axisParallelRectangleBoundaryPath z w).toClosedPath.toPath.extend t =
          AffineMap.lineMap (Complex.mk z.re w.im) z (8 * t - 7) := by
      simpa [Path.toClosedPath] using axisParallelRectangleBoundaryPath_eqOn_left_side z w ht
    ext
    · simpa [γ, left, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.re hside
    · simpa [γ, left, ClosedPath.realCurve, Function.comp, AffineMap.lineMap_apply] using
        congrArg Complex.im hside
  have htopDeriv :
      HasDerivWithinAt top ((8 * (z.re - w.re), 0) : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    have hfst :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap w.re z.re (8 * t - 6))
          (8 * (z.re - w.re)) (7 / 8 : ℝ) := by
      convert
        (AffineMap.hasDerivAt_lineMap (a := w.re) (b := z.re) (x := 8 * (7 / 8 : ℝ) - 6)).comp
          (7 / 8 : ℝ) (((hasDerivAt_id (7 / 8 : ℝ)).const_mul 8).sub_const 6) using 1
      · ext t
        ring
      · ring
    simpa [top] using
      hfst.hasDerivWithinAt.prodMk (hasDerivAt_const (7 / 8 : ℝ) w.im).hasDerivWithinAt
  have hleftDeriv :
      HasDerivWithinAt left (0, 8 * (z.im - w.im) : Plane)
        (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    have hsnd :
        HasDerivAt (fun t : ℝ ↦ AffineMap.lineMap w.im z.im (8 * t - 7))
          (8 * (z.im - w.im)) (7 / 8 : ℝ) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using
        (AffineMap.hasDerivAt_lineMap (a := w.im) (b := z.im) (x := 8 * (7 / 8 : ℝ) - 7)).comp
          (7 / 8 : ℝ) (((hasDerivAt_id (7 / 8 : ℝ)).const_mul 8).sub_const 7)
    simpa [left] using (hasDerivAt_const (7 / 8 : ℝ) z.re).hasDerivWithinAt.prod hsnd.hasDerivWithinAt
  have htopγ :
      HasDerivWithinAt γ ((8 * (z.re - w.re), 0) : Plane)
        (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    apply htopDeriv.congr htopEq
    exact htopEq (7 / 8 : ℝ) (by constructor <;> norm_num)
  have hleftγ :
      HasDerivWithinAt γ (0, 8 * (z.im - w.im) : Plane)
        (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    apply hleftDeriv.congr hleftEq
    exact hleftEq (7 / 8 : ℝ) (by constructor <;> norm_num)
  have htopUD :
      UniqueDiffWithinAt ℝ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) ?_ ?_
    · refine ⟨13 / 16, ?_⟩
      simp
    · exact subset_closure (by constructor <;> norm_num)
  have hleftUD :
      UniqueDiffWithinAt ℝ (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
    refine uniqueDiffWithinAt_convex (convex_Icc (7 / 8 : ℝ) (1 : ℝ)) ?_ ?_
    · refine ⟨15 / 16, ?_⟩
      simp
    · exact subset_closure (by constructor <;> norm_num)
  have hcompare : (8 * (z.re - w.re), 0 : Plane) = (0, 8 * (z.im - w.im) : Plane) := by
    calc
      (8 * (z.re - w.re), 0 : Plane)
          = derivWithin γ (Set.Icc (3 / 4 : ℝ) (7 / 8 : ℝ)) (7 / 8 : ℝ) := by
            symm
            exact htopγ.derivWithin htopUD
      _ = d := htopMain.derivWithin htopUD
      _ = derivWithin γ (Set.Icc (7 / 8 : ℝ) (1 : ℝ)) (7 / 8 : ℝ) := by
            symm
            exact hleftMain.derivWithin hleftUD
      _ = (0, 8 * (z.im - w.im) : Plane) := hleftγ.derivWithin hleftUD
  have hre : 8 * (z.re - w.re) = 0 := by
    simpa using congrArg Prod.fst hcompare
  have him : 8 * (z.im - w.im) = 0 := by
    simpa using congrArg Prod.snd hcompare
  linarith
-/

/-- Helper for Example II.1-extra-21: a regular interior parameter of the rectangle boundary path
must lie on exactly one of the four open side intervals, because the three intermediate corner
parameters are not differentiable. -/
lemma axis_parallel_rectangle_boundary_regular_parameter_mem_side_interval
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨
      t₀ ∈ Set.Ioo (1 / 2) (3 / 4) ∨
      t₀ ∈ Set.Ioo (3 / 4) (7 / 8) ∨
      t₀ ∈ Set.Ioo (7 / 8) (1 : ℝ) := by
  sorry
  /-
  let t : I := ⟨t₀, ⟨ht₀.1.le, ht₀.2.le⟩⟩
  rcases axis_parallel_rectangle_boundary_parameter_cases t with
    ht0 | htbottom | hthalf | htright | ht34 | httop | ht78 | htleft | ht1
  · exact (ht₀.1.ne' ht0).elim
  · exact Or.inl htbottom
  · exact
      (axis_parallel_rectangle_boundary_not_differentiable_at_half z w hRe hIm)
        (by
          have ht0 : t₀ = 1 / 2 := by simpa [t] using hthalf
          simpa [ht0] using hdiff)
  · exact Or.inr <| Or.inl htright
  · exact
      (axis_parallel_rectangle_boundary_not_differentiable_at_three_quarters z w hRe hIm)
        (by
          have ht0 : t₀ = 3 / 4 := by simpa [t] using ht34
          simpa [ht0] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inl httop
  · exact
      (axis_parallel_rectangle_boundary_not_differentiable_at_seven_eighths z w hRe hIm)
        (by
          have ht0 : t₀ = 7 / 8 := by simpa [t] using ht78
          simpa [ht0] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inr htleft
  · exact (ht₀.2.ne ht1).elim
-/

lemma axis_parallel_rectangle_boundary_path_exists_boundary_straightening
    (z w : ℂ) (hRe : z.re < w.re) (hIm : z.im < w.im) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Complex.Rectangle z w)
        ((axisParallelRectangleBoundaryPath z w).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the corner-exclusion/classification step is now finished, so only the
  -- explicit strip-chart construction for the four affine side models remains.
  rcases axis_parallel_rectangle_boundary_regular_parameter_mem_side_interval z w hRe hIm ht₀ hdiff with
    htbottom | htright | httop | htleft
  · -- TODO: build the bottom-side affine strip chart and verify the left-side interior condition.
    sorry
  · -- TODO: build the right-side affine strip chart and verify the left-side interior condition.
    sorry
  · -- TODO: build the top-side affine strip chart and verify the left-side interior condition.
    sorry
  · -- TODO: build the left-side affine strip chart and verify the left-side interior condition.
    sorry

/-- Example II.1-extra-21: if `z` is the lower-left corner and `w` the upper-right corner of a
nondegenerate axis-parallel rectangle, then the canonical boundary path gives a singleton family
that is an oriented boundary of `Complex.Rectangle z w`. -/
theorem axisParallelRectangleBoundary_isOrientedBoundaryOf (z w : ℂ)
    (hRe : z.re < w.re) (hIm : z.im < w.im) :
    IsOrientedBoundaryOf (Complex.Rectangle z w)
      (fun _ : Unit ↦ (axisParallelRectangleBoundaryPath z w).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (axisParallelRectangleBoundaryPath z w).toClosedPath
  change IsOrientedBoundaryOf (Complex.Rectangle z w) Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The rectangle is the product of two compact real intervals.
    simpa [Complex.Rectangle] using isCompact_uIcc.reProdIm isCompact_uIcc
  · rintro ⟨⟩
    -- The singleton loop inherits the known piecewise differentiability of the rectangle boundary.
    simpa [Γ] using
      axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable z w
  · rintro ⟨⟩ s t hst
    -- Delegate the loop simplicity to the explicit side-by-side coordinate analysis.
    exact axis_parallel_rectangle_boundary_path_simple_eq_or_endpoints z w hRe hIm hst
  · intro i j hij
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i, Set.range ((Γ i : ClosedPath ℂ) : C(I, ℂ))) =
          Set.range (axisParallelRectangleBoundaryPath z w) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        cases i
        simpa [Γ, Path.toClosedPath] using hi
      · intro hx
        refine Set.mem_iUnion.mpr ?_
        refine ⟨(), ?_⟩
        simpa [Γ, Path.toClosedPath] using hx
    -- Rewrite the singleton union back to the boundary-path image, then invoke the frontier theorem.
    simpa [ClosedPath.range_toPath] using
      hboundary.trans (axisParallelRectangleBoundaryPath_range_eq_frontier z w)
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- Delegate the regular-point chart to the side-local affine straightening helper.
    exact axis_parallel_rectangle_boundary_path_exists_boundary_straightening
      z w hRe hIm ht₀ hdiff hderiv
