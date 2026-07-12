import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

open scoped unitInterval

noncomputable section

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
