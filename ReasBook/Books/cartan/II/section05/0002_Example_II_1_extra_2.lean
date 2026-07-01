import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»

noncomputable section

open scoped unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Example II.1-extra-2: the boundary path of the axis-parallel rectangle with
opposite corners `z` and `w`, traversed through the four affine sides
`z → (w.re, z.im) → w → (z.re, w.im) → z`. -/
def axisParallelRectangleBoundaryPath (z w : ℂ) : Path z z :=
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  (Path.segment z zw).trans
    ((Path.segment zw w).trans
      ((Path.segment w wz).trans
        (Path.segment wz z)))

/-- Helper for Example II.1-extra-2: every real affine reparametrization is `C^1` on any set. -/
lemma contDiffOn_affine_reparam (m c : ℝ) (s : Set ℝ) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ m * t + c) s := by
  -- Real affine functions are built from the identity by multiplication and addition.
  simpa using
    ((contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ m) s).mul contDiffOn_id).add
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ c) s)

/-- Helper for Example II.1-extra-2: composing a line segment with a `C^1` parameter change that
stays inside `I` keeps the segment `C^1` on the source set. -/
lemma contDiffOn_lineMap_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} {f : ℝ → ℝ} {s : Set ℝ} (hf : ContDiffOn ℝ 1 f s) (hI : Set.MapsTo f s I) :
    ContDiffOn ℝ 1 (fun t ↦ AffineMap.lineMap a b (f t)) s := by
  -- Compose the smooth segment parametrization with the smooth affine time change.
  simpa [ContinuousAffineMap.coe_lineMap_eq] using
    (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) a b)).contDiffOn.comp hf hI

/-- Helper for Example II.1-extra-2: on the first time interval, the rectangle boundary path is the
bottom side segment from `z` to `(w.re, z.im)`. -/
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

/-- Helper for Example II.1-extra-2: on the second time interval, the rectangle boundary path is
the right side segment from `(w.re, z.im)` to `w`. -/
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

/-- Helper for Example II.1-extra-2: on the third time interval, the rectangle boundary path is
the top side segment from `w` to `(z.re, w.im)`. -/
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

/-- Helper for Example II.1-extra-2: on the final time interval, the rectangle boundary path is
the left side segment from `(z.re, w.im)` back to `z`. -/
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

/-- Example II.1-extra-2: the canonical boundary path of the axis-parallel rectangle with
opposite corners `z` and `w` is piecewise differentiable. -/
-- Proof sketch: each side is an affine segment, hence differentiable, and the only singular
-- parameters of the concatenated path are the three corner break points.
theorem axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable
    (z w : ℂ) :
    (axisParallelRectangleBoundaryPath z w).IsPiecewiseDifferentiable := by
  let subdiv : Fin (3 + 2) → ℝ := ![0, 1 / 2, 3 / 4, 7 / 8, 1]
  -- The nested concatenation changes side exactly at the three break points `1/2`, `3/4`, `7/8`.
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
