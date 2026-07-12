import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0010_Proposition_4_1»
import DifferentialForms_Cartan_1970.I.section04.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.III.section12.«0038_Exercise_25».PiCotKernel

noncomputable section

open scoped Topology unitInterval

/-- The half-side length of the square contour `γ_n`. -/
def exercise25SquareRadius (n : ℕ) : ℝ :=
  n + (1 / 2 : ℝ)

/-- The positively oriented square contour with vertices
`±(n + 1 / 2) ± (n + 1 / 2) i`. -/
def exercise25SquareBoundary (n : ℕ) :
    Path (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
      (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I) :=
  axisParallelRectangleBoundaryPath
    (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
    ((exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)

/-- Helper for Exercise 25: on the first parameter interval, the square boundary path follows the
bottom horizontal side from `-r - r i` to `r - r i`. -/
lemma exercise25_square_boundary_eqOn_bottom_side (n : ℕ) :
    Set.EqOn (exercise25SquareBoundary n).extend
      (fun t ↦
        AffineMap.lineMap
          (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          ((exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          (2 * t))
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro t ht
  -- Route correction: specialize the rectangle-boundary side computation directly to the square.
  let r : ℝ := exercise25SquareRadius n
  let z : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  -- On the first half of the concatenation, the contour is exactly the bottom segment.
  have htrans :
      (exercise25SquareBoundary n).extend t = (Path.segment z zw).extend (2 * t) := by
    dsimp [exercise25SquareBoundary, axisParallelRectangleBoundaryPath, r, z, zw, w, wz]
    exact Path.extend_trans_of_le_half (γ₁ := Path.segment z zw)
      (γ₂ := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))) ht.2
  rw [htrans]
  have hI : 2 * t ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hzw : zw = (r : ℂ) - r * Complex.I := by
    apply Complex.ext <;> simp [zw, z, w, r]
  -- Once the square corner is identified, the standard segment extension formula finishes.
  simpa [hzw, r, z, zw, w, wz] using Path.eqOn_extend_segment z zw hI

/-- Helper for Exercise 25: on the second parameter interval, the square boundary path follows the
right vertical side from `r - r i` to `r + r i`. -/
lemma exercise25_square_boundary_eqOn_right_side (n : ℕ) :
    Set.EqOn (exercise25SquareBoundary n).extend
      (fun t ↦
        AffineMap.lineMap
          ((exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          ((exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (4 * t - 2))
      (Set.Icc (1 / 2) (3 / 4)) := by
  intro t ht
  let r : ℝ := exercise25SquareRadius n
  let z : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  let γ₂ : Path zw z := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))
  -- Discard the bottom segment, then reparametrize the remaining path.
  have houter :
      (exercise25SquareBoundary n).extend t = γ₂.extend (2 * t - 1) := by
    dsimp [exercise25SquareBoundary, axisParallelRectangleBoundaryPath, r, z, zw, w, wz, γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment z zw) (γ₂ := γ₂)
      (by linarith [ht.1])
  have hinner :
      γ₂.extend (2 * t - 1) = (Path.segment zw w).extend (2 * (2 * t - 1)) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_le_half (γ₁ := Path.segment zw w)
      (γ₂ := (Path.segment w wz).trans (Path.segment wz z)) (by linarith [ht.1, ht.2])
  rw [houter, hinner]
  have hI : 2 * (2 * t - 1) ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hseg := Path.eqOn_extend_segment zw w hI
  have hzw : zw = (r : ℂ) - r * Complex.I := by
    apply Complex.ext <;> simp [zw, z, w, r]
  -- The right side is the affine segment between the two right-hand corners.
  calc
    (Path.segment zw w).extend (2 * (2 * t - 1))
        = AffineMap.lineMap zw w (2 * (2 * t - 1)) := hseg
    _ = AffineMap.lineMap zw w (4 * t - 2) := by
      congr 1
      ring
    _ = AffineMap.lineMap ((r : ℂ) - r * Complex.I) ((r : ℂ) + r * Complex.I) (4 * t - 2) := by
      simp [hzw, w, r]

/-- Helper for Exercise 25: on the third parameter interval, the square boundary path follows the
top horizontal side from `r + r i` to `-r + r i`. -/
lemma exercise25_square_boundary_eqOn_top_side (n : ℕ) :
    Set.EqOn (exercise25SquareBoundary n).extend
      (fun t ↦
        AffineMap.lineMap
          ((exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (-(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (8 * t - 6))
      (Set.Icc (3 / 4) (7 / 8)) := by
  intro t ht
  let r : ℝ := exercise25SquareRadius n
  let z : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  let γ₂ : Path zw z := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))
  let γ₃ : Path w z := (Path.segment w wz).trans (Path.segment wz z)
  -- Peel off the first two sides before identifying the top segment.
  have houter :
      (exercise25SquareBoundary n).extend t = γ₂.extend (2 * t - 1) := by
    dsimp [exercise25SquareBoundary, axisParallelRectangleBoundaryPath, r, z, zw, w, wz, γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment z zw) (γ₂ := γ₂)
      (by linarith [ht.1])
  have hmid :
      γ₂.extend (2 * t - 1) = γ₃.extend (2 * (2 * t - 1) - 1) := by
    dsimp [γ₂, γ₃]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment zw w) (γ₂ := γ₃)
      (by linarith [ht.1, ht.2])
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
  have hwz : wz = -(r : ℂ) + r * Complex.I := by
    apply Complex.ext <;> simp [wz, z, w, r]
  -- The remaining segment is the top side from the top-right corner to the top-left corner.
  calc
    (Path.segment w wz).extend (2 * (2 * (2 * t - 1) - 1))
        = AffineMap.lineMap w wz (2 * (2 * (2 * t - 1) - 1)) := hseg
    _ = AffineMap.lineMap w wz (8 * t - 6) := by
      congr 1
      ring
    _ = AffineMap.lineMap ((r : ℂ) + r * Complex.I) (-(r : ℂ) + r * Complex.I) (8 * t - 6) := by
      simp [hwz, w, r]

/-- Helper for Exercise 25: on the final parameter interval, the square boundary path follows the
left vertical side from `-r + r i` back to `-r - r i`. -/
lemma exercise25_square_boundary_eqOn_left_side (n : ℕ) :
    Set.EqOn (exercise25SquareBoundary n).extend
      (fun t ↦
        AffineMap.lineMap
          (-(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          (8 * t - 7))
      (Set.Icc (7 / 8) (1 : ℝ)) := by
  intro t ht
  let r : ℝ := exercise25SquareRadius n
  let z : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z.im
  let wz : ℂ := Complex.mk z.re w.im
  let γ₂ : Path zw z := (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z))
  let γ₃ : Path w z := (Path.segment w wz).trans (Path.segment wz z)
  -- Peel off the first three sides before identifying the closing left segment.
  have houter :
      (exercise25SquareBoundary n).extend t = γ₂.extend (2 * t - 1) := by
    dsimp [exercise25SquareBoundary, axisParallelRectangleBoundaryPath, r, z, zw, w, wz, γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment z zw) (γ₂ := γ₂)
      (by linarith [ht.1])
  have hmid :
      γ₂.extend (2 * t - 1) = γ₃.extend (2 * (2 * t - 1) - 1) := by
    dsimp [γ₂, γ₃]
    exact Path.extend_trans_of_half_le (γ₁ := Path.segment zw w) (γ₂ := γ₃)
      (by linarith [ht.1, ht.2])
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
  have hwz : wz = -(r : ℂ) + r * Complex.I := by
    apply Complex.ext <;> simp [wz, z, w, r]
  -- The final quarter closes the square along the left side.
  calc
    (Path.segment wz z).extend (2 * (2 * (2 * t - 1) - 1) - 1)
        = AffineMap.lineMap wz z (2 * (2 * (2 * t - 1) - 1) - 1) := hseg
    _ = AffineMap.lineMap wz z (8 * t - 7) := by
      congr 1
      ring
    _ = AffineMap.lineMap (-(r : ℂ) + r * Complex.I) (-(r : ℂ) - r * Complex.I) (8 * t - 7) := by
      simp [hwz, z, r]

/-- Helper for Exercise 25: on the bottom side, the square boundary has explicit coordinates. -/
lemma exercise25_square_boundary_bottom_coordinates (n : ℕ) {t : I}
    (ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (exercise25SquareBoundary n t).re = (4 * (t : ℝ) - 1) * exercise25SquareRadius n ∧
      (exercise25SquareBoundary n t).im = -exercise25SquareRadius n := by
  have hside :
      (exercise25SquareBoundary n).extend (t : ℝ) =
        AffineMap.lineMap
          (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          ((exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          (2 * (t : ℝ)) :=
    exercise25_square_boundary_eqOn_bottom_side n ht
  have hpath :
      exercise25SquareBoundary n t =
        AffineMap.lineMap
          (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          ((exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          (2 * (t : ℝ)) := by
    simpa using hside
  constructor
  · -- Read the real part of the affine parametrization of the bottom edge.
    have hre :
        (exercise25SquareBoundary n t).re =
          2 * (t : ℝ) * exercise25SquareRadius n +
            2 * (t : ℝ) * exercise25SquareRadius n - exercise25SquareRadius n := by
      simpa [AffineMap.lineMap_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using congrArg Complex.re hpath
    nlinarith
  · -- The imaginary part stays fixed at the bottom value `-r`.
    simpa [AffineMap.lineMap_apply] using congrArg Complex.im hpath

/-- Helper for Exercise 25: on the right side, the square boundary has explicit coordinates. -/
lemma exercise25_square_boundary_right_coordinates (n : ℕ) {t : I}
    (ht : (t : ℝ) ∈ Set.Icc (1 / 2) (3 / 4)) :
    (exercise25SquareBoundary n t).re = exercise25SquareRadius n ∧
      (exercise25SquareBoundary n t).im = (8 * (t : ℝ) - 5) * exercise25SquareRadius n := by
  have hside :
      (exercise25SquareBoundary n).extend (t : ℝ) =
        AffineMap.lineMap
          ((exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          ((exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (4 * (t : ℝ) - 2) :=
    exercise25_square_boundary_eqOn_right_side n ht
  have hpath :
      exercise25SquareBoundary n t =
        AffineMap.lineMap
          ((exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          ((exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (4 * (t : ℝ) - 2) := by
    simpa using hside
  constructor
  · -- The real part stays fixed at the right-hand value `r`.
    simpa [AffineMap.lineMap_apply] using congrArg Complex.re hpath
  · -- Read the imaginary part of the affine parametrization of the right edge.
    have him :
        (exercise25SquareBoundary n t).im =
          (4 * (t : ℝ) - 2) * exercise25SquareRadius n +
            (4 * (t : ℝ) - 2) * exercise25SquareRadius n - exercise25SquareRadius n := by
      simpa [AffineMap.lineMap_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using congrArg Complex.im hpath
    nlinarith

/-- Helper for Exercise 25: on the top side, the square boundary has explicit coordinates. -/
lemma exercise25_square_boundary_top_coordinates (n : ℕ) {t : I}
    (ht : (t : ℝ) ∈ Set.Icc (3 / 4) (7 / 8)) :
    (exercise25SquareBoundary n t).re = (13 - 16 * (t : ℝ)) * exercise25SquareRadius n ∧
      (exercise25SquareBoundary n t).im = exercise25SquareRadius n := by
  have hside :
      (exercise25SquareBoundary n).extend (t : ℝ) =
        AffineMap.lineMap
          ((exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (-(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (8 * (t : ℝ) - 6) :=
    exercise25_square_boundary_eqOn_top_side n ht
  have hpath :
      exercise25SquareBoundary n t =
        AffineMap.lineMap
          ((exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (-(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (8 * (t : ℝ) - 6) := by
    simpa using hside
  constructor
  · -- Read the real part of the affine parametrization of the top edge.
    have hre :
        (exercise25SquareBoundary n t).re =
          exercise25SquareRadius n +
            (-(exercise25SquareRadius n * (-6 + (t : ℝ) * 8)) +
              -(exercise25SquareRadius n * (-6 + (t : ℝ) * 8))) := by
      simpa [AffineMap.lineMap_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using congrArg Complex.re hpath
    nlinarith
  · -- The imaginary part stays fixed at the top value `r`.
    simpa [AffineMap.lineMap_apply] using congrArg Complex.im hpath

/-- Helper for Exercise 25: on the left side, the square boundary has explicit coordinates. -/
lemma exercise25_square_boundary_left_coordinates (n : ℕ) {t : I}
    (ht : (t : ℝ) ∈ Set.Icc (7 / 8) (1 : ℝ)) :
    (exercise25SquareBoundary n t).re = -exercise25SquareRadius n ∧
      (exercise25SquareBoundary n t).im = (15 - 16 * (t : ℝ)) * exercise25SquareRadius n := by
  have hside :
      (exercise25SquareBoundary n).extend (t : ℝ) =
        AffineMap.lineMap
          (-(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          (8 * (t : ℝ) - 7) :=
    exercise25_square_boundary_eqOn_left_side n ht
  have hpath :
      exercise25SquareBoundary n t =
        AffineMap.lineMap
          (-(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I)
          (-(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I)
          (8 * (t : ℝ) - 7) := by
    simpa using hside
  constructor
  · -- The real part stays fixed at the left-hand value `-r`.
    simpa [AffineMap.lineMap_apply] using congrArg Complex.re hpath
  · -- Read the imaginary part of the affine parametrization of the left edge.
    have him :
        (exercise25SquareBoundary n t).im =
          exercise25SquareRadius n +
            (-(exercise25SquareRadius n * (-7 + (t : ℝ) * 8)) +
              -(exercise25SquareRadius n * (-7 + (t : ℝ) * 8))) := by
      simpa [AffineMap.lineMap_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using congrArg Complex.im hpath
    nlinarith

/-- Helper for Exercise 25: every point on the square contour `γ_n` lies on the square frontier,
so both coordinates have absolute value at most the radius, one coordinate has absolute value equal
to the radius, and the radius is bounded by the norm. -/
lemma exercise25_square_boundary_geometry (n : ℕ) {z : ℂ}
    (hz : z ∈ Set.range (exercise25SquareBoundary n)) :
    |z.re| ≤ exercise25SquareRadius n ∧
      |z.im| ≤ exercise25SquareRadius n ∧
      (|z.re| = exercise25SquareRadius n ∨ |z.im| = exercise25SquareRadius n) ∧
      exercise25SquareRadius n ≤ ‖z‖ := by
  rcases hz with ⟨t, rfl⟩
  let r : ℝ := exercise25SquareRadius n
  have hr_nonneg : 0 ≤ r := by
    -- The square radius is `n + 1/2`, hence nonnegative.
    dsimp [r, exercise25SquareRadius]
    positivity
  rcases le_total (t : ℝ) (1 / 2) with hbottom | hbottom
  · have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨t.2.1, hbottom⟩
    rcases exercise25_square_boundary_bottom_coordinates n ht with ⟨hre, him⟩
    have hcoeff_lower : -1 ≤ 4 * (t : ℝ) - 1 := by
      nlinarith [t.2.1]
    have hcoeff_upper : 4 * (t : ℝ) - 1 ≤ 1 := by
      nlinarith [hbottom]
    have hre_bound : |(exercise25SquareBoundary n t).re| ≤ r := by
      rw [hre]
      apply abs_le.mpr
      constructor <;> nlinarith
    have him_bound : |(exercise25SquareBoundary n t).im| ≤ r := by
      simp [r, him, abs_neg, abs_of_nonneg hr_nonneg]
    have hside : |(exercise25SquareBoundary n t).im| = r := by
      rw [him, abs_neg, abs_of_nonneg hr_nonneg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [r] using hre_bound
    · simpa [r] using him_bound
    · refine Or.inr ?_
      simpa [r] using hside
    · -- The side equality upgrades the coordinate bound to the norm lower bound.
      calc
        r = |(exercise25SquareBoundary n t).im| := by simpa [r] using hside.symm
        _ ≤ ‖exercise25SquareBoundary n t‖ := Complex.abs_im_le_norm _
  · rcases le_total (t : ℝ) (3 / 4) with hright | hright
    · have ht : (t : ℝ) ∈ Set.Icc (1 / 2) (3 / 4) := ⟨hbottom, hright⟩
      rcases exercise25_square_boundary_right_coordinates n ht with ⟨hre, him⟩
      have hcoeff_lower : -1 ≤ 8 * (t : ℝ) - 5 := by
        nlinarith [hbottom]
      have hcoeff_upper : 8 * (t : ℝ) - 5 ≤ 1 := by
        nlinarith [hright]
      have hre_bound : |(exercise25SquareBoundary n t).re| ≤ r := by
        simp [r, hre, abs_of_nonneg hr_nonneg]
      have him_bound : |(exercise25SquareBoundary n t).im| ≤ r := by
        rw [him]
        apply abs_le.mpr
        constructor <;> nlinarith
      have hside : |(exercise25SquareBoundary n t).re| = r := by
        rw [hre, abs_of_nonneg hr_nonneg]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [r] using hre_bound
      · simpa [r] using him_bound
      · refine Or.inl ?_
        simpa [r] using hside
      · -- On the vertical edge, the real-part equality gives the norm lower bound.
        calc
          r = |(exercise25SquareBoundary n t).re| := by simpa [r] using hside.symm
          _ ≤ ‖exercise25SquareBoundary n t‖ := Complex.abs_re_le_norm _
    · rcases le_total (t : ℝ) (7 / 8) with htop | htop
      · have ht : (t : ℝ) ∈ Set.Icc (3 / 4) (7 / 8) := ⟨hright, htop⟩
        rcases exercise25_square_boundary_top_coordinates n ht with ⟨hre, him⟩
        have hcoeff_lower : -1 ≤ 13 - 16 * (t : ℝ) := by
          nlinarith [htop]
        have hcoeff_upper : 13 - 16 * (t : ℝ) ≤ 1 := by
          nlinarith [hright]
        have hre_bound : |(exercise25SquareBoundary n t).re| ≤ r := by
          rw [hre]
          apply abs_le.mpr
          constructor <;> nlinarith
        have him_bound : |(exercise25SquareBoundary n t).im| ≤ r := by
          simp [r, him, abs_of_nonneg hr_nonneg]
        have hside : |(exercise25SquareBoundary n t).im| = r := by
          rw [him, abs_of_nonneg hr_nonneg]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [r] using hre_bound
        · simpa [r] using him_bound
        · refine Or.inr ?_
          simpa [r] using hside
        · -- The top-edge imaginary coordinate again controls the whole norm.
          calc
            r = |(exercise25SquareBoundary n t).im| := by simpa [r] using hside.symm
            _ ≤ ‖exercise25SquareBoundary n t‖ := Complex.abs_im_le_norm _
      · have ht : (t : ℝ) ∈ Set.Icc (7 / 8) (1 : ℝ) := ⟨htop, t.2.2⟩
        rcases exercise25_square_boundary_left_coordinates n ht with ⟨hre, him⟩
        have hcoeff_lower : -1 ≤ 15 - 16 * (t : ℝ) := by
          nlinarith [t.2.2]
        have hcoeff_upper : 15 - 16 * (t : ℝ) ≤ 1 := by
          nlinarith [htop]
        have hre_bound : |(exercise25SquareBoundary n t).re| ≤ r := by
          simp [r, hre, abs_neg, abs_of_nonneg hr_nonneg]
        have him_bound : |(exercise25SquareBoundary n t).im| ≤ r := by
          rw [him]
          apply abs_le.mpr
          constructor <;> nlinarith
        have hside : |(exercise25SquareBoundary n t).re| = r := by
          rw [hre, abs_neg, abs_of_nonneg hr_nonneg]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [r] using hre_bound
        · simpa [r] using him_bound
        · refine Or.inl ?_
          simpa [r] using hside
        · -- Route correction: the left edge now uses the explicit coordinate lemma, not a raw
          -- transport through the nested path definition.
          calc
            r = |(exercise25SquareBoundary n t).re| := by simpa [r] using hside.symm
            _ ≤ ‖exercise25SquareBoundary n t‖ := Complex.abs_re_le_norm _

/-- Helper for Exercise 25: the cosine on a horizontal translate is controlled by the
corresponding hyperbolic cosine. -/
lemma exercise25_norm_cos_add_mul_I_le_cosh (x t : ℝ) :
    ‖Complex.cos (x + t * Complex.I)‖ ≤ Real.cosh t := by
  -- Compare squares because both sides are nonnegative.
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.cosh_pos _).le]
  have hsq :
      ‖Complex.cos (x + t * Complex.I)‖ ^ 2 = Real.cos x ^ 2 + Real.sinh t ^ 2 := by
    simpa [Complex.sq_norm] using (normSq_cos_add_mul_I x t)
  have htrig := Real.sin_sq_add_cos_sq x
  have hcosh := Real.cosh_sq t
  nlinarith

/-- Helper for Exercise 25: the norm of `sin (x + t i)` dominates `|sinh t|`. -/
lemma exercise25_abs_sinh_le_norm_sin_add_mul_I (x t : ℝ) :
    |Real.sinh t| ≤ ‖Complex.sin (x + t * Complex.I)‖ := by
  -- Compare squares and discard the nonnegative `sin^2 x` term.
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)]
  have habs_sq : |Real.sinh t| ^ 2 = Real.sinh t ^ 2 := by
    rw [sq_abs]
  have hsq :
      ‖Complex.sin (x + t * Complex.I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh t ^ 2 := by
    simpa [Complex.sq_norm] using (normSq_sin_add_mul_I x t)
  have hsin_nonneg : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  nlinarith [hsq, habs_sq]

/-- Helper for Exercise 25: once `u ≥ π / 2`, the hyperbolic cotangent is bounded by an explicit
constant independent of `u`. -/
lemma exercise25_cosh_div_sinh_le_uniform {u : ℝ} (hu : Real.pi / 2 ≤ u) :
    Real.cosh u / Real.sinh u ≤ 2 / (1 - Real.exp (-Real.pi)) := by
  have hu_pos : 0 < u := by
    linarith [Real.pi_pos]
  have hsinh_pos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu_pos
  have hexp_lt_one : Real.exp (-Real.pi) < 1 := by
    simpa using (Real.exp_lt_exp.mpr (by linarith [Real.pi_pos] : -Real.pi < 0))
  have hcoef_nonneg : 0 ≤ 1 - Real.exp (-Real.pi) := sub_nonneg.mpr hexp_lt_one.le
  have hcosh_le_exp : Real.cosh u ≤ Real.exp u := by
    -- `exp u = cosh u + sinh u`, and `sinh u` is nonnegative for `u ≥ 0`.
    rw [← Real.cosh_add_sinh]
    exact le_add_of_nonneg_right (Real.sinh_nonneg_iff.mpr hu_pos.le)
  have hExpTail :
      Real.exp (-u) ≤ Real.exp (-Real.pi) * Real.exp u := by
    have hrewrite : Real.exp (-u) = Real.exp (-2 * u) * Real.exp u := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hrewrite]
    have hmain : Real.exp (-2 * u) ≤ Real.exp (-Real.pi) := by
      exact Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right hmain (Real.exp_pos u).le
  have hsinh_lower :
      (1 - Real.exp (-Real.pi)) * Real.exp u ≤ 2 * Real.sinh u := by
    -- Rewrite `sinh` via exponentials and use the exponential tail estimate.
    rw [Real.sinh_eq]
    nlinarith
  have hcross :
      Real.cosh u * (1 - Real.exp (-Real.pi)) ≤ 2 * Real.sinh u := by
    have hleft :
        Real.cosh u * (1 - Real.exp (-Real.pi)) ≤ Real.exp u * (1 - Real.exp (-Real.pi)) := by
      exact mul_le_mul_of_nonneg_right hcosh_le_exp hcoef_nonneg
    exact hleft.trans <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hsinh_lower
  have hcoef_pos : 0 < 1 - Real.exp (-Real.pi) := sub_pos.mpr hexp_lt_one
  -- Cross-multiply through the two positive denominators.
  exact (div_le_div_iff₀ hsinh_pos hcoef_pos).2 <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

/-- Helper for Exercise 25: on the half-integer square sides, the trigonometric factors take the
textbook values `cos (π x) = 0` and `sin (π x)^2 = 1`. -/
lemma exercise25_half_integer_trig_of_abs_eq_squareRadius (n : ℕ) {x : ℝ}
    (hx : |x| = exercise25SquareRadius n) :
    Real.cos (Real.pi * x) = 0 ∧ Real.sin (Real.pi * x) ^ 2 = 1 := by
  have hcos_pos : Real.cos (Real.pi * exercise25SquareRadius n) = 0 := by
    -- Rewrite the positive half-integer side to the imported Exercise 14 evaluation.
    simpa [exercise25SquareRadius, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
      cos_pi_nat_add_half n
  have hsin_pos : Real.sin (Real.pi * exercise25SquareRadius n) ^ 2 = 1 := by
    -- The matching sine-square identity is the second imported half-integer evaluation.
    simpa [exercise25SquareRadius, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
      sin_sq_pi_nat_add_half n
  -- Split the absolute-value condition into the two half-integer sides of the square.
  rcases eq_or_eq_neg_of_abs_eq hx with rfl | rfl
  · exact ⟨hcos_pos, hsin_pos⟩
  · constructor
    · -- Cosine is even, so the negative half-integer side has the same value.
      rw [mul_neg, Real.cos_neg]
      exact hcos_pos
    · -- Sine is odd, but squaring removes the sign.
      rw [mul_neg, Real.sin_neg]
      simpa [pow_two] using hsin_pos

/-- Helper for Exercise 25: on a vertical side of `γ_n`, the denominator `sin (π z)` has norm
`cosh (π Im z)`. -/
lemma exercise25_norm_sin_pi_of_re_abs_eq_radius (n : ℕ) {z : ℂ}
    (hzre : |z.re| = exercise25SquareRadius n) :
    ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.cosh (Real.pi * z.im) := by
  obtain ⟨_, hsin_sq⟩ := exercise25_half_integer_trig_of_abs_eq_squareRadius n hzre
  have hzmul :
      ((Real.pi : ℂ) * z) = (Real.pi * z.re : ℂ) + (Real.pi * z.im) * Complex.I := by
    -- Normalize `π z` to the scalar form `x + t I` expected by Exercise 14.
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, mul_comm]
  -- Compare nonnegative squares after rewriting the denominator to the `x + t I` surface.
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.cosh_pos _).le]
  have hsq :
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ ^ 2 =
        Real.sin (Real.pi * z.re) ^ 2 + Real.sinh (Real.pi * z.im) ^ 2 := by
    rw [hzmul]
    simpa [Complex.sq_norm] using
      (normSq_sin_add_mul_I (Real.pi * z.re) (Real.pi * z.im))
  have hcosh := Real.cosh_sq (Real.pi * z.im)
  -- The half-integer sine square collapses the norm identity to `cosh^2`.
  nlinarith [hsq, hsin_sq, hcosh]

/-- Helper for Exercise 25: on a horizontal side of `γ_n`, the hyperbolic terms depend only on
the square radius, not on the sign of the imaginary part. -/
lemma exercise25_hyperbolic_of_im_abs_eq_squareRadius (n : ℕ) {y : ℝ}
    (hy : |y| = exercise25SquareRadius n) :
    Real.cosh (Real.pi * y) = Real.cosh (Real.pi * exercise25SquareRadius n) ∧
      |Real.sinh (Real.pi * y)| = Real.sinh (Real.pi * exercise25SquareRadius n) := by
  constructor
  · -- Hyperbolic cosine is even, so `|y| = r` fixes the value on both horizontal sides.
    rcases eq_or_eq_neg_of_abs_eq hy with hy | hy
    · rw [hy]
    · rw [hy, mul_neg, Real.cosh_neg]
  · -- The absolute value of `sinh` only depends on `|π y|`, hence on the radius.
    rw [Real.abs_sinh]
    calc
      Real.sinh |Real.pi * y| = Real.sinh (|Real.pi| * |y|) := by rw [abs_mul]
      _ = Real.sinh (Real.pi * exercise25SquareRadius n) := by
        rw [abs_of_pos Real.pi_pos, hy]

/-- Helper for Exercise 25: on the vertical sides of `γ_n`, the cotangent kernel is bounded by
`π`. -/
lemma exercise25_piCot_norm_le_pi_of_re_abs_eq_radius (n : ℕ) {z : ℂ}
    (hzre : |z.re| = exercise25SquareRadius n) :
    ‖exercise25PiCot z‖ ≤ Real.pi := by
  have hzmul :
      ((Real.pi : ℂ) * z) = (Real.pi * z.re : ℂ) + (Real.pi * z.im) * Complex.I := by
    -- Normalize `π z` to the scalar form already controlled by Exercise 14.
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, mul_comm]
  have hnum :
      ‖Complex.cos ((Real.pi : ℂ) * z)‖ ≤ Real.cosh (Real.pi * z.im) := by
    -- Bound the numerator by the generic cosine-on-a-strip estimate.
    rw [hzmul]
    simpa using exercise25_norm_cos_add_mul_I_le_cosh (Real.pi * z.re) (Real.pi * z.im)
  have hden :
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.cosh (Real.pi * z.im) :=
    exercise25_norm_sin_pi_of_re_abs_eq_radius n hzre
  -- Route correction: after the square-geometry reduction, the source proof is a direct
  -- quotient estimate using the exact half-integer denominator.
  calc
    ‖exercise25PiCot z‖
      = Real.pi * (‖Complex.cos ((Real.pi : ℂ) * z)‖ / ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by
          rw [exercise25PiCot, Complex.cot, norm_mul, norm_div]
          simp [Real.pi_pos.le, mul_comm]
    _ ≤ Real.pi * (Real.cosh (Real.pi * z.im) / ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum (norm_nonneg _)) Real.pi_pos.le
    _ = Real.pi * (Real.cosh (Real.pi * z.im) / Real.cosh (Real.pi * z.im)) := by rw [hden]
    _ = Real.pi := by
          rw [div_self (by positivity : Real.cosh (Real.pi * z.im) ≠ 0)]
          ring

/-- Helper for Exercise 25: on the horizontal sides of `γ_n`, the cotangent kernel is bounded by
an explicit constant independent of `n`. -/
lemma exercise25_piCot_norm_le_horizontal_constant_of_im_abs_eq_radius (n : ℕ) {z : ℂ}
    (hzim : |z.im| = exercise25SquareRadius n) :
    ‖exercise25PiCot z‖ ≤ (Real.pi : ℝ) * (2 / (1 - Real.exp (-Real.pi))) := by
  have hzmul :
      ((Real.pi : ℂ) * z) = (Real.pi * z.re : ℂ) + (Real.pi * z.im) * Complex.I := by
    -- Normalize `π z` to the `x + t I` form used by the strip estimates.
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, mul_comm]
  have hnum :
      ‖Complex.cos ((Real.pi : ℂ) * z)‖ ≤ Real.cosh (Real.pi * z.im) := by
    -- The numerator estimate is the same generic cosine bound as on the vertical sides.
    rw [hzmul]
    simpa using exercise25_norm_cos_add_mul_I_le_cosh (Real.pi * z.re) (Real.pi * z.im)
  have hden :
      |Real.sinh (Real.pi * z.im)| ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
    -- The denominator dominates the hyperbolic sine term on every horizontal line.
    rw [hzmul]
    simpa using exercise25_abs_sinh_le_norm_sin_add_mul_I (Real.pi * z.re) (Real.pi * z.im)
  obtain ⟨hcosh_fixed, hsinh_fixed⟩ :=
    exercise25_hyperbolic_of_im_abs_eq_squareRadius n hzim
  have hsinh_pos : 0 < Real.sinh (Real.pi * exercise25SquareRadius n) := by
    -- The half-integer radius lies in the positive half-plane, so its `sinh` is positive.
    simpa [exercise25SquareRadius, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
      sinh_pi_nat_add_half_pos n
  have hinv :
      ‖Complex.sin ((Real.pi : ℂ) * z)‖⁻¹ ≤ (|Real.sinh (Real.pi * z.im)|)⁻¹ := by
    -- Larger positive denominators give smaller reciprocals.
    have hpos : 0 < |Real.sinh (Real.pi * z.im)| := by
      rw [hsinh_fixed]
      exact hsinh_pos
    simpa [one_div] using one_div_le_one_div_of_le hpos hden
  have hquot :
      Real.cosh (Real.pi * z.im) / ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤
        Real.cosh (Real.pi * z.im) / |Real.sinh (Real.pi * z.im)| := by
    -- Convert the denominator lower bound into a quotient upper bound.
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hinv (Real.cosh_pos _).le
  have hu : Real.pi / 2 ≤ Real.pi * exercise25SquareRadius n := by
    -- The square radius is `n + 1/2`, so `π r` is at least `π / 2`.
    dsimp [exercise25SquareRadius]
    nlinarith [Real.pi_pos]
  -- Route correction: the horizontal estimate is the source quotient argument
  -- `‖cos‖ ≤ cosh`, `|sinh| ≤ ‖sin‖`, then the uniform hyperbolic bound.
  calc
    ‖exercise25PiCot z‖
      = Real.pi * (‖Complex.cos ((Real.pi : ℂ) * z)‖ / ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by
          rw [exercise25PiCot, Complex.cot, norm_mul, norm_div]
          simp [Real.pi_pos.le, mul_comm]
    _ ≤ Real.pi * (Real.cosh (Real.pi * z.im) / ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum (norm_nonneg _)) Real.pi_pos.le
    _ ≤ Real.pi * (Real.cosh (Real.pi * z.im) / |Real.sinh (Real.pi * z.im)|) := by
          exact mul_le_mul_of_nonneg_left hquot Real.pi_pos.le
    _ = Real.pi * (Real.cosh (Real.pi * exercise25SquareRadius n) /
          Real.sinh (Real.pi * exercise25SquareRadius n)) := by
          rw [hcosh_fixed, hsinh_fixed]
    _ ≤ (Real.pi : ℝ) * (2 / (1 - Real.exp (-Real.pi))) := by
          exact mul_le_mul_of_nonneg_left
            (exercise25_cosh_div_sinh_le_uniform hu) Real.pi_pos.le
