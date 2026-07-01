import Mathlib
import cartan.II.section05.«0010_Proposition_4_1»
import cartan.I.section04.«0029_Exercise_14»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was checked directly against mathlib's cotangent/meromorphic owners, the
-- local rectangle-boundary contour owner `axisParallelRectangleBoundaryPath`, and the chapter's
-- residue API centered on `meromorphicTrailingCoeffAt`.

noncomputable section

open Filter Bornology
open scoped Topology unitInterval

/-- The kernel `z ↦ π cot (π z)` used in the residue summation formulas. -/
def exercise25PiCot (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)

/-- Helper for Exercise 25: `π cot (π z)` is the logarithmic derivative of `sin (π z)`. -/
lemma exercise25_piCot_as_logDeriv_sinPi :
    exercise25PiCot = fun z ↦ logDeriv (fun w : ℂ ↦ Complex.sin ((Real.pi : ℂ) * w)) z := by
  funext z
  -- Rewrite the composed logarithmic derivative using the chain rule for `logDeriv`.
  change exercise25PiCot z =
    logDeriv (Complex.sin ∘ fun w : ℂ ↦ (Real.pi : ℂ) * w) z
  rw [logDeriv_comp Complex.differentiableAt_sin]
  · rw [Complex.logDeriv_sin]
    -- The derivative of `w ↦ π w` is `π`, so the formula matches the kernel definition.
    simp [exercise25PiCot, mul_comm]
  · fun_prop

/-- Helper for Exercise 25: multiplying `π cot (π z)` by `z - n` removes the pole at the integer
`n`, and the resulting punctured-neighborhood limit is `1`. -/
lemma exercise25_tendsto_sub_integer_mul_piCot (n : ℤ) :
    Tendsto (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (𝓝[≠] (n : ℂ)) (𝓝 1) := by
  let sinPi : ℂ → ℂ := fun z ↦ Complex.sin ((Real.pi : ℂ) * z)
  have hsinPi_an : AnalyticAt ℂ sinPi (n : ℂ) := by
    -- The sine composition is entire, hence analytic at every integer.
    fun_prop
  have hsinPi_zero : sinPi (n : ℂ) = 0 := by
    -- Integer multiples of `π` are zeros of the sine function.
    change Complex.sin ((Real.pi : ℂ) * (n : ℂ)) = 0
    rw [mul_comm]
    simpa using Complex.sin_int_mul_pi n
  have hcos_ne : Complex.cos ((Real.pi : ℂ) * (n : ℂ)) ≠ 0 := by
    intro hcos
    have hsin : Complex.sin ((Real.pi : ℂ) * (n : ℂ)) = 0 := hsinPi_zero
    rw [Complex.cos_eq_zero_iff_sin_eq] at hcos
    rcases hcos with hcos | hcos <;> simp [hsin] at hcos
  have hsinPi_deriv_ne : deriv sinPi (n : ℂ) ≠ 0 := by
    have hderiv :
        deriv sinPi (n : ℂ) = (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * (n : ℂ)) := by
      -- Differentiate `sin (π z)` by a single chain-rule step.
      change
        deriv (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z)) (n : ℂ) =
          (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * (n : ℂ))
      calc
        deriv (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z)) (n : ℂ)
            = Complex.cos ((Real.pi : ℂ) * (n : ℂ)) * ((Real.pi : ℂ) * 1) := by
                exact
                  ((Complex.hasDerivAt_sin ((Real.pi : ℂ) * (n : ℂ))).comp (n : ℂ)
                    ((hasDerivAt_id (n : ℂ)).const_mul (Real.pi : ℂ))).deriv
        _ = (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * (n : ℂ)) := by
              ring
    rw [hderiv]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hcos_ne
  have hlimit :=
      hsinPi_an.tendsto_mul_logDeriv_simple_zero hsinPi_zero hsinPi_deriv_ne
  -- Replace the logarithmic derivative with the kernel from this exercise.
  simpa [sinPi, exercise25_piCot_as_logDeriv_sinPi] using hlimit

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

/-- Exercise 25 (1): the kernel `z ↦ π cot (π z)` is meromorphic on the whole complex plane. -/
theorem exercise25_piCot_meromorphic :
    Meromorphic exercise25PiCot := by
  -- Rewrite the kernel as a logarithmic derivative of an entire sine composition.
  rw [exercise25_piCot_as_logDeriv_sinPi]
  let hsinPi : Meromorphic (fun w : ℂ ↦ Complex.sin ((Real.pi : ℂ) * w)) := by
    intro z
    fun_prop
  simpa using hsinPi.logDeriv

/-- Exercise 25 (2): for every integer `n`, the function `z ↦ π cot (π z)` has a simple pole at
`z = n`. -/
theorem exercise25_piCot_simple_pole_at_integer (n : ℤ) :
    meromorphicOrderAt exercise25PiCot (n : ℂ) = (-1 : WithTop ℤ) := by
  have hmer : MeromorphicAt exercise25PiCot (n : ℂ) := exercise25_piCot_meromorphic (n : ℂ)
  have hsub_mer : MeromorphicAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) := by
    fun_prop
  have hprod_mer : MeromorphicAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) :=
    hsub_mer.mul hmer
  have hprod_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 0 := by
    -- The pole is removable after multiplication, and the resulting limit is the nonzero value `1`.
    exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod_mer).1
      ⟨1, one_ne_zero, exercise25_tendsto_sub_integer_mul_piCot n⟩
  have hmul_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) =
        meromorphicOrderAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) +
          meromorphicOrderAt exercise25PiCot (n : ℂ) :=
    meromorphicOrderAt_mul hsub_mer hmer
  rw [hmul_order] at hprod_order
  -- Subtract the known order of `z - n` to isolate the order of the cotangent kernel.
  have hsum_zero : meromorphicOrderAt exercise25PiCot (n : ℂ) + (1 : WithTop ℤ) = 0 := by
    simpa [add_comm] using hprod_order
  have hsub := congrArg (fun t : WithTop ℤ ↦ t - (1 : WithTop ℤ)) hsum_zero
  simpa [sub_eq_add_neg, add_assoc] using hsub


/-- Exercise 25 (3): for every integer `n`, the residue of `z ↦ π cot (π z)` at `z = n` is `1`. -/
theorem exercise25_piCot_meromorphicTrailingCoeffAt_integer (n : ℤ) :
    meromorphicTrailingCoeffAt exercise25PiCot (n : ℂ) = 1 := by
  have hmer : MeromorphicAt exercise25PiCot (n : ℂ) := exercise25_piCot_meromorphic (n : ℂ)
  have hsub_mer : MeromorphicAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) := by
    fun_prop
  have hprod_mer : MeromorphicAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) :=
    hsub_mer.mul hmer
  have hprod_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 0 := by
    -- The product has a nonzero punctured-neighborhood limit, so it has order zero.
    exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod_mer).1
      ⟨1, one_ne_zero, exercise25_tendsto_sub_integer_mul_piCot n⟩
  have hprod_coeff_tendsto := hprod_mer.tendsto_nhds_meromorphicTrailingCoeffAt
  have hprod_coeff_tendsto' :
      Tendsto (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (𝓝[≠] (n : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt
          (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ))) := by
    -- For an order-zero product, the trailing-coefficient limit is the product itself.
    simpa [hprod_order, Pi.smul_apply, Pi.pow_apply, smul_eq_mul] using hprod_coeff_tendsto
  have hprod_coeff :
      meromorphicTrailingCoeffAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 1 :=
    tendsto_nhds_unique hprod_coeff_tendsto' (exercise25_tendsto_sub_integer_mul_piCot n)
  have hprod_coeff' :
      meromorphicTrailingCoeffAt ((fun z : ℂ ↦ z - (n : ℂ)) * exercise25PiCot) (n : ℂ) = 1 := by
    simpa using hprod_coeff
  have hmul_coeff := hsub_mer.meromorphicTrailingCoeffAt_mul hmer
  -- Divide out the known trailing coefficient of `z - n`, which is `1`.
  rw [meromorphicTrailingCoeffAt_id_sub_const, hprod_coeff'] at hmul_coeff
  simpa using hmul_coeff.symm

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

/-- Exercise 25 (4): there is a constant `M1 > 0`, independent of `n`, such that
`|π cot (π z)| ≤ M1` on the square contour `γ_n`. -/
theorem exercise25_piCot_norm_bounded_on_square_boundaries :
    ∃ M1 : ℝ, 0 < M1 ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary n),
        ‖exercise25PiCot z‖ ≤ M1 := by
  let M1 : ℝ :=
    max Real.pi ((Real.pi : ℝ) * (2 / (1 - Real.exp (-Real.pi))))
  refine ⟨M1, ?_, ?_⟩
  · -- The constant is positive because it dominates `π`.
    exact lt_of_lt_of_le Real.pi_pos (le_max_left _ _)
  · intro n z hz
    rcases exercise25_square_boundary_geometry n hz with ⟨_, _, hside, _⟩
    rcases hside with hzre | hzim
    · -- On a vertical side, use the vertical cotangent bound.
      exact (exercise25_piCot_norm_le_pi_of_re_abs_eq_radius n hzre).trans (le_max_left _ _)
    · -- On a horizontal side, use the horizontal cotangent bound.
      exact
        (exercise25_piCot_norm_le_horizontal_constant_of_im_abs_eq_radius n hzim).trans
          (le_max_right _ _)

/-- Helper for Exercise 25: the degree-gap hypothesis already forces the denominator polynomial to
be nonzero. -/
lemma exercise25_denominator_ne_zero_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    Q ≠ 0 := by
  -- If `Q = 0`, then its nat-degree is `0`, contradicting `P.natDegree + 2 ≤ Q.natDegree`.
  intro hQ
  subst hQ
  simp at hdeg

/-- Helper for Exercise 25: after multiplying the numerator by `X^2`, the corrected numerator
still has nat-degree at most the denominator nat-degree. -/
lemma exercise25_numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (P * Polynomial.X ^ 2).natDegree ≤ Q.natDegree := by
  by_cases hP : P = 0
  · -- The zero numerator stays zero after the correction, so the degree bound is trivial.
    subst hP
    simp
  · -- Otherwise `natDegree_mul_X_pow` turns the claim into the original arithmetic degree gap.
    simpa [Polynomial.natDegree_mul_X_pow (n := 2) hP] using hdeg

/-- Helper for Exercise 25: the corrected numerator `(P * X^2).eval` is `O(Q.eval)` at the
cobounded filter, which is the algebraic form of bounding `z^2 * P(z) / Q(z)` near infinity. -/
lemma exercise25_numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (fun z ↦ (P * Polynomial.X ^ 2).eval z) =O[cobounded ℂ] Q.eval := by
  by_cases hP : P = 0
  · -- The zero corrected numerator is bounded by every comparison function.
    simpa [hP] using Asymptotics.isBigO_zero Q.eval (cobounded ℂ)
  · -- Convert the nat-degree comparison into the degree inequality required by polynomial Big-O.
    have hQ : Q ≠ 0 := exercise25_denominator_ne_zero_of_degree_gap_two P Q hdeg
    have hdeg' : (P * Polynomial.X ^ 2).degree ≤ Q.degree := by
      rw [Polynomial.degree_eq_natDegree (mul_ne_zero hP (pow_ne_zero 2 Polynomial.X_ne_zero)),
        Polynomial.degree_eq_natDegree hQ]
      exact_mod_cast
        exercise25_numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two P Q hdeg
    simpa using
      (Polynomial.isBigO_cobounded_of_degree_le
        (P := P * Polynomial.X ^ 2) (Q := Q) hdeg')

/-- Helper for Exercise 25: a norm inequality `‖a‖ ≤ K ‖b‖` turns into a bound on `‖a / b‖`. -/
lemma exercise25_norm_div_le_of_norm_le_mul {a b : ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hab : ‖a‖ ≤ K * ‖b‖) :
    ‖a / b‖ ≤ K := by
  by_cases hb : b = 0
  · -- If the denominator vanishes, then complex division is zero and the claim reduces to `0 ≤ K`.
    subst hb
    simpa using hK
  · -- Otherwise divide the norm inequality by the positive factor `‖b‖`.
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hb)).2 <| by simpa [mul_comm] using hab

/-- Helper for Exercise 25: the corrected rational function `z^2 * P(z) / Q(z)` is uniformly
bounded outside a sufficiently large disk when `deg Q ≥ deg P + 2`. -/
lemma exercise25_rational_mul_sq_eventually_bounded
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖(z ^ 2 : ℂ) * (P.eval z / Q.eval z)‖ ≤ K := by
  obtain ⟨K, hKpos, hKbound⟩ :=
    Asymptotics.isBigO_iff'.mp
      (exercise25_numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two P Q hdeg)
  have hbounded :
      ∀ᶠ z in cobounded ℂ, ‖(z ^ 2 : ℂ) * (P.eval z / Q.eval z)‖ ≤ K := by
    -- Route correction: bound the source-corrected object `z^2 * P(z) / Q(z)` directly.
    filter_upwards [hKbound] with z hz
    have hquot :
        ‖((P * Polynomial.X ^ 2).eval z) / Q.eval z‖ ≤ K :=
      exercise25_norm_div_le_of_norm_le_mul hKpos.le hz
    have hnorm :
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) ≤ K := by
      calc
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖)
            = ‖P.eval z‖ * ‖z‖ ^ (2 : ℕ) / ‖Q.eval z‖ := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ac_rfl
        _ ≤ K := by
              simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
                norm_div, norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using hquot
    calc
      ‖(z ^ 2 : ℂ) * (P.eval z / Q.eval z)‖
          = ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) := by
              rw [norm_mul, norm_div, norm_pow]
      _ ≤ K := hnorm
  rcases Filter.hasBasis_cobounded_norm.eventually_iff.mp hbounded with ⟨R₀, -, hR₀⟩
  refine ⟨K, max R₀ 1, ?_, ?_⟩
  · -- Keep the eventual radius positive without changing the bounded region.
    refine lt_min hKpos ?_
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro z hz
    -- Any point outside the larger radius is in the original eventual region as well.
    exact hR₀ <| by
      simpa using (le_trans (le_max_left _ _) hz)

/-- Helper for Exercise 25: a bound on `‖z^2 w‖` converts to the decay estimate `‖w‖ ≤ K / ‖z‖^2`
once `z` stays away from `0`. -/
lemma exercise25_decay_of_mul_sq_bound {R K : ℝ} {z w : ℂ}
    (hR : 0 < R) (hz : R ≤ ‖z‖) (hbound : ‖(z ^ 2 : ℂ) * w‖ ≤ K) :
    ‖w‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR hz
  have hzsqpos : 0 < ‖z‖ ^ (2 : ℕ) := by positivity
  -- Rewrite the corrected norm as `‖w‖ * ‖z‖^2` and divide by the positive square norm.
  refine (le_div_iff₀ hzsqpos).2 ?_
  calc
    ‖w‖ * ‖z‖ ^ (2 : ℕ) = ‖(z ^ 2 : ℂ) * w‖ := by
      rw [norm_mul, norm_pow, mul_comm]
    _ ≤ K := hbound

/-- Exercise 25 (5): if `deg Q ≥ deg P + 2`, then the rational function `P / Q` satisfies the
bound `|P(z) / Q(z)| ≤ K / |z|^2` for all sufficiently large `|z|`. -/
theorem exercise25_rational_decay_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖P.eval z / Q.eval z‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  obtain ⟨K, R, hKR, hbounded⟩ := exercise25_rational_mul_sq_eventually_bounded P Q hdeg
  refine ⟨K, R, hKR, ?_⟩
  intro z hz
  have hR : 0 < R := (lt_min_iff.mp hKR).2
  -- Route correction: first bound `z^2 * P(z) / Q(z)` near infinity, then divide by `‖z‖^2`.
  exact exercise25_decay_of_mul_sq_bound hR hz (hbounded z hz)

/-- The square boundaries `γ_n` eventually avoid any fixed finite subset of `ℂ`; equivalently,
after discarding finitely many initial contours, every later `γ_n` is disjoint from that set. -/
theorem exercise25_squareBoundary_eventually_disjoint (s : Finset ℂ) :
    ∃ N : ℕ, ∀ n : ℕ,
      Disjoint (Set.range (exercise25SquareBoundary (n + N))) (s : Set ℂ) := by
  classical
  let B : ℝ := ∑ w ∈ s, ‖w‖
  let N : ℕ := Nat.ceil B
  refine ⟨N, fun n => Set.disjoint_left.mpr ?_⟩
  intro z hzboundary hzs
  have hzmem : z ∈ s := by
    simpa using hzs
  have hnorm_le_B : ‖z‖ ≤ B := by
    -- A single nonnegative summand is bounded by the whole finite sum of norms.
    simpa [B] using
      (Finset.single_le_sum (f := fun w : ℂ ↦ ‖w‖) (fun w _ ↦ norm_nonneg _) hzmem :
        ‖z‖ ≤ ∑ w ∈ s, ‖w‖)
  have hradius_le_norm :
      exercise25SquareRadius (n + N) ≤ ‖z‖ :=
    (exercise25_square_boundary_geometry (n + N) hzboundary).2.2.2
  have hB_le_N : B ≤ N := Nat.le_ceil B
  have hN_lt_radius : (N : ℝ) < exercise25SquareRadius (n + N) := by
    -- Every later square has radius strictly larger than the chosen ceiling bound.
    have hN_le_nat : N ≤ n + N := by
      exact Nat.le_add_left N n
    have hN_le_real : (N : ℝ) ≤ (n + N : ℕ) := by
      exact_mod_cast hN_le_nat
    dsimp [exercise25SquareRadius]
    linarith
  have hnorm_lt_radius : ‖z‖ < exercise25SquareRadius (n + N) := by
    exact lt_of_le_of_lt (hnorm_le_B.trans hB_le_N) hN_lt_radius
  exact (not_lt_of_ge hradius_le_norm) hnorm_lt_radius

/-- Helper for Exercise 25: the extension of an affine segment is `C¹` on the unit interval. -/
lemma exercise25_segment_contDiffOn (a b : ℂ) :
    ContDiffOn ℝ 1 (Path.segment a b).extend I := by
  -- The segment extension agrees with the affine line map on the unit interval.
  have hline : ContDiffOn ℝ 1 (ContinuousAffineMap.lineMap (R := ℝ) a b) I :=
    (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) a b)).contDiffOn
  refine hline.congr ?_
  intro t ht
  simpa using Path.eqOn_extend_segment a b ht

/-- Helper for Exercise 25: the square contour never meets a zero of `sin (π z)` because one of
its coordinates is a half-integer side value. -/
lemma exercise25_sin_pi_ne_zero_on_square_boundary (n : ℕ) {z : ℂ}
    (hz : z ∈ Set.range (exercise25SquareBoundary n)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  rcases exercise25_square_boundary_geometry n hz with ⟨_, _, hside, _⟩
  rcases hside with hzre | hzim
  · -- On a vertical side the denominator norm is the positive hyperbolic cosine.
    have hnorm :
        ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.cosh (Real.pi * z.im) :=
      exercise25_norm_sin_pi_of_re_abs_eq_radius n hzre
    intro hzero
    have hpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      rw [hnorm]
      positivity
    simpa [hzero] using hpos.ne'
  · -- On a horizontal side the denominator dominates the positive `sinh (π r_n)` term.
    have hzmul :
        ((Real.pi : ℂ) * z) = (Real.pi * z.re : ℂ) + (Real.pi * z.im) * Complex.I := by
      -- Normalize `π z` to the `x + t I` surface used by the strip estimates.
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, mul_comm]
    obtain ⟨_, hsinh_fixed⟩ := exercise25_hyperbolic_of_im_abs_eq_squareRadius n hzim
    have hsinh_pos : 0 < Real.sinh (Real.pi * exercise25SquareRadius n) := by
      simpa [exercise25SquareRadius, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
        sinh_pi_nat_add_half_pos n
    have hlower :
        Real.sinh (Real.pi * exercise25SquareRadius n) ≤
          ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      calc
        Real.sinh (Real.pi * exercise25SquareRadius n)
            = |Real.sinh (Real.pi * z.im)| := by rw [hsinh_fixed]
        _ ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
              rw [hzmul]
              simpa using
                exercise25_abs_sinh_le_norm_sin_add_mul_I (Real.pi * z.re) (Real.pi * z.im)
    intro hzero
    have hpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := lt_of_lt_of_le hsinh_pos hlower
    simpa [hzero] using hpos.ne'

/-- Helper for Exercise 25: after discarding finitely many initial square contours, the
denominator polynomial is nonzero on every later square boundary. -/
lemma exercise25_square_boundary_denominator_nonzero_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ NQ : ℕ, ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary (n + NQ)), Q.eval z ≠ 0 := by
  classical
  have hQ : Q ≠ 0 := exercise25_denominator_ne_zero_of_degree_gap_two P Q hdeg
  obtain ⟨NQ, hdisj⟩ := exercise25_squareBoundary_eventually_disjoint (Q.roots.toFinset)
  refine ⟨NQ, ?_⟩
  intro n z hz
  have hznot : z ∉ (Q.roots.toFinset : Set ℂ) :=
    Set.disjoint_left.mp (hdisj n) hz
  intro hzero
  have hzroot : z ∈ Q.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact hzero
  exact hznot hzroot

/-- Helper for Exercise 25: each affine side segment of the square contour `γ_n` lies in the
range of the full boundary path. -/
lemma exercise25_square_boundary_side_ranges_subset (n : ℕ) :
    let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
    let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    Set.range (Path.segment z₀ zw) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment zw w) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment w wz) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment wz z₀) ⊆ Set.range (exercise25SquareBoundary n) := by
  let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
  let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The bottom segment is the first side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inl hz
  · -- The right segment is the second side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inl hz
  · -- The top segment is the third side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inl hz
  · -- The left segment is the final side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inr hz

/-- Helper for Exercise 25: once the boundary avoids the zeros of `Q`, the kernel
`(P / Q) π cot (π z)` is a continuous scalar field on the contour image and therefore yields a
curve-integrable scalar `1`-form on each affine side of the square contour. -/
lemma exercise25_square_boundary_integrand_sides_curve_integrable_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
          exercise25SquareRadius (n + N) * Complex.I
        let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
          exercise25SquareRadius (n + N) * Complex.I
        let zw : ℂ := Complex.mk w.re z₀.im
        let wz : ℂ := Complex.mk z₀.re w.im
        CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment z₀ zw) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment zw w) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment w wz) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment wz z₀) := by
  obtain ⟨NQ, hQnz⟩ := exercise25_square_boundary_denominator_nonzero_eventually P Q hdeg
  refine ⟨NQ, ?_⟩
  intro n
  let D : Set ℂ := Set.range (exercise25SquareBoundary (n + NQ))
  let z₀ : ℂ := -(exercise25SquareRadius (n + NQ) : ℂ) -
    exercise25SquareRadius (n + NQ) * Complex.I
  let w : ℂ := (exercise25SquareRadius (n + NQ) : ℂ) +
    exercise25SquareRadius (n + NQ) * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  have hrat :
      ContinuousOn (fun z ↦ P.eval z / Q.eval z) D := by
    -- The rational factor is continuous on the boundary once `Q` has no zeros there.
    refine ContinuousOn.div P.continuous.continuousOn
      Q.continuous.continuousOn ?_
    intro z hz
    exact hQnz n z hz
  have hcot :
      ContinuousOn exercise25PiCot D := by
    have hcos :
        ContinuousOn (fun z : ℂ ↦ Complex.cos ((Real.pi : ℂ) * z)) D := by
      simpa using
        (Complex.continuous_cos.comp ((continuous_const : Continuous fun _ : ℂ ↦ (Real.pi : ℂ)).mul
          continuous_id)).continuousOn
    have hsin :
        ContinuousOn (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z)) D := by
      simpa using
        (Complex.continuous_sin.comp ((continuous_const : Continuous fun _ : ℂ ↦ (Real.pi : ℂ)).mul
          continuous_id)).continuousOn
    have hquot :
        ContinuousOn
          (fun z : ℂ ↦
            Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) D := by
      -- Rewrite `cot` as `cos / sin`, and use the boundary nonvanishing of `sin (π z)`.
      refine ContinuousOn.div hcos hsin ?_
      intro z hz
      exact exercise25_sin_pi_ne_zero_on_square_boundary (n + NQ) hz
    -- Multiplying by the constant factor `π` recovers `exercise25PiCot`.
    simpa [exercise25PiCot, Complex.cot, mul_assoc] using
      (continuousOn_const.mul hquot)
  have hcoeff :
      ContinuousOn (fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) D := by
    -- The full scalar coefficient is the product of the rational factor and the cotangent kernel.
    exact hrat.mul hcot
  have hform :
      ContinuousOn
        (fun z ↦ (((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z)) D := by
    -- Package the scalar coefficient as a continuous complex-linear `1`-form.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
  have hsubsets := exercise25_square_boundary_side_ranges_subset (n + NQ)
  dsimp [z₀, w, zw, wz] at hsubsets
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment z₀ zw) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
      (fun t ↦ hbottom_subset ⟨t, rfl⟩)
  have hright_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment zw w) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
      (fun t ↦ hright_subset ⟨t, rfl⟩)
  have htop_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment w wz) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
      (fun t ↦ htop_subset ⟨t, rfl⟩)
  have hleft_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment wz z₀) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
      (fun t ↦ hleft_subset ⟨t, rfl⟩)
  -- Record the four side integrability statements explicitly for the later ML estimate.
  simpa [z₀, w, zw, wz] using
    ⟨hbottom_int, hright_int, htop_int, hleft_int⟩

/-- Helper for Exercise 25: a `C / r_n^2` bound on the whole square boundary gives the source ML
estimate `2 C / r_n` on any single affine side of `γ_n`. -/
lemma exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
    {φ : ℂ → ℂ} (n : ℕ) {C : ℝ} {a b : ℂ}
    (hsubset : Set.range (Path.segment a b) ⊆ Set.range (exercise25SquareBoundary n))
    (hlength : ‖b - a‖ = 2 * exercise25SquareRadius n)
    (hbound : ∀ z ∈ Set.range (exercise25SquareBoundary n),
      ‖φ z‖ ≤ C / exercise25SquareRadius n ^ (2 : ℕ)) :
    ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖ ≤
      2 * C / exercise25SquareRadius n := by
  let r : ℝ := exercise25SquareRadius n
  have hr_pos : 0 < r := by
    -- Every square radius is `n + 1 / 2`, hence strictly positive.
    dsimp [r, exercise25SquareRadius]
    positivity
  have hsegment :
      ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖ ≤
        (C / r ^ (2 : ℕ)) * ‖b - a‖ := by
    -- Transport the boundary bound to the segment image and invoke the segment ML estimate.
    refine norm_curveIntegral_segment_le ?_
    intro z hz
    have hz' : z ∈ Set.range (Path.segment a b) := by
      simpa [Path.range_segment] using hz
    simpa [Complex.scalarOneForm] using hbound z (hsubset hz')
  calc
    ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖
        ≤ (C / r ^ (2 : ℕ)) * ‖b - a‖ := hsegment
    _ = (C / r ^ (2 : ℕ)) * (2 * exercise25SquareRadius n) := by rw [hlength]
    _ = (C / r ^ (2 : ℕ)) * (2 * r) := by simp [r]
    _ = 2 * C / r := by field_simp [r, hr_pos.ne']

/-- Helper for Exercise 25: once the boundary avoids the zeros of `Q`, the kernel
`(P / Q) π cot (π z)` is a continuous scalar field on the contour image and therefore yields a
curve-integrable scalar `1`-form there. -/
lemma exercise25_square_boundary_integrand_curve_integrable_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
          (exercise25SquareBoundary (n + N)) := by
  obtain ⟨N, hsides⟩ :=
    exercise25_square_boundary_integrand_sides_curve_integrable_eventually P Q hdeg
  refine ⟨N, ?_⟩
  intro n
  let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
    exercise25SquareRadius (n + N) * Complex.I
  let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
    exercise25SquareRadius (n + N) * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  rcases hsides n with ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
  -- Glue the four affine sides back into the square contour.
  simpa [exercise25SquareBoundary, z₀, w, zw, wz, axisParallelRectangleBoundaryPath] using
    (CurveIntegrable.trans hbottom_int
      (CurveIntegrable.trans hright_int
        (CurveIntegrable.trans htop_int hleft_int)))

/-- Helper for Exercise 25: a uniform `C / r_n^2` bound on the scalar coefficient along the square
boundary gives the source ML estimate `‖∮_{γ_n} φ(z) dz‖ ≤ 8 C / r_n`. -/
lemma exercise25_square_boundary_norm_curveIntegral_le
    {φ : ℂ → ℂ} (n : ℕ) {C : ℝ}
    (hsides :
      let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
      let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
      let zw : ℂ := Complex.mk w.re z₀.im
      let wz : ℂ := Complex.mk z₀.re w.im
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀))
    (hbound : ∀ z ∈ Set.range (exercise25SquareBoundary n),
      ‖φ z‖ ≤ C / exercise25SquareRadius n ^ (2 : ℕ)) :
    ‖∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ φ z) dz) z‖ ≤
      8 * C / exercise25SquareRadius n := by
  let r : ℝ := exercise25SquareRadius n
  let z₀ : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  have hz₀ : z₀ = -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I := by
    rfl
  have hw : w = (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I := by
    rfl
  have hzw : zw = (exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I := by
    -- The intermediate lower-right corner has the expected square coordinates.
    apply Complex.ext <;> simp [zw, z₀, w, r]
  have hwz : wz = -(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I := by
    -- The intermediate upper-left corner has the expected square coordinates.
    apply Complex.ext <;> simp [wz, z₀, w, r]
  have hr_nonneg : 0 ≤ exercise25SquareRadius n := by
    dsimp [exercise25SquareRadius]
    positivity
  have htwo_r_nonneg : 0 ≤ 2 * exercise25SquareRadius n := by
    positivity
  have hsides' :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) := by
    simpa [z₀, w, zw, wz, r] using hsides
  rcases hsides' with ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
  have hsubsets :
      Set.range (Path.segment z₀ zw) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment zw w) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment w wz) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment wz z₀) ⊆ Set.range (exercise25SquareBoundary n) := by
    simpa [z₀, w, zw, wz, r] using exercise25_square_boundary_side_ranges_subset n
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_length :
      ‖zw - z₀‖ =
        2 * exercise25SquareRadius n := by
    -- The bottom side is horizontal with Euclidean length `2 r_n`.
    calc
      ‖zw - z₀‖ = ‖(2 * exercise25SquareRadius n : ℂ)‖ := by
        rw [hzw, hz₀]
        ring_nf
      _ = 2 * exercise25SquareRadius n := by
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hright_length :
      ‖w - zw‖ =
        2 * exercise25SquareRadius n := by
    -- The right side is vertical with Euclidean length `2 r_n`.
    calc
      ‖w - zw‖ = ‖(2 * exercise25SquareRadius n : ℂ) * Complex.I‖ := by
        rw [hzw, hw]
        ring_nf
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
      _ = 2 * exercise25SquareRadius n := by
            rw [Complex.norm_I, mul_one]
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have htop_length :
      ‖wz - w‖ =
        2 * exercise25SquareRadius n := by
    -- The top side is again horizontal with Euclidean length `2 r_n`.
    calc
      ‖wz - w‖ = ‖(-2 * exercise25SquareRadius n : ℂ)‖ := by
        rw [hwz, hw]
        ring_nf
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ := by
            have hneg : (-2 * exercise25SquareRadius n : ℂ) =
                -((2 * exercise25SquareRadius n : ℂ)) := by ring
            rw [hneg, norm_neg]
      _ = 2 * exercise25SquareRadius n := by
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hleft_length :
      ‖z₀ - wz‖ =
        2 * exercise25SquareRadius n := by
    -- The left side is vertical with Euclidean length `2 r_n`.
    calc
      ‖z₀ - wz‖ = ‖(-2 * exercise25SquareRadius n : ℂ) * Complex.I‖ := by
        rw [hwz, hz₀]
        ring_nf
      _ = ‖(-2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by
            have hneg : (-2 * exercise25SquareRadius n : ℂ) =
                -((2 * exercise25SquareRadius n : ℂ)) := by ring
            rw [hneg, norm_neg]
      _ = 2 * exercise25SquareRadius n := by
            rw [Complex.norm_I, mul_one]
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hbottom_le :
      ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := z₀) (b := zw) hbottom_subset hbottom_length hbound
  have hright_le :
      ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := zw) (b := w) hright_subset hright_length hbound
  have htop_le :
      ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := w) (b := wz) htop_subset htop_length hbound
  have hleft_le :
      ‖∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := wz) (b := z₀) hleft_subset hleft_length hbound
  have hboundary_eq :
      exercise25SquareBoundary n =
        (Path.segment z₀ zw).trans
          ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
    rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
  -- Expand the square boundary into its four affine sides before summing the one-side estimates.
  rw [hboundary_eq]
  rw [curveIntegral_trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))]
  rw [curveIntegral_trans hright_int (CurveIntegrable.trans htop_int hleft_int)]
  rw [curveIntegral_trans htop_int hleft_int]
  calc
    ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z +
          (∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
            (∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
              ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z))‖
        ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
              (∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
                ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z)‖ := norm_add_le _ _
    _ ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            (‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ +
              ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
                ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            (‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ +
              (‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z‖ +
                ‖∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖)) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 2 * C / exercise25SquareRadius n +
            (2 * C / exercise25SquareRadius n +
              (2 * C / exercise25SquareRadius n + 2 * C / exercise25SquareRadius n)) := by
          gcongr
    _ = 8 * C / exercise25SquareRadius n := by ring

/-- Helper for Exercise 25: on a common tail of square boundaries, the coefficient
`(P / Q)(z) π cot (π z)` satisfies the source decay estimate `O(r_n^{-2})`. -/
lemma exercise25_square_boundary_integrand_decay
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary (n + N)),
        ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤
          C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by
  obtain ⟨M1, hM1pos, hM1⟩ := exercise25_piCot_norm_bounded_on_square_boundaries
  obtain ⟨K, R, hKR, hdecay⟩ := exercise25_rational_decay_of_degree_gap_two P Q hdeg
  let N : ℕ := Nat.ceil R
  let C : ℝ := K * M1
  refine ⟨C, N, mul_pos (lt_min_iff.mp hKR).1 hM1pos, ?_⟩
  intro n z hz
  let r : ℝ := exercise25SquareRadius (n + N)
  have hr_le_norm : r ≤ ‖z‖ := (exercise25_square_boundary_geometry (n + N) hz).2.2.2
  have hR_le_r : R ≤ r := by
    -- The chosen shift forces every later square radius past the eventual decay threshold `R`.
    have hceil : R ≤ N := Nat.le_ceil R
    have hN_le_real : (N : ℝ) ≤ r := by
      dsimp [r, exercise25SquareRadius]
      have hN_le_nat : N ≤ n + N := Nat.le_add_left N n
      have hN_le_nat' : (N : ℝ) ≤ (n + N : ℕ) := by
        exact_mod_cast hN_le_nat
      linarith
    exact hceil.trans hN_le_real
  have hzR : R ≤ ‖z‖ := hR_le_r.trans hr_le_norm
  have hrat :
      ‖P.eval z / Q.eval z‖ ≤ K / ‖z‖ ^ (2 : ℕ) :=
    hdecay z hzR
  have hkernel :
      ‖exercise25PiCot z‖ ≤ M1 :=
    hM1 (n + N) z hz
  have hcoeff :
      ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤ (K / ‖z‖ ^ (2 : ℕ)) * M1 := by
    -- First multiply the global rational decay bound by the square-boundary cotangent bound.
    have hK_nonneg : 0 ≤ K := (lt_min_iff.mp hKR).1.le
    calc
      ‖P.eval z / Q.eval z * exercise25PiCot z‖
          ≤ ‖P.eval z / Q.eval z‖ * ‖exercise25PiCot z‖ := norm_mul_le _ _
      _ ≤ (K / ‖z‖ ^ (2 : ℕ)) * M1 := by
            exact mul_le_mul hrat hkernel (norm_nonneg _) (by positivity)
  have hrpow_pos : 0 < r ^ (2 : ℕ) := by
    dsimp [r, exercise25SquareRadius]
    positivity
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, exercise25SquareRadius]
    positivity
  have hnormpow_ge : r ^ (2 : ℕ) ≤ ‖z‖ ^ (2 : ℕ) := by
    -- Square the radius bound using monotonicity of `x ↦ x^2` on the nonnegative reals.
    simpa using
      (pow_le_pow_left₀ (a := r) (b := ‖z‖) hr_nonneg hr_le_norm 2)
  have hdiv :
      K / ‖z‖ ^ (2 : ℕ) ≤ K / r ^ (2 : ℕ) := by
    -- Replace `‖z‖` by the smaller square radius in the denominator.
    have hK_nonneg : 0 ≤ K := (lt_min_iff.mp hKR).1.le
    have hinv :
        (‖z‖ ^ (2 : ℕ))⁻¹ ≤ (r ^ (2 : ℕ))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hrpow_pos hnormpow_ge
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv hK_nonneg
  calc
    ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤ (K / ‖z‖ ^ (2 : ℕ)) * M1 := hcoeff
    _ ≤ (K / r ^ (2 : ℕ)) * M1 := by
          exact mul_le_mul_of_nonneg_right hdiv hM1pos.le
    _ = C / r ^ (2 : ℕ) := by
          simp [C, div_eq_mul_inv, mul_assoc, mul_comm]
    _ = C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by rfl

/-- Exercise 25 (6): for a rational function `P / Q` whose poles are exactly the nonintegral
points in the finite set `s`, and with `deg Q ≥ deg P + 2`, there is a tail of square contours
`γ_{n + N}` on which the one-form `((P / Q) π cot (π z)) dz` is genuinely curve-integrable, and
those contour integrals tend to `0`. -/
theorem exercise25_rational_contour_integral_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    ∃ N : ℕ,
      (∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
          (exercise25SquareBoundary (n + N))) ∧
      Tendsto
        (fun n : ℕ ↦
          ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z)
        atTop (𝓝 0) := by
  let _ := hpoles
  let _ := hnonint
  obtain ⟨Ncontour, hcontour⟩ :=
    exercise25_square_boundary_integrand_curve_integrable_eventually P Q hdeg
  obtain ⟨Nsides, hsides⟩ :=
    exercise25_square_boundary_integrand_sides_curve_integrable_eventually P Q hdeg
  obtain ⟨C, Ndecay, hCpos, hdecay⟩ := exercise25_square_boundary_integrand_decay P Q hdeg
  let N : ℕ := max Ncontour (max Nsides Ndecay)
  refine ⟨N, (fun n ↦ ?_), ?_⟩
  · let m : ℕ := n + (N - Ncontour)
    have hNcontour_le : Ncontour ≤ N := by
      -- The common shift `N` dominates the contour-integrability threshold.
      dsimp [N]
      exact le_max_left _ _
    have hidx : m + Ncontour = n + N := by
      dsimp [m]
      omega
    -- Rewrite the eventual contour-integrability tail to the common square `γ_{n + N}`.
    rw [← hidx]
    exact hcontour m
  · have hbound :
        ∀ n : ℕ,
          ‖∫ᶜ z in exercise25SquareBoundary (n + N),
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z‖ ≤
            8 * C / exercise25SquareRadius (n + N) := by
      intro n
      let ms : ℕ := n + (N - Nsides)
      let md : ℕ := n + (N - Ndecay)
      have hNsides_le : Nsides ≤ N := by
        -- The common shift `N` also dominates the side-integrability threshold.
        dsimp [N]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      have hNdecay_le : Ndecay ≤ N := by
        -- Likewise for the decay threshold.
        dsimp [N]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      have hidxs : ms + Nsides = n + N := by
        dsimp [ms]
        omega
      have hidxd : md + Ndecay = n + N := by
        dsimp [md]
        omega
      have hsidesN :
          let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
            exercise25SquareRadius (n + N) * Complex.I
          let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
            exercise25SquareRadius (n + N) * Complex.I
          let zw : ℂ := Complex.mk w.re z₀.im
          let wz : ℂ := Complex.mk z₀.re w.im
          CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment z₀ zw) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment zw w) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment w wz) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment wz z₀) := by
        -- The four side-integrability statements are the same after rewriting the index.
        rw [← hidxs]
        exact hsides ms
      have hdecayN :
          ∀ z ∈ Set.range (exercise25SquareBoundary (n + N)),
            ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤
              C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by
        intro z hz
        -- Transport the pointwise decay estimate to the common contour.
        rw [← hidxd] at hz ⊢
        exact hdecay md z hz
      -- Apply the already proved square-boundary ML estimate at the common shift `n + N`.
      exact exercise25_square_boundary_norm_curveIntegral_le
        (n := n + N) (C := C) hsidesN hdecayN
    have hradius :
        Tendsto (fun n : ℕ ↦ exercise25SquareRadius (n + N)) atTop atTop := by
      -- The square radius grows linearly, so its reciprocal tends to `0`.
      simpa [exercise25SquareRadius, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        (tendsto_atTop_add_const_right atTop ((N : ℝ) + (1 / 2 : ℝ))
          tendsto_natCast_atTop_atTop)
    have htail :
        Tendsto (fun n : ℕ ↦ 8 * C / exercise25SquareRadius (n + N)) atTop (𝓝 0) := by
      have hinv :
          Tendsto (fun n : ℕ ↦ (exercise25SquareRadius (n + N))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hradius
      simpa [div_eq_mul_inv, mul_assoc] using
        (tendsto_const_nhds.mul hinv :
          Tendsto
            (fun n : ℕ ↦ (8 * C) * (exercise25SquareRadius (n + N))⁻¹)
            atTop (𝓝 ((8 * C) * 0)))
    -- Squeeze the contour integrals between their norm bound and the vanishing reciprocal tail.
    exact squeeze_zero_norm hbound htail

/-- Exercise 25 (7): under the same hypotheses as in part (6), the symmetric sums of the values of
`P / Q` at the integers converge to minus the sum of the nonintegral residues weighted by
`π cot (π z)`. -/
theorem exercise25_rational_integer_sum_tendsto
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)))
      atTop
      (𝓝 (-s.sum fun z ↦
        meromorphicTrailingCoeffAt (fun w ↦ P.eval w / Q.eval w) z * exercise25PiCot z)) := sorry

/-- Exercise 25 (8): the symmetric integer-sum formula remains valid under the weaker degree
assumption `deg P < deg Q`. -/
theorem exercise25_rational_integer_sum_tendsto_of_degree_gap_one
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)))
      atTop
      (𝓝 (-s.sum fun z ↦
        meromorphicTrailingCoeffAt (fun w ↦ P.eval w / Q.eval w) z * exercise25PiCot z)) := sorry

/-- Exercise 25 (9): if `-π < α < π`, then there is a constant `M2 > 0`, independent of `n`,
such that `|exp(i α z) / sin(π z)| ≤ M2` on the square contour `γ_n`. -/
theorem exercise25_exp_div_sin_norm_bounded_on_square_boundaries
    (alpha : ℝ) (halpha_left : -Real.pi < alpha) (halpha_right : alpha < Real.pi) :
    ∃ M2 : ℝ, 0 < M2 ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary n),
        ‖Complex.exp (Complex.I * (alpha : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)‖ ≤ M2 := sorry

/-- Exercise 25 (10): if `-π < α < π`, then the weighted symmetric sums
`∑_{-n ≤ p ≤ n} (-1)^p f(p) exp(i α p)` of a rational function `P / Q` with `deg P < deg Q`
converge to the residue sum weighted by `exp(i α z) / sin(π z)`. -/
theorem exercise25_rational_alternating_exponential_sum_tendsto
    (alpha : ℝ) (halpha : -Real.pi < alpha ∧ alpha < Real.pi)
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦
          ((-1 : ℂ) ^ Int.natAbs p) *
            Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) *
              (P.eval (p : ℂ) / Q.eval (p : ℂ))))
      atTop
      (𝓝 (-(Real.pi : ℂ) *
        s.sum fun z ↦
          meromorphicTrailingCoeffAt (fun w ↦ P.eval w / Q.eval w) z *
            Complex.exp (Complex.I * (alpha : ℂ) * z) /
            Complex.sin ((Real.pi : ℂ) * z))) := sorry
