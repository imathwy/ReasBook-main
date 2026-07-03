import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open scoped Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "unitCircle" => Metric.sphere (0 : Plane) 1

/-- The boundary of the square of side length `2` centered at the origin in `ℝ²`. -/
def squareBoundary : Set Plane :=
  { p | max |p 0| |p 1| = 1 }

/-- A point of `ℝ²` lies on the square boundary exactly when the maximum of the absolute values of
its two coordinates is `1`. -/
@[simp] theorem mem_squareBoundary (p : Plane) :
    p ∈ squareBoundary ↔ max |p 0| |p 1| = 1 := Iff.rfl

/-- Helper for Problem 3-5: the `ℓ∞` gauge of a point in `ℝ²`. -/
def squareGauge (p : Plane) : ℝ :=
  max |p 0| |p 1|

/-- Helper for Problem 3-5: the square gauge is nonnegative. -/
theorem squareGauge_nonneg (p : Plane) : 0 ≤ squareGauge p := by
  -- Both absolute values are nonnegative, so their maximum is also nonnegative.
  exact le_trans (abs_nonneg _) (le_max_left _ _)

/-- Helper for Problem 3-5: the square gauge vanishes exactly at the origin. -/
theorem squareGauge_eq_zero_iff (p : Plane) : squareGauge p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    ext i
    fin_cases i
    · have hmax : max |p 0| |p 1| = 0 := hp
      have h0 : |p 0| = 0 := by
        have := le_max_left (|p 0|) (|p 1|)
        rw [hmax] at this
        exact le_antisymm this (abs_nonneg _)
      exact abs_eq_zero.mp h0
    · have hmax : max |p 0| |p 1| = 0 := hp
      have h1 : |p 1| = 0 := by
        have := le_max_right (|p 0|) (|p 1|)
        rw [hmax] at this
        exact le_antisymm this (abs_nonneg _)
      exact abs_eq_zero.mp h1
  · intro hp
    simp [squareGauge, hp]

/-- Helper for Problem 3-5: the square gauge is strictly positive away from the origin. -/
theorem squareGauge_pos {p : Plane} (hp : p ≠ 0) : 0 < squareGauge p := by
  -- The previous characterization reduces strict positivity to ruling out the zero gauge.
  refine lt_of_le_of_ne (squareGauge_nonneg p) ?_
  intro hzero
  exact hp ((squareGauge_eq_zero_iff p).mp hzero.symm)

/-- Helper for Problem 3-5: the square gauge is homogeneous under real scaling. -/
theorem squareGauge_smul (c : ℝ) (p : Plane) : squareGauge (c • p) = |c| * squareGauge p := by
  -- Pull the scalar absolute value through both coordinates and factor it out of the maximum.
  simpa [squareGauge, abs_mul, mul_comm, mul_left_comm, mul_assoc] using
    (max_mul_of_nonneg (|p 0|) (|p 1|) (abs_nonneg c)).symm

/-- Helper for Problem 3-5: each coordinate is bounded by the Euclidean norm. -/
theorem abs_le_norm (p : Plane) (i : Fin 2) : |p i| ≤ ‖p‖ := by
  -- Compare the chosen coordinate square with the full Euclidean norm square.
  fin_cases i
  · rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two]
    have h : (p 0) ^ 2 ≤ (p 0) ^ 2 + (p 1) ^ 2 := by
      nlinarith [sq_nonneg (p 1)]
    simpa using h
  · rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two]
    have h : (p 1) ^ 2 ≤ (p 0) ^ 2 + (p 1) ^ 2 := by
      nlinarith [sq_nonneg (p 0)]
    simpa [add_comm] using h

/-- Helper for Problem 3-5: the square gauge is bounded by the Euclidean norm. -/
theorem squareGauge_le_norm (p : Plane) : squareGauge p ≤ ‖p‖ := by
  -- The maximum of the two coordinate magnitudes is bounded by the norm because each coordinate is.
  exact max_le (abs_le_norm p 0) (abs_le_norm p 1)

/-- Helper for Problem 3-5: the Euclidean norm is bounded by `sqrt 2` times the square gauge. -/
theorem norm_le_sqrt_two_mul_squareGauge (p : Plane) :
    ‖p‖ ≤ Real.sqrt 2 * squareGauge p := by
  -- Bound each coordinate square by the square of the `ℓ∞` gauge, then compare squares.
  have h0abs : |p 0| ≤ squareGauge p := by
    simpa [squareGauge] using (le_max_left (|p 0|) (|p 1|))
  have h1abs : |p 1| ≤ squareGauge p := by
    simpa [squareGauge] using (le_max_right (|p 0|) (|p 1|))
  have h0 : (p 0) ^ 2 ≤ (squareGauge p) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (squareGauge_nonneg p)]
    exact h0abs
  have h1 : (p 1) ^ 2 ≤ (squareGauge p) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (squareGauge_nonneg p)]
    exact h1abs
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (squareGauge_nonneg p))]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith

/-- Helper for Problem 3-5: radial rescaling from the Euclidean circle to the square boundary. -/
noncomputable def radialToSquare (p : Plane) : Plane :=
  if hp : p = 0 then 0 else (‖p‖ / squareGauge p) • p

/-- Helper for Problem 3-5: radial rescaling from the square boundary back to the Euclidean circle. -/
noncomputable def radialFromSquare (p : Plane) : Plane :=
  if hp : p = 0 then 0 else (squareGauge p / ‖p‖) • p

/-- Helper for Problem 3-5: away from the origin, `radialToSquare` is the expected scalar multiple. -/
theorem radialToSquare_eq {p : Plane} (hp : p ≠ 0) :
    radialToSquare p = (‖p‖ / squareGauge p) • p := by
  -- Off the origin the piecewise definition chooses the radial branch.
  simp [radialToSquare, hp]

/-- Helper for Problem 3-5: away from the origin, `radialFromSquare` is the expected scalar multiple. -/
theorem radialFromSquare_eq {p : Plane} (hp : p ≠ 0) :
    radialFromSquare p = (squareGauge p / ‖p‖) • p := by
  -- Off the origin the inverse piecewise definition also chooses its radial branch.
  simp [radialFromSquare, hp]

/-- Helper for Problem 3-5: `radialToSquare` keeps a nonzero point on the same ray, so its square
gauge becomes the original Euclidean norm. -/
theorem squareGauge_radialToSquare {p : Plane} (hp : p ≠ 0) :
    squareGauge (radialToSquare p) = ‖p‖ := by
  -- The radial rescaling multiplies the square gauge by the same positive scalar.
  have hg : squareGauge p ≠ 0 := ne_of_gt (squareGauge_pos hp)
  rw [radialToSquare_eq hp, squareGauge_smul, abs_of_nonneg]
  · field_simp [hg]
  · exact div_nonneg (norm_nonneg _) (squareGauge_nonneg p)

/-- Helper for Problem 3-5: the Euclidean norm of `radialToSquare p` is the expected rescaled norm. -/
theorem norm_radialToSquare {p : Plane} (hp : p ≠ 0) :
    ‖radialToSquare p‖ = ‖p‖ ^ 2 / squareGauge p := by
  -- Taking norms turns the scalar multiple into a scalar factor.
  rw [radialToSquare_eq hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
  · ring
  · exact div_nonneg (norm_nonneg _) (squareGauge_nonneg p)

/-- Helper for Problem 3-5: the Euclidean norm of `radialFromSquare p` is exactly the square gauge. -/
theorem norm_radialFromSquare {p : Plane} (hp : p ≠ 0) :
    ‖radialFromSquare p‖ = squareGauge p := by
  -- The inverse radial rescaling multiplies the norm by `squareGauge p / ‖p‖`.
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  rw [radialFromSquare_eq hp, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
  · field_simp [hn]
  · exact div_nonneg (squareGauge_nonneg p) (norm_nonneg _)

/-- Helper for Problem 3-5: `radialFromSquare` keeps a nonzero point on the same ray, so its square
gauge is the expected rescaled value. -/
theorem squareGauge_radialFromSquare {p : Plane} (hp : p ≠ 0) :
    squareGauge (radialFromSquare p) = squareGauge p ^ 2 / ‖p‖ := by
  -- The square gauge scales linearly along rays, just as the norm does.
  rw [radialFromSquare_eq hp, squareGauge_smul, abs_of_nonneg]
  · ring
  · exact div_nonneg (squareGauge_nonneg p) (norm_nonneg _)

/-- Helper for Problem 3-5: `radialToSquare` does not send a nonzero point to the origin. -/
theorem radialToSquare_ne_zero {p : Plane} (hp : p ≠ 0) : radialToSquare p ≠ 0 := by
  -- A nonzero point stays nonzero because both the point and the scalar factor are nonzero.
  have hscale : ‖p‖ / squareGauge p ≠ 0 := by
    exact div_ne_zero (norm_ne_zero_iff.mpr hp) (ne_of_gt (squareGauge_pos hp))
  rw [radialToSquare_eq hp]
  exact smul_ne_zero hscale hp

/-- Helper for Problem 3-5: `radialFromSquare` does not send a nonzero point to the origin. -/
theorem radialFromSquare_ne_zero {p : Plane} (hp : p ≠ 0) : radialFromSquare p ≠ 0 := by
  -- The inverse rescaling has the same nonvanishing property on nonzero points.
  have hscale : squareGauge p / ‖p‖ ≠ 0 := by
    exact div_ne_zero (ne_of_gt (squareGauge_pos hp)) (norm_ne_zero_iff.mpr hp)
  rw [radialFromSquare_eq hp]
  exact smul_ne_zero hscale hp

/-- Helper for Problem 3-5: the two radial maps are inverse on nonzero points. -/
theorem radialFromSquare_radialToSquare {p : Plane} (hp : p ≠ 0) :
    radialFromSquare (radialToSquare p) = p := by
  -- After rewriting both radial maps, the two scalar factors cancel to `1`.
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hg : squareGauge p ≠ 0 := ne_of_gt (squareGauge_pos hp)
  rw [radialFromSquare_eq (radialToSquare_ne_zero hp), squareGauge_radialToSquare hp,
    norm_radialToSquare hp, radialToSquare_eq hp, smul_smul]
  have hscalar : ‖p‖ / (‖p‖ ^ 2 / squareGauge p) * (‖p‖ / squareGauge p) = (1 : ℝ) := by
    field_simp [hn, hg]
  rw [hscalar, one_smul]

/-- Helper for Problem 3-5: the two radial maps are inverse on nonzero points. -/
theorem radialToSquare_radialFromSquare {p : Plane} (hp : p ≠ 0) :
    radialToSquare (radialFromSquare p) = p := by
  -- The symmetric scalar-cancellation argument proves the other inverse identity.
  have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hg : squareGauge p ≠ 0 := ne_of_gt (squareGauge_pos hp)
  rw [radialToSquare_eq (radialFromSquare_ne_zero hp), norm_radialFromSquare hp,
    squareGauge_radialFromSquare hp, radialFromSquare_eq hp, smul_smul]
  have hscalar : squareGauge p / (squareGauge p ^ 2 / ‖p‖) * (squareGauge p / ‖p‖) = (1 : ℝ) := by
    field_simp [hn, hg]
  rw [hscalar, one_smul]

/-- Helper for Problem 3-5: the square radial map is Lipschitz at the origin up to a fixed
constant. -/
theorem norm_radialToSquare_le (p : Plane) : ‖radialToSquare p‖ ≤ Real.sqrt 2 * ‖p‖ := by
  by_cases hp : p = 0
  · -- At the origin the bound is immediate from the defining `if`.
    simp [radialToSquare, hp]
  · -- Away from the origin we control the extra radial factor by the `sqrt 2` gauge estimate.
    rw [norm_radialToSquare hp]
    have hg : 0 < squareGauge p := squareGauge_pos hp
    have hratio : ‖p‖ / squareGauge p ≤ Real.sqrt 2 := by
      refine (div_le_iff₀ hg).2 ?_
      simpa [mul_comm] using norm_le_sqrt_two_mul_squareGauge p
    calc
      ‖p‖ ^ 2 / squareGauge p = ‖p‖ * (‖p‖ / squareGauge p) := by ring
      _ ≤ ‖p‖ * Real.sqrt 2 := mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
      _ = Real.sqrt 2 * ‖p‖ := by ring

/-- Helper for Problem 3-5: the inverse radial map is norm-controlled at the origin. -/
theorem norm_radialFromSquare_le (p : Plane) : ‖radialFromSquare p‖ ≤ ‖p‖ := by
  by_cases hp : p = 0
  · -- At the origin both sides are zero.
    simp [radialFromSquare, hp]
  · -- Away from the origin the norm is exactly the square gauge.
    rw [norm_radialFromSquare hp]
    exact squareGauge_le_norm p

/-- Helper for Problem 3-5: the square gauge is continuous. -/
theorem continuous_squareGauge : Continuous squareGauge := by
  -- The square gauge is the maximum of the two continuous coordinate-absolute-value maps.
  have h0 : Continuous fun p : Plane ↦ |p 0| := by
    fun_prop
  have h1 : Continuous fun p : Plane ↦ |p 1| := by
    fun_prop
  simpa [squareGauge] using h0.max h1

/-- Helper for Problem 3-5: `radialToSquare` is continuous at every nonzero point. -/
theorem continuousAt_radialToSquare_of_ne_zero {p : Plane} (hp : p ≠ 0) :
    ContinuousAt radialToSquare p := by
  -- Near a nonzero point the `if` branch is locally constant, so we reduce to the explicit formula.
  have hbranch : ContinuousAt (fun q : Plane ↦ (‖q‖ / squareGauge q) • q) p := by
    have hscale : ContinuousAt (fun q : Plane ↦ ‖q‖ / squareGauge q) p := by
      exact continuous_norm.continuousAt.div continuous_squareGauge.continuousAt
        (by simpa [squareGauge_eq_zero_iff] using hp)
    exact hscale.smul continuousAt_id
  have hEq :
      radialToSquare =ᶠ[𝓝 p] fun q : Plane ↦ (‖q‖ / squareGauge q) • q := by
    filter_upwards [isOpen_ne.mem_nhds hp] with q hq
    simp [radialToSquare, hq]
  exact hbranch.congr_of_eventuallyEq hEq

/-- Helper for Problem 3-5: `radialFromSquare` is continuous at every nonzero point. -/
theorem continuousAt_radialFromSquare_of_ne_zero {p : Plane} (hp : p ≠ 0) :
    ContinuousAt radialFromSquare p := by
  -- The same local branch replacement works for the inverse radial map.
  have hbranch : ContinuousAt (fun q : Plane ↦ (squareGauge q / ‖q‖) • q) p := by
    have hscale : ContinuousAt (fun q : Plane ↦ squareGauge q / ‖q‖) p := by
      exact continuous_squareGauge.continuousAt.div continuous_norm.continuousAt
        (by simpa using norm_ne_zero_iff.mpr hp)
    exact hscale.smul continuousAt_id
  have hEq :
      radialFromSquare =ᶠ[𝓝 p] fun q : Plane ↦ (squareGauge q / ‖q‖) • q := by
    filter_upwards [isOpen_ne.mem_nhds hp] with q hq
    simp [radialFromSquare, hq]
  exact hbranch.congr_of_eventuallyEq hEq

/-- Helper for Problem 3-5: `radialToSquare` is continuous at the origin. -/
theorem continuousAt_radialToSquare_zero : ContinuousAt radialToSquare 0 := by
  -- The global norm bound squeezes `radialToSquare p` to zero with `p`.
  rw [ContinuousAt, show radialToSquare 0 = 0 by simp [radialToSquare]]
  refine squeeze_zero_norm (fun p ↦ norm_radialToSquare_le p) ?_
  have hcont : Continuous fun p : Plane ↦ Real.sqrt 2 * ‖p‖ :=
    continuous_const.mul (show Continuous fun p : Plane ↦ ‖p‖ from continuous_norm)
  simpa using (hcont.continuousAt : ContinuousAt (fun p : Plane ↦ Real.sqrt 2 * ‖p‖) 0).tendsto

/-- Helper for Problem 3-5: `radialFromSquare` is continuous at the origin. -/
theorem continuousAt_radialFromSquare_zero : ContinuousAt radialFromSquare 0 := by
  -- The inverse radial map satisfies the same squeeze argument at the origin.
  rw [ContinuousAt, show radialFromSquare 0 = 0 by simp [radialFromSquare]]
  refine squeeze_zero_norm (fun p ↦ norm_radialFromSquare_le p) ?_
  have hcont : Continuous fun p : Plane ↦ ‖p‖ := continuous_norm
  simpa using (hcont.continuousAt : ContinuousAt (fun p : Plane ↦ ‖p‖) 0).tendsto

/-- Helper for Problem 3-5: `radialToSquare` is continuous. -/
theorem continuous_radialToSquare : Continuous radialToSquare := by
  -- Continuity is assembled from the origin case and the nonzero case.
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p = 0
  · simpa [hp] using continuousAt_radialToSquare_zero
  · exact continuousAt_radialToSquare_of_ne_zero hp

/-- Helper for Problem 3-5: `radialFromSquare` is continuous. -/
theorem continuous_radialFromSquare : Continuous radialFromSquare := by
  -- The inverse radial map is continuous for the same reason.
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p = 0
  · simpa [hp] using continuousAt_radialFromSquare_zero
  · exact continuousAt_radialFromSquare_of_ne_zero hp

-- Proof sketch: use a radial homeomorphism that rescales each nonzero ray so that the Euclidean
-- unit circle is sent to the unit square in the `ℓ∞` norm, and extend it by the identity at the
-- origin.
/-- Problem 3-5 (1): there exists a homeomorphism of `ℝ²` that sends the unit circle to the
boundary of the square of side length `2` centered at the origin. -/
theorem exists_homeomorph_maps_unitCircle_to_squareBoundary :
    ∃ F : Plane ≃ₜ Plane, F '' unitCircle = squareBoundary := by
  -- Package the two radial maps into inverse continuous maps, then identify the image set.
  refine ⟨
    { toEquiv :=
        { toFun := radialToSquare
          invFun := radialFromSquare
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := continuous_radialToSquare
      continuous_invFun := continuous_radialFromSquare },
    ?_⟩
  · intro p
    by_cases hp : p = 0
    · simp [hp, radialToSquare, radialFromSquare]
    · exact radialFromSquare_radialToSquare hp
  · intro p
    by_cases hp : p = 0
    · simp [hp, radialToSquare, radialFromSquare]
    · exact radialToSquare_radialFromSquare hp
  · ext q
    constructor
    · rintro ⟨p, hpCircle, rfl⟩
      have hnorm : ‖p‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hpCircle
      have hp : p ≠ 0 := by
        exact norm_ne_zero_iff.mp (by simpa [hnorm])
      change squareGauge (radialToSquare p) = 1
      rw [squareGauge_radialToSquare hp, hnorm]
    · intro hq
      have hGauge : squareGauge q = 1 := hq
      have hq0 : q ≠ 0 := by
        intro hzero
        rw [hzero] at hGauge
        simp [squareGauge] at hGauge
      refine ⟨radialFromSquare q, ?_, ?_⟩
      · have hnorm : ‖radialFromSquare q‖ = 1 := by
          rw [norm_radialFromSquare hq0, hGauge]
        simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hnorm
      · simpa using radialToSquare_radialFromSquare hq0

/-- Helper for Problem 3-5: the northeast corner of the square boundary. -/
def squareCorner : Plane := WithLp.toLp 2 ![1, 1]

/-- Helper for Problem 3-5: the chosen corner really lies on the square boundary. -/
theorem squareCorner_mem_squareBoundary : squareCorner ∈ squareBoundary := by
  -- Both coordinates equal `1`, so the defining maximum is `1`.
  simp [squareCorner, squareBoundary]

/-- Helper for Problem 3-5: the local rotation arc through `p`. -/
noncomputable def rotationArc (p : Plane) : ℝ → Plane :=
  fun t ↦ WithLp.toLp 2
    ![Real.cos t * p 0 - Real.sin t * p 1, Real.sin t * p 0 + Real.cos t * p 1]

/-- Helper for Problem 3-5: the velocity of the local rotation arc at time `0`. -/
def rotationVelocity (p : Plane) : Plane :=
  WithLp.toLp 2 ![-p 1, p 0]

/-- Helper for Problem 3-5: the first coordinate of the rotation arc. -/
@[simp] theorem rotationArc_apply_zero (p : Plane) (t : ℝ) :
    rotationArc p t 0 = Real.cos t * p 0 - Real.sin t * p 1 := by
  -- At coordinate `0`, the defining `if` selects the cosine-sine formula.
  simp [rotationArc, PiLp.toLp_apply]

/-- Helper for Problem 3-5: the second coordinate of the rotation arc. -/
@[simp] theorem rotationArc_apply_one (p : Plane) (t : ℝ) :
    rotationArc p t 1 = Real.sin t * p 0 + Real.cos t * p 1 := by
  -- At coordinate `1`, the defining `if` selects the complementary formula.
  simp [rotationArc, PiLp.toLp_apply]

/-- Helper for Problem 3-5: the velocity vector records the expected quarter-turn. -/
@[simp] theorem rotationVelocity_apply_zero (p : Plane) :
    rotationVelocity p 0 = -p 1 := by
  -- The first coordinate is the negative second coordinate of `p`.
  simp [rotationVelocity, PiLp.toLp_apply]

/-- Helper for Problem 3-5: the velocity vector records the expected quarter-turn. -/
@[simp] theorem rotationVelocity_apply_one (p : Plane) :
    rotationVelocity p 1 = p 0 := by
  -- The second coordinate is the first coordinate of `p`.
  simp [rotationVelocity, PiLp.toLp_apply]

/-- Helper for Problem 3-5: the local rotation arc starts at the chosen point. -/
@[simp] theorem rotationArc_zero (p : Plane) : rotationArc p 0 = p := by
  -- Evaluating the trigonometric coefficients at `0` collapses the rotation to the identity.
  ext i
  fin_cases i <;> simp [rotationArc, PiLp.toLp_apply, Real.sin_zero, Real.cos_zero]

/-- Helper for Problem 3-5: rotating a point in the plane preserves its Euclidean norm. -/
theorem norm_rotationArc (p : Plane) (t : ℝ) : ‖rotationArc p t‖ = ‖p‖ := by
  -- Expand both norms in coordinates and use `sin^2 + cos^2 = 1`.
  have hsq : ‖rotationArc p t‖ ^ 2 = ‖p‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
      Fin.sum_univ_two, rotationArc_apply_zero, rotationArc_apply_one]
    nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith [hsq, norm_nonneg (rotationArc p t), norm_nonneg p]

/-- Helper for Problem 3-5: the local rotation arc stays on the unit circle. -/
theorem rotationArc_mem_unitCircle {p : Plane} (hp : p ∈ unitCircle) (t : ℝ) :
    rotationArc p t ∈ unitCircle := by
  -- Norm preservation transfers the unit-circle condition from `p` to `rotationArc p t`.
  have hp_norm : ‖p‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hp
  have hrot_norm : ‖rotationArc p t‖ = 1 := by
    rw [norm_rotationArc, hp_norm]
  simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hrot_norm

/-- Helper for Problem 3-5: the rotation arc has the expected tangent vector at `0`. -/
theorem rotationArc_hasDerivAt_zero (p : Plane) :
    HasDerivAt (rotationArc p) (rotationVelocity p) 0 := by
  -- Differentiate the coordinate tuple first, then package it into `Plane` using `toLp`.
  have htuple :
      HasDerivAt
        (fun t : ℝ ↦
          (![Real.cos t * p 0 - Real.sin t * p 1,
            Real.sin t * p 0 + Real.cos t * p 1] : Fin 2 → ℝ))
        (![-p 1, p 0] : Fin 2 → ℝ) 0 := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [Real.sin_zero, Real.cos_zero] using
        (((Real.hasDerivAt_cos 0).mul_const (p 0)).sub
          ((Real.hasDerivAt_sin 0).mul_const (p 1)))
    · simpa [Real.sin_zero, Real.cos_zero] using
        (((Real.hasDerivAt_sin 0).mul_const (p 0)).add
          ((Real.hasDerivAt_cos 0).mul_const (p 1)))
  have hbase :
      (fun i : Fin 2 ↦ p i) =
        (fun t : ℝ ↦
          (![Real.cos t * p 0 - Real.sin t * p 1,
            Real.sin t * p 0 + Real.cos t * p 1] : Fin 2 → ℝ)) 0 := by
    ext i
    fin_cases i <;> simp [Real.sin_zero, Real.cos_zero]
  have htoLp :
      HasFDerivAt (WithLp.toLp 2)
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap)
        (fun i : Fin 2 ↦ p i) :=
    PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (fun i : Fin 2 ↦ p i)
  rw [hbase] at htoLp
  simpa [rotationArc, rotationVelocity] using
    htoLp.comp_hasDerivAt 0 htuple

/-- Helper for Problem 3-5: the tangent vector to the rotation arc is nonzero on the unit circle. -/
theorem rotationVelocity_ne_zero {p : Plane} (hp : p ∈ unitCircle) :
    rotationVelocity p ≠ 0 := by
  -- A zero velocity would force both coordinates of `p` to vanish, contradicting `‖p‖ = 1`.
  intro hv
  have hp0 : p 0 = 0 := by
    have hv1 := congrArg (fun x : Plane ↦ x 1) hv
    simpa [rotationVelocity, PiLp.toLp_apply] using hv1
  have hp1 : p 1 = 0 := by
    have hv0 := congrArg (fun x : Plane ↦ x 0) hv
    simpa [rotationVelocity, PiLp.toLp_apply] using hv0
  have hp_zero : p = 0 := by
    ext i
    fin_cases i <;> simp [hp0, hp1]
  have hp_norm : ‖p‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hp
  have : ‖p‖ = 0 := by simpa [hp_zero]
  linarith

/-- Helper for Problem 3-5: each coordinate of a curve on the square boundary has a local maximum
at the corner `(1, 1)`. -/
theorem squareBoundary_coord_isLocalMax_at_corner {δ : ℝ → Plane} {v : Plane}
    (hδ : HasDerivAt δ v 0) (hδ0 : δ 0 = squareCorner)
    (hδsq : ∀ᶠ t in 𝓝 0, δ t ∈ squareBoundary) (i : Fin 2) :
    IsLocalMax (fun t ↦ δ t i) 0 := by
  -- Use continuity from differentiability to keep the chosen coordinate positive near the corner.
  have hcorner_i : squareCorner i = 1 := by
    fin_cases i <;> simp [squareCorner, PiLp.toLp_apply]
  have hcoord_deriv : HasDerivAt (fun t ↦ δ t i) (v i) 0 := by
    have hproj :
        HasFDerivAt (fun q : Plane ↦ q i)
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i) (δ 0) :=
      PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (δ 0) i
    simpa using hproj.comp_hasDerivAt 0 hδ
  have hcoord : ContinuousAt (fun t ↦ δ t i) 0 := hcoord_deriv.continuousAt
  have hpos : ∀ᶠ t in 𝓝 0, 0 < δ t i := by
    have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 (δ 0 i) := by
      rw [hδ0, hcorner_i]
      exact Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
    exact hcoord hIoi
  have hle : ∀ᶠ t in 𝓝 0, δ t i ≤ 1 := by
    -- On the square boundary, the relevant absolute value is bounded by the defining maximum `1`.
    filter_upwards [hδsq, hpos] with t htSq htPos
    fin_cases i
    · have hsq : max |δ t 0| |δ t 1| = 1 := htSq
      have hcoord_le : |δ t 0| ≤ 1 := by
        simpa [hsq] using (le_max_left (|δ t 0|) (|δ t 1|))
      have habs : |δ t 0| = δ t 0 := abs_of_pos htPos
      rwa [habs] at hcoord_le
    · have hsq : max |δ t 0| |δ t 1| = 1 := htSq
      have hcoord_le : |δ t 1| ≤ 1 := by
        simpa [hsq] using (le_max_right (|δ t 0|) (|δ t 1|))
      have habs : |δ t 1| = δ t 1 := abs_of_pos htPos
      rwa [habs] at hcoord_le
  -- The eventual inequality `δ t i ≤ 1 = δ 0 i` is exactly the local-maximum condition.
  show ∀ᶠ t in 𝓝 0, (fun t ↦ δ t i) t ≤ (fun t ↦ δ t i) 0
  simpa [IsLocalMax, hδ0, hcorner_i] using hle

/-- Helper for Problem 3-5: a differentiable curve on the square boundary has zero velocity at the
corner `(1, 1)`. -/
theorem squareBoundary_curve_deriv_eq_zero_at_corner {δ : ℝ → Plane} {v : Plane}
    (hδ : HasDerivAt δ v 0) (hδ0 : δ 0 = squareCorner)
    (hδsq : ∀ᶠ t in 𝓝 0, δ t ∈ squareBoundary) :
    v = 0 := by
  -- Apply Fermat's theorem to the two coordinate functions and then compare coordinates.
  ext i
  have hmax : IsLocalMax (fun t ↦ δ t i) 0 :=
    squareBoundary_coord_isLocalMax_at_corner hδ hδ0 hδsq i
  have hcoord : HasDerivAt (fun t ↦ δ t i) (v i) 0 := by
    have hproj :
        HasFDerivAt (fun q : Plane ↦ q i)
          (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i) (δ 0) :=
      PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (δ 0) i
    simpa using hproj.comp_hasDerivAt 0 hδ
  simpa [hcoord.deriv] using hmax.deriv_eq_zero

-- Proof sketch: if a diffeomorphism sent the smooth unit circle to the square boundary, then the
-- image of a smooth parametrized arc would have to be a smooth immersed curve in `ℝ²`; checking
-- the coordinate functions at a corner gives a contradiction because the square boundary is not a
-- smooth embedded one-manifold there.
/-- Problem 3-5 (2): no diffeomorphism of `ℝ²` sends the unit circle to the boundary of the square
of side length `2` centered at the origin. -/
theorem not_exists_diffeomorph_maps_unitCircle_to_squareBoundary :
    ¬ ∃ F : Plane ≃ₘ[ℝ] Plane, F '' unitCircle = squareBoundary := by
  -- Route correction: work with the explicit local rotation arc through a preimage of the corner.
  rintro ⟨F, hFK⟩
  have hcorner_im : squareCorner ∈ F '' unitCircle := by
    rw [hFK]
    exact squareCorner_mem_squareBoundary
  rcases hcorner_im with ⟨p, hpCircle, hp_corner⟩
  let v : Plane := rotationVelocity p
  let δ : ℝ → Plane := fun t ↦ F (rotationArc p t)
  have hδ0 : δ 0 = squareCorner := by
    -- The image curve starts at the chosen corner because the rotation arc starts at `p`.
    simp [δ, hp_corner]
  have hδsq : ∀ᶠ t in 𝓝 0, δ t ∈ squareBoundary := by
    -- Every point of the rotated arc lies on the unit circle, hence its image lies on the square.
    refine Filter.Eventually.of_forall ?_
    intro t
    rw [← hFK]
    exact ⟨rotationArc p t, rotationArc_mem_unitCircle hpCircle t, rfl⟩
  have hFderiv : HasFDerivAt F (fderiv ℝ F p) p := by
    -- For a diffeomorphism of vector spaces, manifold smoothness specializes to ordinary smoothness.
    have hdiff : DifferentiableAt ℝ F p := by
      simpa using ((F.contDiff.contDiffAt : ContDiffAt ℝ ∞ F p).differentiableAt (by simp))
    simpa using hdiff.hasFDerivAt
  have hδderiv : HasDerivAt δ ((fderiv ℝ F p) v) 0 := by
    -- Chain the derivative of `F` with the derivative of the rotation arc.
    have hFderiv' : HasFDerivAt F (fderiv ℝ F p) (rotationArc p 0) := by
      simpa using hFderiv
    simpa [δ, v] using hFderiv'.comp_hasDerivAt 0 (rotationArc_hasDerivAt_zero p)
  have hzero : (fderiv ℝ F p) v = 0 := by
    -- The corner obstruction forces the image-curve velocity to vanish.
    simpa [δ] using squareBoundary_curve_deriv_eq_zero_at_corner hδderiv hδ0 hδsq
  have hinj : Function.Injective (fderiv ℝ F p : Plane →L[ℝ] Plane) := by
    -- The derivative of a diffeomorphism is a continuous linear equivalence, hence injective.
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    rw [← mfderiv_eq_fderiv]
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe F hn (x := p)]
    exact (F.mfderivToContinuousLinearEquiv hn p).injective
  have hv_zero : v = 0 := by
    -- Injectivity transfers the vanishing of the image velocity back to the original velocity.
    apply hinj
    simpa using hzero
  exact rotationVelocity_ne_zero hpCircle hv_zero
