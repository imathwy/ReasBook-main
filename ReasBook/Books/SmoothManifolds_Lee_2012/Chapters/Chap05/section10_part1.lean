import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_5_10 (from Chap05/Sec05_29) -/
noncomputable section

open Set
open scoped Manifold ContDiff

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "unitSphere2" => Metric.sphere (0 : R3) 1

/-- Helper for Exercise 5.10: the forward spherical-coordinate map records azimuth,
inclination, and radius. -/
def sphericalCoordinatesToFun (x : R3) : R3 :=
  WithLp.toLp 2 ![Complex.arg (Complex.mk (x 0) (x 1)), Real.arccos (x 2 / ‖x‖), ‖x‖]

/-- Helper for Exercise 5.10: the inverse spherical-coordinate map rebuilds a point from
azimuth, inclination, and radius. -/
def sphericalCoordinatesInvFun (u : R3) : R3 :=
  WithLp.toLp 2
    ![u 2 * Real.sin (u 1) * Real.cos (u 0),
      u 2 * Real.sin (u 1) * Real.sin (u 0),
      u 2 * Real.cos (u 1)]

/-- Helper for Exercise 5.10: the spherical-coordinate source removes the branch cut and the
`z`-axis. -/
def sphericalCoordinatesSourceSet : Set R3 :=
  {x : R3 | 0 < x 0 ∨ x 1 ≠ 0}

/-- Helper for Exercise 5.10: the spherical-coordinate target is the usual azimuth-inclination-
radius region. -/
def sphericalCoordinatesTargetSet : Set R3 :=
  {u : R3 |
    u 0 ∈ Ioo (-Real.pi) Real.pi ∧ u 1 ∈ Ioo (0 : ℝ) Real.pi ∧ 0 < u 2}

/-- Helper for Exercise 5.10: source points have nonzero planar complex coordinate. -/
lemma sphericalCoordinates_source_complex_ne_zero {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    Complex.mk (x 0) (x 1) ≠ 0 := by
  -- The source excludes exactly the points with nonpositive `x`-coordinate and vanishing
  -- `y`-coordinate, so the planar complex coordinate cannot vanish.
  intro hz
  have hx0 : x 0 = 0 := by
    simpa using congrArg Complex.re hz
  have hx1 : x 1 = 0 := by
    simpa using congrArg Complex.im hz
  rcases hx with hx0_pos | hx1_ne
  · linarith
  · exact hx1_ne hx1

/-- Helper for Exercise 5.10: source points have positive Euclidean norm. -/
lemma sphericalCoordinates_source_norm_pos {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    0 < ‖x‖ := by
  -- The source condition forces the planar complex coordinate to be nonzero, hence `x ≠ 0`.
  have hx_ne : x ≠ 0 := by
    intro hx0
    have hcomplex_zero : Complex.mk (x 0) (x 1) = 0 := by
      subst hx0
      rfl
    exact sphericalCoordinates_source_complex_ne_zero hx hcomplex_zero
  exact norm_pos_iff.mpr hx_ne

/-- Helper for Exercise 5.10: on the source, the vertical ratio `z / ‖x‖` stays strictly between
`-1` and `1`. -/
lemma sphericalCoordinates_source_ratio_bounds {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    -1 < x 2 / ‖x‖ ∧ x 2 / ‖x‖ < 1 := by
  -- Compare the full norm square with the `z`-coordinate square; the planar part is strictly
  -- positive on the source because the branch-cut projection is nonzero.
  have hnorm_pos : 0 < ‖x‖ := sphericalCoordinates_source_norm_pos hx
  have hplanar_pos : 0 < x 0 ^ 2 + x 1 ^ 2 := by
    have hcomplex_ne : Complex.mk (x 0) (x 1) ≠ 0 :=
      sphericalCoordinates_source_complex_ne_zero hx
    have hcomplex_normSq_pos : 0 < Complex.normSq (Complex.mk (x 0) (x 1)) := by
      exact Complex.normSq_pos.mpr hcomplex_ne
    simpa [Complex.normSq_apply, pow_two, add_assoc, add_comm, add_left_comm]
      using hcomplex_normSq_pos
  have hnorm_sq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, add_assoc, add_comm, add_left_comm]
      using (EuclideanSpace.real_norm_sq_eq x)
  have hz_sq_lt : x 2 ^ 2 < ‖x‖ ^ 2 := by
    rw [hnorm_sq]
    nlinarith
  have hratio_sq_lt : (x 2 / ‖x‖) ^ 2 < 1 ^ 2 := by
    rw [div_pow, one_pow]
    exact (div_lt_one (sq_pos_of_pos hnorm_pos)).2 hz_sq_lt
  have hratio_abs_lt : |x 2 / ‖x‖| < 1 := by
    exact abs_lt_of_sq_lt_sq hratio_sq_lt (by norm_num)
  exact abs_lt.mp hratio_abs_lt

/-- Helper for Exercise 5.10: on the source, the ratio `z / ‖x‖` avoids the arccos endpoints. -/
lemma sphericalCoordinates_source_ratio_mem_endpoint_compl {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    x 2 / ‖x‖ ∈ ({-1, 1}ᶜ : Set ℝ) := by
  -- The strict inequalities from the previous lemma exclude both endpoint values.
  rcases sphericalCoordinates_source_ratio_bounds hx with ⟨hleft, hright⟩
  change x 2 / ‖x‖ ∉ ({-1, 1} : Set ℝ)
  simp [hleft.ne', hright.ne]

/-- Helper for Exercise 5.10: the inverse spherical-coordinate map has norm squared equal to the
square of the radius coordinate. -/
lemma sphericalCoordinatesInvFun_norm_sq (u : R3) :
    ‖sphericalCoordinatesInvFun u‖ ^ 2 = u 2 ^ 2 := by
  -- Expand the inverse map and reduce the Euclidean norm to the standard trigonometric identity.
  have hnonneg :
      0 ≤
        (u 2 * Real.sin (u 1) * Real.cos (u 0)) ^ 2 +
          (u 2 * Real.sin (u 1) * Real.sin (u 0)) ^ 2 +
          (u 2 * Real.cos (u 1)) ^ 2 := by
    positivity
  rw [show ‖sphericalCoordinatesInvFun u‖ ^ 2 =
      √((u 2 * Real.sin (u 1) * Real.cos (u 0)) ^ 2 +
          (u 2 * Real.sin (u 1) * Real.sin (u 0)) ^ 2 +
          (u 2 * Real.cos (u 1)) ^ 2) ^ 2 by
      simp [sphericalCoordinatesInvFun, EuclideanSpace.norm_eq, Fin.sum_univ_three]]
  rw [Real.sq_sqrt hnonneg]
  have hφ : Real.cos (u 0) ^ 2 + Real.sin (u 0) ^ 2 = 1 := by
    simpa [pow_two, add_comm] using Real.sin_sq_add_cos_sq (u 0)
  have hθ : Real.sin (u 1) ^ 2 + Real.cos (u 1) ^ 2 = 1 := by
    simpa [pow_two, add_comm] using Real.sin_sq_add_cos_sq (u 1)
  calc
    (u 2 * Real.sin (u 1) * Real.cos (u 0)) ^ 2 +
        (u 2 * Real.sin (u 1) * Real.sin (u 0)) ^ 2 +
        (u 2 * Real.cos (u 1)) ^ 2 =
        u 2 ^ 2 * (Real.sin (u 1) ^ 2 * (Real.cos (u 0) ^ 2 + Real.sin (u 0) ^ 2) +
          Real.cos (u 1) ^ 2) := by
      ring
    _ = u 2 ^ 2 * (Real.sin (u 1) ^ 2 * 1 + Real.cos (u 1) ^ 2) := by
      rw [hφ]
    _ = u 2 ^ 2 * (Real.sin (u 1) ^ 2 + Real.cos (u 1) ^ 2) := by
      ring
    _ = u 2 ^ 2 * 1 := by
      rw [hθ]
    _ = u 2 ^ 2 := by
      ring

/-- Helper for Exercise 5.10: the planar complex norm square is the full Euclidean norm square
minus the vertical coordinate square. -/
lemma sphericalCoordinates_planar_norm_sq (x : R3) :
    ‖Complex.mk (x 0) (x 1)‖ ^ 2 = ‖x‖ ^ 2 - x 2 ^ 2 := by
  -- Expand both norm squares in coordinates and cancel the vertical contribution.
  calc
    ‖Complex.mk (x 0) (x 1)‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    _ = ‖x‖ ^ 2 - x 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      ring

/-- Helper for Exercise 5.10: the horizontal radius recovered from `‖x‖` and `arccos (z / ‖x‖)`
is the norm of the planar complex coordinate. -/
lemma sphericalCoordinates_radius_sin_arccos_eq_complex_norm {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    ‖x‖ * Real.sin (Real.arccos (x 2 / ‖x‖)) = ‖Complex.mk (x 0) (x 1)‖ := by
  -- Compare squares after rewriting `sin (arccos ·)` as a square root; the source bounds make
  -- the square root real-valued and the planar norm square identity removes the remaining ratio.
  have hnorm_ne : ‖x‖ ≠ 0 := ne_of_gt (sphericalCoordinates_source_norm_pos hx)
  rcases sphericalCoordinates_source_ratio_bounds hx with ⟨hratio_left, hratio_right⟩
  have hsqrt_nonneg : 0 ≤ 1 - (x 2 / ‖x‖) ^ 2 := by
    nlinarith
  rw [Real.sin_arccos]
  refine (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _)).mp ?_
  calc
    (‖x‖ * Real.sqrt (1 - (x 2 / ‖x‖) ^ 2)) ^ 2 = ‖x‖ ^ 2 * (1 - (x 2 / ‖x‖) ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hsqrt_nonneg]
    _ = ‖x‖ ^ 2 - x 2 ^ 2 := by
      rw [div_pow]
      field_simp [hnorm_ne]
    _ = ‖Complex.mk (x 0) (x 1)‖ ^ 2 := by
      simpa using (sphericalCoordinates_planar_norm_sq x).symm

/-- Helper for Exercise 5.10: target points have positive horizontal radius factor. -/
lemma sphericalCoordinates_target_horizontal_pos {u : R3}
    (hu : u ∈ sphericalCoordinatesTargetSet) :
    0 < u 2 * Real.sin (u 1) := by
  -- The target requires positive radius and inclination strictly between `0` and `π`.
  rcases hu with ⟨_, hu1, hu2⟩
  exact mul_pos hu2 (Real.sin_pos_of_mem_Ioo hu1)

/-- Helper for Exercise 5.10: the inverse map sends target points back into the spherical-chart
source. -/
lemma sphericalCoordinates_map_target {u : R3}
    (hu : u ∈ sphericalCoordinatesTargetSet) :
    sphericalCoordinatesInvFun u ∈ sphericalCoordinatesSourceSet := by
  -- Route correction: the source-faithful polar-coordinate split is on whether `sin φ` vanishes,
  -- with the positive horizontal factor handled separately.
  rcases hu with ⟨hu0, hu1, hu2⟩
  have hhorizontal : 0 < u 2 * Real.sin (u 1) :=
    sphericalCoordinates_target_horizontal_pos ⟨hu0, hu1, hu2⟩
  rcases eq_or_ne (Real.sin (u 0)) 0 with hsin | hsin
  · -- When `sin φ = 0`, the angle lies at `0` inside `(-π, π)`, so the first coordinate is
    -- the positive horizontal factor.
    left
    have hu0_zero : u 0 = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt hu0.1 hu0.2).mp hsin
    simpa [sphericalCoordinatesInvFun, hu0_zero, Real.cos_zero, mul_assoc] using hhorizontal
  · -- Otherwise the second coordinate keeps the point away from the branch cut.
    right
    have hcoord1_ne : u 2 * Real.sin (u 1) * Real.sin (u 0) ≠ 0 :=
      mul_ne_zero hhorizontal.ne' hsin
    simpa [sphericalCoordinatesInvFun, mul_assoc] using hcoord1_ne

/-- Helper for Exercise 5.10: the planar part of the inverse spherical-coordinate map is the
usual complex polar factor. -/
lemma sphericalCoordinatesInvFun_planar_as_complex (u : R3) :
    Complex.mk ((sphericalCoordinatesInvFun u) 0) ((sphericalCoordinatesInvFun u) 1) =
      (u 2 * Real.sin (u 1)) * (Real.cos (u 0) + Real.sin (u 0) * Complex.I) := by
  -- This is the source-faithful bridge from the first two Euclidean coordinates to one complex
  -- number in polar form.
  apply Complex.ext
  · -- The real part is the horizontal radius times `cos φ`.
    simp [sphericalCoordinatesInvFun, PiLp.toLp_apply, Complex.mul_re, Complex.mul_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, mul_assoc]
  · -- The imaginary part is the horizontal radius times `sin φ`.
    simp [sphericalCoordinatesInvFun, PiLp.toLp_apply, Complex.mul_re, Complex.mul_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, mul_assoc]

/-- Helper for Exercise 5.10: source points map to the complex slit plane used by the
`Complex.arg` API. -/
lemma sphericalCoordinates_source_mem_slitPlane {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    Complex.mk (x 0) (x 1) ∈ Complex.slitPlane := by
  -- This is the exact source-to-`Complex.arg` bridge: the source inequality is the slit-plane
  -- membership condition written in Euclidean coordinates.
  simpa [sphericalCoordinatesSourceSet, Complex.mem_slitPlane_iff] using hx

/-- Helper for Exercise 5.10: the forward map sends source points into the standard spherical
target. -/
lemma sphericalCoordinates_map_source {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    sphericalCoordinatesToFun x ∈ sphericalCoordinatesTargetSet := by
  -- Route correction: the forward proof should first translate the source condition into the
  -- slit-plane hypothesis for `Complex.arg`, then combine this with the ratio bounds.
  rcases sphericalCoordinates_source_ratio_bounds hx with ⟨hratio_left, hratio_right⟩
  have harg_lt_pi : Complex.arg (Complex.mk (x 0) (x 1)) < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    rcases hx with hx0 | hx1
    · exact Or.inl hx0.le
    · exact Or.inr hx1
  refine ⟨?_, ?_, sphericalCoordinates_source_norm_pos hx⟩
  · simp only [sphericalCoordinatesToFun, PiLp.toLp_apply]
    exact ⟨Complex.neg_pi_lt_arg _, harg_lt_pi⟩
  · simp only [sphericalCoordinatesToFun, PiLp.toLp_apply]
    exact ⟨Real.arccos_pos.mpr hratio_right, Real.arccos_lt_pi.mpr hratio_left⟩

/-- Helper for Exercise 5.10: applying spherical coordinates after the inverse map recovers the
target coordinates. -/
lemma sphericalCoordinates_left_inv {u : R3}
    (hu : u ∈ sphericalCoordinatesTargetSet) :
    sphericalCoordinatesToFun (sphericalCoordinatesInvFun u) = u := by
  -- Route correction: instead of chasing three unrelated coordinates, recover the planar part as
  -- one complex polar factor, then use the inverse norm identity for inclination and radius.
  rcases hu with ⟨hu0, hu1, hu2⟩
  have hhorizontal : 0 < u 2 * Real.sin (u 1) :=
    sphericalCoordinates_target_horizontal_pos ⟨hu0, hu1, hu2⟩
  have hnorm_eq : ‖sphericalCoordinatesInvFun u‖ = u 2 := by
    -- The radius coordinate is positive on the target, so its square root is determined uniquely.
    refine (sq_eq_sq₀ (norm_nonneg _) hu2.le).mp ?_
    simpa using sphericalCoordinatesInvFun_norm_sq u
  have harg :
      Complex.arg
          (Complex.mk ((sphericalCoordinatesInvFun u) 0) ((sphericalCoordinatesInvFun u) 1)) =
        u 0 := by
    -- The planar complex factor has argument exactly the azimuth coordinate.
    rw [sphericalCoordinatesInvFun_planar_as_complex]
    simpa [mul_assoc] using
      (Complex.arg_mul_cos_add_sin_mul_I hhorizontal ⟨hu0.1, hu0.2.le⟩)
  have hratio :
      (sphericalCoordinatesInvFun u) 2 / ‖sphericalCoordinatesInvFun u‖ = Real.cos (u 1) := by
    -- After substituting the recovered norm, the third coordinate is the usual cosine factor.
    rw [hnorm_eq]
    calc
      (sphericalCoordinatesInvFun u) 2 / u 2 = (u 2 * Real.cos (u 1)) / u 2 := by
        simp [sphericalCoordinatesInvFun, PiLp.toLp_apply]
      _ = Real.cos (u 1) := by
        field_simp [hu2.ne']
  ext i
  fin_cases i
  · -- The azimuth coordinate is recovered from the planar complex argument.
    simpa [sphericalCoordinatesToFun, PiLp.toLp_apply] using harg
  · -- The inclination coordinate is `arccos (cos θ) = θ` on `(0, π)`.
    simpa [sphericalCoordinatesToFun, PiLp.toLp_apply, hratio] using
      (Real.arccos_cos hu1.1.le hu1.2.le)
  · -- The radius coordinate is exactly the norm of the reconstructed point.
    simpa [sphericalCoordinatesToFun, PiLp.toLp_apply] using hnorm_eq

/-- Helper for Exercise 5.10: rebuilding a source point from its spherical coordinates gives the
original point. -/
lemma sphericalCoordinates_right_inv {x : R3}
    (hx : x ∈ sphericalCoordinatesSourceSet) :
    sphericalCoordinatesInvFun (sphericalCoordinatesToFun x) = x := by
  -- Route correction: reconstruct the first two coordinates through one complex identity, then
  -- read off the real and imaginary parts; the third coordinate is a direct scalar simplification.
  have hplanar :
      Complex.mk ((sphericalCoordinatesInvFun (sphericalCoordinatesToFun x)) 0)
          ((sphericalCoordinatesInvFun (sphericalCoordinatesToFun x)) 1) =
        Complex.mk (x 0) (x 1) := by
    -- The horizontal radius becomes the planar complex norm, so the polar form collapses.
    let z : ℂ := Complex.mk (x 0) (x 1)
    calc
      Complex.mk ((sphericalCoordinatesInvFun (sphericalCoordinatesToFun x)) 0)
          ((sphericalCoordinatesInvFun (sphericalCoordinatesToFun x)) 1) =
          (‖x‖ * Real.sin (Real.arccos (x 2 / ‖x‖))) *
            (Real.cos (Complex.arg (Complex.mk (x 0) (x 1))) +
              Real.sin (Complex.arg (Complex.mk (x 0) (x 1))) * Complex.I) := by
        rw [sphericalCoordinatesInvFun_planar_as_complex]
        simp [sphericalCoordinatesToFun, PiLp.toLp_apply]
      _ = (((‖x‖ * Real.sin (Real.arccos (x 2 / ‖x‖))) : ℝ) : ℂ) *
            (Real.cos (Complex.arg (Complex.mk (x 0) (x 1))) +
              Real.sin (Complex.arg (Complex.mk (x 0) (x 1))) * Complex.I) := by
        simp
      _ = (‖Complex.mk (x 0) (x 1)‖ : ℂ) *
            (Real.cos (Complex.arg (Complex.mk (x 0) (x 1))) +
              Real.sin (Complex.arg (Complex.mk (x 0) (x 1))) * Complex.I) := by
        exact congrArg
          (fun r : ℝ =>
            (r : ℂ) *
              (Real.cos (Complex.arg (Complex.mk (x 0) (x 1))) +
                Real.sin (Complex.arg (Complex.mk (x 0) (x 1))) * Complex.I))
          (sphericalCoordinates_radius_sin_arccos_eq_complex_norm hx)
      _ = Complex.mk (x 0) (x 1) := by
        simpa [z] using (Complex.norm_mul_cos_add_sin_mul_I z)
  have hcoord2 :
      (sphericalCoordinatesInvFun (sphericalCoordinatesToFun x)) 2 = x 2 := by
    -- The third coordinate simplifies using `cos (arccos t) = t` and nonvanishing norm.
    have hnorm_ne : ‖x‖ ≠ 0 := ne_of_gt (sphericalCoordinates_source_norm_pos hx)
    rcases sphericalCoordinates_source_ratio_bounds hx with ⟨hratio_left, hratio_right⟩
    calc
      (sphericalCoordinatesInvFun (sphericalCoordinatesToFun x)) 2
          = ‖x‖ * Real.cos (Real.arccos (x 2 / ‖x‖)) := by
              simp [sphericalCoordinatesInvFun, sphericalCoordinatesToFun, PiLp.toLp_apply]
      _ = ‖x‖ * (x 2 / ‖x‖) := by
        rw [Real.cos_arccos hratio_left.le hratio_right.le]
      _ = x 2 := by
        field_simp [hnorm_ne]
  ext i
  fin_cases i
  · -- The first coordinate is the real part of the reconstructed planar complex number.
    simpa [sphericalCoordinatesInvFun, sphericalCoordinatesToFun, PiLp.toLp_apply] using
      congrArg Complex.re hplanar
  · -- The second coordinate is the imaginary part of the reconstructed planar complex number.
    simpa [sphericalCoordinatesInvFun, sphericalCoordinatesToFun, PiLp.toLp_apply] using
      congrArg Complex.im hplanar
  · -- The third coordinate is the vertical factor handled above.
    simpa using hcoord2

/-- Helper for Exercise 5.10: the spherical-coordinate source is open. -/
lemma sphericalCoordinates_open_source : IsOpen sphericalCoordinatesSourceSet := by
  -- The source is the union of a half-space and the complement of a coordinate hyperplane.
  have h0_cont : Continuous fun x : R3 => x 0 := PiLp.continuous_apply 2 _ 0
  have h1_cont : Continuous fun x : R3 => x 1 := PiLp.continuous_apply 2 _ 1
  simpa [sphericalCoordinatesSourceSet] using
    (isOpen_lt continuous_const h0_cont).union
      (isOpen_ne_fun h1_cont continuous_const)

/-- Helper for Exercise 5.10: the spherical-coordinate target is open. -/
lemma sphericalCoordinates_open_target : IsOpen sphericalCoordinatesTargetSet := by
  -- Each target inequality is open, and the target is their finite intersection.
  have h0_cont : Continuous fun u : R3 => u 0 := PiLp.continuous_apply 2 _ 0
  have h1_cont : Continuous fun u : R3 => u 1 := PiLp.continuous_apply 2 _ 1
  have h2_cont : Continuous fun u : R3 => u 2 := PiLp.continuous_apply 2 _ 2
  rw [sphericalCoordinatesTargetSet]
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  change IsOpen
    (({u : R3 | -Real.pi < u 0} ∩ {u : R3 | u 0 < Real.pi}) ∩
      (({u : R3 | 0 < u 1} ∩ {u : R3 | u 1 < Real.pi}) ∩ {u : R3 | 0 < u 2}))
  exact
    ((isOpen_lt continuous_const h0_cont).inter (isOpen_lt h0_cont continuous_const)).inter
      (((isOpen_lt continuous_const h1_cont).inter
          (isOpen_lt h1_cont continuous_const)).inter
        (isOpen_lt continuous_const h2_cont))

/-- Helper for Exercise 5.10: the inverse spherical-coordinate formula is smooth on the target. -/
lemma sphericalCoordinates_invFun_contDiffOn_target :
    ContDiffOn ℝ ω sphericalCoordinatesInvFun sphericalCoordinatesTargetSet := by
  -- Each inverse coordinate is an elementary product of smooth scalar functions.
  have h0 : ContDiff ℝ ω (fun u : R3 ↦ u 2 * Real.sin (u 1) * Real.cos (u 0)) := by
    fun_prop
  have h1 : ContDiff ℝ ω (fun u : R3 ↦ u 2 * Real.sin (u 1) * Real.sin (u 0)) := by
    fun_prop
  have h2 : ContDiff ℝ ω (fun u : R3 ↦ u 2 * Real.cos (u 1)) := by
    fun_prop
  -- Package the three smooth scalar coordinates into the Euclidean target `R3`.
  refine contDiffOn_piLp' (p := (2 : ENNReal)) ?_
  intro i
  fin_cases i
  · simpa [sphericalCoordinatesInvFun, PiLp.toLp_apply] using h0.contDiffOn
  · simpa [sphericalCoordinatesInvFun, PiLp.toLp_apply] using h1.contDiffOn
  · simpa [sphericalCoordinatesInvFun, PiLp.toLp_apply] using h2.contDiffOn

/-- Helper for Exercise 5.10: the inverse spherical-coordinate formula is continuous on the
target. -/
lemma sphericalCoordinates_continuousOn_invFun :
    ContinuousOn sphericalCoordinatesInvFun sphericalCoordinatesTargetSet := by
  -- Smoothness on the target immediately implies continuity there.
  exact sphericalCoordinates_invFun_contDiffOn_target.continuousOn

/-- Helper for Exercise 5.10: the real polar-coordinate chart is smooth at each point of its
source because its explicit inverse is smooth and has invertible derivative there. -/
lemma polarCoord_contDiffAt_of_mem_source {q : ℝ × ℝ} (hq : q ∈ polarCoord.source) :
    ContDiffAt ℝ ω polarCoord q := by
  -- Follow the Chapter 1 route: smoothness of the explicit inverse plus the inverse function
  -- theorem for local partial homeomorphisms.
  have hsymm : ContDiff ℝ ω polarCoord.symm := by
    change ContDiff ℝ ω
      (fun p : ℝ × ℝ ↦ (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    fun_prop
  have hq_target : q ∈ polarCoord.symm.target := hq
  exact polarCoord.symm.contDiffAt_symm hq_target
    (f₀' := (fderivPolarCoordSymm (polarCoord q)).toContinuousLinearEquivOfDetNeZero (by
      rw [det_fderivPolarCoordSymm]
      exact (polarCoord.map_source hq).1.ne'))
    (by
      simpa using hasFDerivAt_polarCoord_symm (polarCoord q))
    hsymm.contDiffAt

/-- Helper for Exercise 5.10: `Complex.arg` is analytic, hence smooth, at every slit-plane
point. -/
lemma complex_arg_contDiffAt_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ω Complex.arg z := by
  -- Rewrite the complex slit-plane chart through the real polar-coordinate chart.
  have hz_real : Complex.equivRealProd z ∈ polarCoord.source := by
    simpa [Complex.polarCoord_source] using hz
  have hreal : ContDiffAt ℝ ω polarCoord (Complex.equivRealProd z) := by
    exact polarCoord_contDiffAt_of_mem_source hz_real
  have hcomplex : ContDiffAt ℝ ω Complex.polarCoord z := by
    simpa [Complex.polarCoord] using hreal.comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  -- The argument is the second polar-coordinate component.
  have hEq : Complex.arg = fun w : ℂ ↦ (Complex.polarCoord w).2 := by
    funext w
    simp [Complex.polarCoord_apply]
  rw [hEq]
  simpa using contDiff_snd.contDiffAt.comp z hcomplex

/-- Helper for Exercise 5.10: `Complex.arg` is smooth on the canonical slit plane used by
spherical coordinates. -/
lemma Complex.arg_contDiffOn_slitPlane :
    ContDiffOn ℝ ω Complex.arg Complex.slitPlane := by
  -- The pointwise slit-plane smoothness upgrades immediately to `ContDiffOn`.
  intro z hz
  exact (complex_arg_contDiffAt_of_mem_slitPlane hz).contDiffWithinAt

/-- Helper for Exercise 5.10: the forward spherical-coordinate formula is smooth on the
source. -/
lemma sphericalCoordinates_arg_contDiffOn :
    ContDiffOn ℝ ω (fun x : R3 ↦ Complex.arg (Complex.mk (x 0) (x 1)))
      sphericalCoordinatesSourceSet := by
  -- The planar projection into `ℂ` is globally smooth in the Euclidean coordinates.
  have hplanar : ContDiff ℝ ω (fun x : R3 ↦ Complex.mk (x 0) (x 1)) := by
    have hcoord0 : ContDiff ℝ ω (fun x : R3 ↦ ((x 0 : ℝ) : ℂ)) := by
      simpa using
        (Complex.ofRealCLM.contDiff.comp
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := (0 : Fin 3))))
    have hcoord1 : ContDiff ℝ ω (fun x : R3 ↦ ((x 1 : ℝ) : ℂ)) := by
      simpa using
        (Complex.ofRealCLM.contDiff.comp
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := (1 : Fin 3))))
    simpa [Complex.mk_eq_add_mul_I] using hcoord0.add (hcoord1.mul contDiff_const)
  -- Compose the slit-plane smoothness of `Complex.arg` with that planar projection.
  refine Complex.arg_contDiffOn_slitPlane.comp hplanar.contDiffOn ?_
  intro x hx
  exact sphericalCoordinates_source_mem_slitPlane hx

/-- Helper for Exercise 5.10: the forward spherical-coordinate formula is smooth on the
source. -/
lemma sphericalCoordinates_contDiffOn_toFun :
    ContDiffOn ℝ ω sphericalCoordinatesToFun sphericalCoordinatesSourceSet := by
  -- Build the radial coordinate and the normalized height separately before applying `arccos`.
  have hnorm : ContDiffOn ℝ ω (fun x : R3 ↦ ‖x‖) sphericalCoordinatesSourceSet := by
    simpa using
      (contDiff_id.contDiffOn.norm (𝕜 := ℝ) fun x hx ↦
        norm_ne_zero_iff.mp (sphericalCoordinates_source_norm_pos hx).ne')
  have hratio : ContDiffOn ℝ ω (fun x : R3 ↦ x 2 / ‖x‖) sphericalCoordinatesSourceSet := by
    have hcoord2 : ContDiff ℝ ω (fun x : R3 ↦ x 2) := by
      simpa using
        (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := (2 : Fin 3)))
    exact hcoord2.contDiffOn.div hnorm fun x hx =>
      (sphericalCoordinates_source_norm_pos hx).ne'
  have hincl :
      ContDiffOn ℝ ω (fun x : R3 ↦ Real.arccos (x 2 / ‖x‖)) sphericalCoordinatesSourceSet := by
    refine Real.contDiffOn_arccos.comp hratio ?_
    intro x hx
    exact sphericalCoordinates_source_ratio_mem_endpoint_compl hx
  -- Package the three smooth scalar coordinates into the Euclidean target `R3`.
  refine contDiffOn_piLp' (p := (2 : ENNReal)) ?_
  intro i
  fin_cases i
  · simpa [sphericalCoordinatesToFun, PiLp.toLp_apply] using sphericalCoordinates_arg_contDiffOn
  · simpa [sphericalCoordinatesToFun, PiLp.toLp_apply] using hincl
  · simpa [sphericalCoordinatesToFun, PiLp.toLp_apply] using hnorm

/-- Helper for Exercise 5.10: the forward spherical-coordinate formula is continuous on the
source. -/
lemma sphericalCoordinates_continuousOn_toFun :
    ContinuousOn sphericalCoordinatesToFun sphericalCoordinatesSourceSet := by
  -- Smoothness on the source immediately implies continuity there.
  exact sphericalCoordinates_contDiffOn_toFun.continuousOn

/-- The standard spherical-coordinate chart on `ℝ³`, with coordinate order
`(azimuth, inclination, radius)` and the usual branch cut along the nonpositive `x`-axis. -/
def sphericalCoordinates : OpenPartialHomeomorph R3 R3 where
  toFun := sphericalCoordinatesToFun
  invFun := sphericalCoordinatesInvFun
  source := sphericalCoordinatesSourceSet
  target := sphericalCoordinatesTargetSet
  map_source' := fun _ hx ↦ sphericalCoordinates_map_source hx
  map_target' := fun _ hy ↦ sphericalCoordinates_map_target hy
  left_inv' := fun _ hx ↦ sphericalCoordinates_right_inv hx
  right_inv' := fun _ hy ↦ sphericalCoordinates_left_inv hy
  open_source := sphericalCoordinates_open_source
  open_target := sphericalCoordinates_open_target
  continuousOn_toFun := sphericalCoordinates_continuousOn_toFun
  continuousOn_invFun := sphericalCoordinates_continuousOn_invFun

/-- The spherical-coordinate chart records azimuth, inclination, and radius in that order. -/
@[simp]
theorem sphericalCoordinates_apply (x : R3) :
    sphericalCoordinates x =
      WithLp.toLp 2
        ![Complex.arg (Complex.mk (x 0) (x 1)), Real.arccos (x 2 / ‖x‖), ‖x‖] := by
  -- The bundled chart uses the raw forward formula.
  rfl

/-- Helper for Exercise 5.10: the inverse spherical-coordinate map rebuilds a point from
azimuth, inclination, and radius. -/
@[simp]
theorem sphericalCoordinates_symm_apply (u : R3) :
    sphericalCoordinates.symm u =
      WithLp.toLp 2
        ![u 2 * Real.sin (u 1) * Real.cos (u 0),
          u 2 * Real.sin (u 1) * Real.sin (u 0),
          u 2 * Real.cos (u 1)] := by
  -- The inverse chart is exactly the raw inverse formula.
  rfl

/-- The source of the spherical-coordinate chart is the complement of the branch cut together with
the `z`-axis. -/
@[simp]
theorem sphericalCoordinates_source :
    sphericalCoordinates.source = {x : R3 | 0 < x 0 ∨ x 1 ≠ 0} := by
  -- Unfold the bundled source back to the raw source set.
  rfl

/-- The target of the spherical-coordinate chart consists of the usual open azimuth-inclination-
radius region. -/
@[simp]
theorem sphericalCoordinates_target :
    sphericalCoordinates.target =
      {u : R3 |
        u 0 ∈ Ioo (-Real.pi) Real.pi ∧ u 1 ∈ Ioo (0 : ℝ) Real.pi ∧ 0 < u 2} := by
  -- Unfold the bundled target back to the raw target set.
  rfl

/-- Helper for Exercise 5.10: the inverse spherical-coordinate map has norm squared equal to the
square of the radius coordinate. -/
lemma sphericalCoordinates_symm_norm_sq (u : R3) :
    ‖sphericalCoordinates.symm u‖ ^ 2 = u 2 ^ 2 := by
  -- This is the raw inverse norm computation specialized to the bundled chart.
  change ‖sphericalCoordinatesInvFun u‖ ^ 2 = u 2 ^ 2
  exact sphericalCoordinatesInvFun_norm_sq u

/-- Helper for Exercise 5.10: in the restricted spherical-coordinate chart, the unit sphere is
cut out by the equation `r = 1` on the target side. -/
lemma sphericalCoordinates_restrOpen_symm_mem_unitSphere2_iff
    {U : Set R3} (hU_open : IsOpen U) {u : R3}
    (hu : u ∈ (sphericalCoordinates.restrOpen U hU_open).target) :
    (sphericalCoordinates.restrOpen U hU_open).symm u ∈ unitSphere2 ↔ u 2 = 1 := by
  -- Reduce the sphere equation to the explicit inverse norm formula and use positivity of the
  -- target radius to choose the positive square root.
  have hu_restr :
      u ∈ sphericalCoordinates.target ∩ sphericalCoordinates.symm ⁻¹' U := by
    simpa [OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target] using hu
  have hu_target : u ∈ sphericalCoordinates.target := hu_restr.1
  have hu_target_data :
      u 0 ∈ Ioo (-Real.pi) Real.pi ∧ u 1 ∈ Ioo (0 : ℝ) Real.pi ∧ 0 < u 2 := by
    simpa [sphericalCoordinates_target] using hu_target
  have hu2_pos : 0 < u 2 := hu_target_data.2.2
  have hsymm_sq :
      ‖(sphericalCoordinates.restrOpen U hU_open).symm u‖ ^ 2 = u 2 ^ 2 := by
    simpa using sphericalCoordinates_symm_norm_sq u
  constructor
  · intro hu_sphere
    have hnorm :
        ‖(sphericalCoordinates.restrOpen U hU_open).symm u‖ = 1 := by
      change (sphericalCoordinates.restrOpen U hU_open).symm u ∈ Metric.sphere (0 : R3) 1 at hu_sphere
      simpa using (mem_sphere_iff_norm.1 hu_sphere)
    have hu2_sq : u 2 ^ 2 = 1 := by
      calc
        u 2 ^ 2 = ‖(sphericalCoordinates.restrOpen U hU_open).symm u‖ ^ 2 := by
          simpa using hsymm_sq.symm
        _ = 1 := by rw [hnorm]; norm_num
    nlinarith
  · intro hu_radius
    have hnorm_sq :
        ‖(sphericalCoordinates.restrOpen U hU_open).symm u‖ ^ 2 = 1 := by
      simpa [hu_radius] using hsymm_sq
    have hnorm :
        ‖(sphericalCoordinates.restrOpen U hU_open).symm u‖ = 1 := by
      refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp ?_
      simpa using hnorm_sq
    change (sphericalCoordinates.restrOpen U hU_open).symm u ∈ Metric.sphere (0 : R3) 1
    have hdist : ‖(sphericalCoordinates.restrOpen U hU_open).symm u - (0 : R3)‖ = 1 := by
      simpa using hnorm
    exact mem_sphere_iff_norm.2 hdist

/-- Helper for Exercise 5.10: fixing the last coordinate in `ℝ³` produces a Euclidean
`2`-slice. -/
lemma target_last_coordinate_eq_const_isEuclideanSlice
    (V : Set R3) (c : ℝ) :
    {u ∈ V | u 2 = c}.IsEuclideanSlice V 2 := by
  refine ⟨by decide, fun _ ↦ c, ?_⟩
  -- For `k = 2` in `ℝ³`, the only constrained tail coordinate is the third coordinate.
  ext u
  constructor
  · intro hu
    rcases hu with ⟨huV, hu2⟩
    constructor
    · exact huV
    · intro i
      fin_cases i
      simpa [Set.euclideanSlice] using hu2
  · intro hu
    rcases hu with ⟨huV, huTail⟩
    constructor
    · exact huV
    · simpa [Set.euclideanSlice] using huTail 0

/-- Exercise 5.10: on any open subset of the standard spherical-coordinate domain, the restricted
chart cuts out the unit sphere by the explicit coordinate equation `r = 1`. -/
theorem sphericalCoordinates_restrOpen_image_unitSphere2_eq_radiusOneSlice
    {U : Set R3} (hU_open : IsOpen U) :
    (sphericalCoordinates.restrOpen U hU_open) '' (unitSphere2 ∩
      (sphericalCoordinates.restrOpen U hU_open).source) =
      {u ∈ (sphericalCoordinates.restrOpen U hU_open).target | u 2 = 1} := by
  let e := sphericalCoordinates.restrOpen U hU_open
  -- Transport the sphere through the restricted chart, then rewrite the target-side condition
  -- using the explicit inverse formula.
  calc
    e '' (unitSphere2 ∩ e.source) = e.target ∩ e.symm ⁻¹' unitSphere2 := by
      rw [inter_comm, e.image_source_inter_eq']
    _ = {u ∈ e.target | u 2 = 1} := by
      ext u
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hu, hu_sphere⟩
        exact ⟨hu, (sphericalCoordinates_restrOpen_symm_mem_unitSphere2_iff hU_open hu).1 hu_sphere⟩
      · rintro ⟨hu, hu_radius⟩
        exact ⟨hu, (sphericalCoordinates_restrOpen_symm_mem_unitSphere2_iff hU_open hu).2 hu_radius⟩

/-- Helper for Exercise 5.10: after restricting spherical coordinates to an open subset, the
image of the unit sphere is a Euclidean `2`-slice in the chart target. -/
lemma sphericalCoordinates_restrOpen_image_unitSphere2_isEuclideanSlice
    {U : Set R3} (hU_open : IsOpen U) :
    ((sphericalCoordinates.restrOpen U hU_open) '' (unitSphere2 ∩
      (sphericalCoordinates.restrOpen U hU_open).source)).IsEuclideanSlice
      (sphericalCoordinates.restrOpen U hU_open).target 2 := by
  -- The previous theorem identifies the image with a single-coordinate slice `r = 1`.
  rw [sphericalCoordinates_restrOpen_image_unitSphere2_eq_radiusOneSlice hU_open]
  exact target_last_coordinate_eq_const_isEuclideanSlice
    ((sphericalCoordinates.restrOpen U hU_open).target) 1

/-- Helper for Exercise 5.10: the inverse spherical-coordinate formula is smooth on the target. -/
lemma sphericalCoordinates_contDiffOn_invFun :
    ContDiffOn ℝ ω sphericalCoordinatesInvFun sphericalCoordinatesTargetSet := by
  -- Reuse the earlier smoothness proof used to certify continuity of the inverse chart map.
  exact sphericalCoordinates_invFun_contDiffOn_target

/-- Helper for Exercise 5.10: the spherical-coordinate chart lies in the smooth groupoid. -/
lemma sphericalCoordinates_mem_contDiffGroupoid :
    sphericalCoordinates ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 3) := by
  -- As in Exercise 4.24, rewrite the bundled chart and inverse back to the explicit formulas.
  have hforward :
      ContDiffOn ℝ ω sphericalCoordinates sphericalCoordinates.source := by
    change ContDiffOn ℝ ω sphericalCoordinatesToFun sphericalCoordinatesSourceSet
    exact sphericalCoordinates_contDiffOn_toFun
  have hbackward :
      ContDiffOn ℝ ω sphericalCoordinates.symm sphericalCoordinates.target := by
    change ContDiffOn ℝ ω sphericalCoordinatesInvFun sphericalCoordinatesTargetSet
    exact sphericalCoordinates_contDiffOn_invFun
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  constructor
  · simpa [modelWithCornersSelf_coe] using hforward
  · simpa [modelWithCornersSelf_coe] using hbackward

/-- Helper for Exercise 5.10: the unrestricted spherical-coordinate chart already belongs to the
smooth maximal atlas of `R3`. -/
lemma sphericalCoordinates_mem_maximalAtlas :
    sphericalCoordinates ∈ IsManifold.maximalAtlas (𝓡 3) (⊤ : WithTop ℕ∞) R3 := by
  -- Maximal-atlas membership is the standard bridge from smooth groupoid membership.
  exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 3)).mem_maximalAtlas_of_mem_groupoid
    sphericalCoordinates_mem_contDiffGroupoid

/-- Helper for Exercise 5.10: on an open set, the generic restriction constructor agrees with the
open restriction used in the statement. -/
lemma sphericalCoordinates_restr_eq_restrOpen
    {U : Set R3} (hU_open : IsOpen U) :
    sphericalCoordinates.restr U = sphericalCoordinates.restrOpen U hU_open := by
  -- Make the `interior U = U` normalization explicit so later atlas rewrites stay low-whnf.
  simp [OpenPartialHomeomorph.restr, hU_open.interior_eq]

/-- Helper for Exercise 5.10: once the spherical-coordinate chart is known to be smooth, its
restriction to any open subset belongs to the smooth maximal atlas of `R3`. -/
lemma sphericalCoordinates_restrOpen_mem_maximalAtlas
    {U : Set R3} (hU_open : IsOpen U) :
    sphericalCoordinates.restrOpen U hU_open ∈
      IsManifold.maximalAtlas (𝓡 3) (⊤ : WithTop ℕ∞) R3 := by
  -- Restrict the already-certified smooth chart and then rewrite `restr` to `restrOpen`.
  simpa [sphericalCoordinates_restr_eq_restrOpen hU_open] using
    restr_mem_maximalAtlas
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 3))
      sphericalCoordinates_mem_maximalAtlas
      hU_open

/-- Consequently, the restricted spherical-coordinate chart is a smooth `2`-slice chart for the
unit sphere. -/
theorem sphericalCoordinates_restrOpen_isSliceChart_unitSphere2
    {U : Set R3} (hU_open : IsOpen U) :
    (sphericalCoordinates.restrOpen U hU_open).IsSliceChart unitSphere2 2 := by
  -- Combine the geometric slice computation with the remaining maximal-atlas membership lemma.
  refine ⟨sphericalCoordinates_restrOpen_mem_maximalAtlas hU_open, ?_⟩
  exact sphericalCoordinates_restrOpen_image_unitSphere2_isEuclideanSlice hU_open
