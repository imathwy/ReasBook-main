module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

open Set

namespace AlexanderHornGeometry

/-- Helper for Example 63.2: the Euclidean coordinate space used for the finite horn stages. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Helper for Example 63.2: the radial coordinate in the first two Euclidean coordinates. -/
noncomputable def radialCoordinate (p : Space) : ℝ :=
  Real.sqrt (p 0 ^ 2 + p 1 ^ 2)

/-- Helper for Example 63.2: the standard round core circle in Euclidean three-space. -/
def roundCore : Set Space :=
  {p | radialCoordinate p = 1 ∧ p 2 = 0}

/-- Helper for Example 63.2: membership in the round core is exactly the radial and height
coordinate equations used to define it. -/
lemma mem_roundCore_iff (p : Space) :
    p ∈ roundCore ↔ radialCoordinate p = 1 ∧ p 2 = 0 := by
  -- Expose the defining equations through a stable owner-level rewrite lemma.
  rfl

/-- Helper for Example 63.2: the equation-defined round core lies on the ambient unit sphere. -/
lemma roundCore_subset_unitSphere : roundCore ⊆ Metric.sphere (0 : Space) 1 := by
  -- Square the radial equation, then add the vanishing third coordinate to obtain unit norm.
  intro p hp
  rw [mem_sphere_zero_iff_norm]
  have hradialSq := congrArg (fun x : ℝ ↦ x ^ 2) (mem_roundCore_iff p |>.mp hp).1
  unfold radialCoordinate at hradialSq
  rw [Real.sq_sqrt (by positivity)] at hradialSq
  have hheight := (mem_roundCore_iff p |>.mp hp).2
  have hnormSq : ‖p‖ ^ 2 = (1 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ, hheight, hradialSq]
  exact (sq_eq_sq₀ (norm_nonneg p) zero_le_one).mp hnormSq

/-- Helper for Example 63.2: the complex displacement whose zero set is the round core. -/
noncomputable def roundCoreSignal (p : Space) : ℂ :=
  (radialCoordinate p - 1 : ℂ) + (p 2 : ℂ) * Complex.I

/-- Helper for Example 63.2: the round-core signal vanishes exactly on the core circle. -/
lemma roundCoreSignal_eq_zero_iff (p : Space) :
    roundCoreSignal p = 0 ↔ p ∈ roundCore := by
  -- Read the real and imaginary coordinates of the signal separately.
  constructor
  · intro hsignal
    have hcoords := Complex.ext_iff.mp hsignal
    simp only [roundCoreSignal, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, sub_zero, add_zero, Complex.zero_re, Complex.add_im,
      Complex.sub_im, Complex.one_im, Complex.mul_I_im, mul_one, zero_add,
      Complex.zero_im] at hcoords
    exact ⟨sub_eq_zero.mp hcoords.1, hcoords.2⟩
  · rintro ⟨hradial, hheight⟩
    -- Both displacement coordinates vanish on the displayed round circle.
    simp only [roundCoreSignal, hradial, hheight, Complex.ofReal_one, Complex.ofReal_zero,
      sub_self, zero_mul, add_zero]

/-- Helper for Example 63.2: outside the round core, the signal is nonzero. -/
lemma roundCoreSignal_ne_zero {p : Space} (hp : p ∈ roundCoreᶜ) :
    roundCoreSignal p ≠ 0 := by
  -- Otherwise the zero-set characterization would put the point on the core.
  intro hzero
  exact hp ((roundCoreSignal_eq_zero_iff p).mp hzero)

/-- Helper for Example 63.2: normalizing the round-core signal produces a unit complex number. -/
lemma roundCorePhase_mem (p : (roundCoreᶜ : Set Space)) :
    ‖roundCoreSignal p / ‖roundCoreSignal p‖‖ = 1 := by
  -- The signal is nonzero on the complement, so its norm cancels in the quotient.
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self]
  exact norm_ne_zero_iff.mpr (roundCoreSignal_ne_zero p.property)

/-- Helper for Example 63.2: the normalized phase detector on the round-core complement. -/
noncomputable def roundCorePhase : (roundCoreᶜ : Set Space) → Circle :=
  fun p ↦ ⟨roundCoreSignal p / ‖roundCoreSignal p‖,
    mem_sphere_zero_iff_norm.mpr (roundCorePhase_mem p)⟩

/-- Helper for Example 63.2: the radial coordinate is continuous. -/
lemma continuous_radialCoordinate : Continuous radialCoordinate := by
  -- Coordinate evaluation, squaring, addition, and square root are continuous.
  unfold radialCoordinate
  fun_prop

/-- Helper for Example 63.2: the complex round-core signal is continuous. -/
lemma continuous_roundCoreSignal : Continuous roundCoreSignal := by
  -- Assemble the real radial displacement and vertical coordinate continuously.
  have hheight : Continuous (fun p : Space ↦ p 2) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) 2
  unfold roundCoreSignal
  exact ((Complex.continuous_ofReal.comp continuous_radialCoordinate).sub continuous_const).add
      ((Complex.continuous_ofReal.comp hheight).mul continuous_const)

/-- Helper for Example 63.2: the normalized phase detector is continuous. -/
lemma continuous_roundCorePhase : Continuous roundCorePhase := by
  -- Division is continuous because the signal never vanishes on this subtype.
  unfold roundCorePhase
  apply Continuous.subtype_mk
  exact (continuous_roundCoreSignal.comp continuous_subtype_val).div
    (Complex.continuous_ofReal.comp
      (continuous_roundCoreSignal.comp continuous_subtype_val).norm)
    (fun p ↦ Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (roundCoreSignal_ne_zero p.property)))

/-- Helper for Example 63.2: the standard coordinate parameterization of the round core. -/
def roundCoreParam (z : Circle) : Space :=
  WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, 0]

/-- Helper for Example 63.2: the quarter-radius normal meridian around the round core. -/
noncomputable def roundCoreMeridian (z : Circle) : Space :=
  WithLp.toLp 2 ![1 + (1 / 4 : ℝ) * (z : ℂ).re, 0,
    (1 / 4 : ℝ) * (z : ℂ).im]

/-- Helper for Example 63.2: the round-core parameterization is continuous. -/
lemma continuous_roundCoreParam : Continuous roundCoreParam := by
  -- Each Euclidean coordinate is a continuous real or imaginary projection.
  unfold roundCoreParam
  fun_prop

/-- Helper for Example 63.2: the normal-meridian parameterization is continuous. -/
lemma continuous_roundCoreMeridian : Continuous roundCoreMeridian := by
  -- Each Euclidean coordinate is assembled continuously from the circle coordinates.
  unfold roundCoreMeridian
  fun_prop

/-- Helper for Example 63.2: the meridian stays in the positive radial half-plane. -/
lemma roundCoreMeridian_radial_pos (z : Circle) :
    0 < 1 + (1 / 4 : ℝ) * (z : ℂ).re := by
  -- The real part of a unit complex number is at least `-1`.
  have hre : -1 ≤ (z : ℂ).re := by
    have habs : |(z : ℂ).re| ≤ ‖(z : ℂ)‖ := RCLike.abs_re_le_norm (z : ℂ)
    rw [Circle.norm_coe] at habs
    exact neg_le_of_abs_le habs
  linarith

/-- Helper for Example 63.2: the radial coordinate of the normal meridian has the expected
positive affine formula. -/
lemma radialCoordinate_roundCoreMeridian (z : Circle) :
    radialCoordinate (roundCoreMeridian z) =
      1 + (1 / 4 : ℝ) * (z : ℂ).re := by
  -- The second coordinate vanishes, and positivity removes the square-root absolute value.
  unfold radialCoordinate
  have hfirst : roundCoreMeridian z 0 = 1 + (1 / 4 : ℝ) * (z : ℂ).re := by
    simp only [roundCoreMeridian, PiLp.toLp_apply, Matrix.cons_val_zero]
  have hsecond : roundCoreMeridian z 1 = 0 := by
    simp only [roundCoreMeridian, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  rw [hfirst, hsecond]
  norm_num [Real.sqrt_sq_eq_abs, abs_of_pos (roundCoreMeridian_radial_pos z)]

/-- Helper for Example 63.2: the round-core signal restricts to a scaled identity on the
normal meridian. -/
lemma roundCoreSignal_roundCoreMeridian (z : Circle) :
    roundCoreSignal (roundCoreMeridian z) = (1 / 4 : ℂ) * (z : ℂ) := by
  -- Substitute the radial formula and compare the real and imaginary coordinates.
  apply Complex.ext
  · norm_num [roundCoreSignal, radialCoordinate_roundCoreMeridian]
  · norm_num [roundCoreSignal, roundCoreMeridian, PiLp.toLp_apply,
      Matrix.cons_val_two]

/-- Helper for Example 63.2: every normal-meridian point lies outside the round core. -/
lemma roundCoreMeridian_mem_compl (z : Circle) : roundCoreMeridian z ∈ roundCoreᶜ := by
  -- A core point would have zero signal, contradicting the scaled unit-circle formula.
  intro hz
  have hzero := (roundCoreSignal_eq_zero_iff (roundCoreMeridian z)).mpr hz
  rw [roundCoreSignal_roundCoreMeridian] at hzero
  have z_ne_zero : (z : ℂ) ≠ 0 := by
    rw [← norm_ne_zero_iff, Circle.norm_coe]
    norm_num
  exact (mul_ne_zero (by norm_num) z_ne_zero) hzero

/-- Helper for Example 63.2: the normal meridian regarded as a map into the round-core
complement. -/
noncomputable def roundCoreMeridianInComplement (z : Circle) : (roundCoreᶜ : Set Space) :=
  ⟨roundCoreMeridian z, roundCoreMeridian_mem_compl z⟩

/-- Helper for Example 63.2: the complement-valued normal meridian is continuous. -/
lemma continuous_roundCoreMeridianInComplement :
    Continuous roundCoreMeridianInComplement := by
  -- Continuity into the subtype follows from continuity of the ambient parameterization.
  exact continuous_roundCoreMeridian.subtype_mk _

/-- Helper for Example 63.2: the phase detector is exactly the identity on the normal
meridian. -/
lemma roundCorePhase_roundCoreMeridian (z : Circle) :
    roundCorePhase (roundCoreMeridianInComplement z) = z := by
  -- The signal is a positive scalar multiple of `z`, so normalization cancels the scalar.
  apply Circle.ext
  simp only [roundCorePhase, roundCoreMeridianInComplement,
    roundCoreSignal_roundCoreMeridian, norm_mul, Circle.norm_coe]
  norm_num

/-- Helper for Example 63.2: the explicit core parameterization has radial coordinate one. -/
lemma radialCoordinate_roundCoreParam (z : Circle) : radialCoordinate (roundCoreParam z) = 1 := by
  -- The radial square is the complex norm square of a unit-circle point.
  unfold radialCoordinate
  rw [show roundCoreParam z 0 = (z : ℂ).re by
    simp only [roundCoreParam, PiLp.toLp_apply, Matrix.cons_val_zero]]
  rw [show roundCoreParam z 1 = (z : ℂ).im by
    simp only [roundCoreParam, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]]
  rw [← Real.sqrt_one]
  congr 1
  simpa only [Real.sqrt_one, pow_two, Complex.normSq_apply] using Circle.normSq_coe z

/-- Helper for Example 63.2: every point of the explicit core parameterization lies on the
equation-defined round core. -/
lemma roundCoreParam_mem (z : Circle) : roundCoreParam z ∈ roundCore := by
  -- Combine the radial computation with the zero third coordinate.
  refine ⟨radialCoordinate_roundCoreParam z, ?_⟩
  norm_num [roundCoreParam, PiLp.toLp_apply, Matrix.cons_val_two]

/-- Helper for Example 63.2: the explicit core and meridian ranges are compact. -/
lemma linkedRoundCoreRanges_compact :
    IsCompact (Set.range roundCoreParam) ∧ IsCompact (Set.range roundCoreMeridian) := by
  -- Both ranges are continuous images of the compact unit circle.
  exact ⟨isCompact_range continuous_roundCoreParam,
    isCompact_range continuous_roundCoreMeridian⟩

/-- Helper for Example 63.2: the explicit core and normal-meridian ranges are disjoint. -/
lemma linkedRoundCoreRanges_disjoint :
    Disjoint (Set.range roundCoreParam) (Set.range roundCoreMeridian) := by
  -- Core points have zero signal, while every meridian point has nonzero signal.
  rw [Set.disjoint_left]
  rintro p ⟨z, rfl⟩ ⟨w, hpw⟩
  have hcore : roundCoreParam z ∈ roundCore := roundCoreParam_mem z
  have hnotcore : roundCoreMeridian w ∉ roundCore := roundCoreMeridian_mem_compl w
  exact hnotcore (hpw ▸ hcore)

/-- Helper for Example 63.2: the explicit linked core ranges have a positive metric
clearance. -/
lemma linkedRoundCores_clearance :
    ∃ δ : NNReal, 0 < δ ∧
      ∀ x, x ∈ Set.range roundCoreParam →
        ∀ y, y ∈ Set.range roundCoreMeridian → (δ : ENNReal) < edist x y := by
  -- Compactness, closedness, and disjointness give a uniform positive separation.
  exact Metric.exists_pos_forall_lt_edist linkedRoundCoreRanges_compact.1
    linkedRoundCoreRanges_compact.2.isClosed linkedRoundCoreRanges_disjoint

end AlexanderHornGeometry
