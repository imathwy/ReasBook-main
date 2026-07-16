import DifferentialForms_Cartan_1970.cartan.VI.section26.«0018_Exercise_8».BoundaryTrace

open Set
open scoped UpperHalfPlane

noncomputable section

/-- A continuous extension of the Exercise 8 Abelian integral to the closed upper half-plane. -/
def IsExercise8Extension (k : Exercise8Modulus) (fbar : ClosedUpperHalfPlane → ℂ) : Prop :=
  Continuous fbar ∧
    ∀ z : UpperHalfPlane,
      fbar ⟨(z : ℂ), le_of_lt z.im_pos⟩ = exercise8_abel_integral k z

/-- Helper for Exercise 8: the strict upper half-plane includes canonically into the closed
upper half-plane. -/
def exercise8_closedUpperHalfPlane_of_upper (z : UpperHalfPlane) : ClosedUpperHalfPlane :=
  ⟨(z : ℂ), le_of_lt z.im_pos⟩

/-- Helper for Exercise 8: the strict upper slice is dense in the closed upper half-plane. -/
lemma exercise8_dense_upper_slice :
    DenseRange (exercise8_closedUpperHalfPlane_of_upper : UpperHalfPlane → ClosedUpperHalfPlane) :=
  by
  -- The source uniqueness step approximates each boundary point by moving a short vertical distance
  -- into the strict upper half-plane.
  rw [Metric.denseRange_iff]
  intro z r hr
  refine
    ⟨⟨(z : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I, ?_⟩, ?_⟩
  · -- Adding `i r/2` makes the imaginary part strictly positive while staying arbitrarily close.
    have hz_im : 0 ≤ ((z : ℂ)).im := z.2
    have hhalf_pos : 0 < r / 2 := by
      linarith
    have :
        0 < (((z : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I)).im := by
      simpa [Complex.add_im] using add_pos_of_nonneg_of_pos hz_im hhalf_pos
    exact this
  · -- In the subtype metric, the perturbation has size exactly `r / 2`.
    have hhalf_lt : |r| / 2 < r := by
      rw [abs_of_pos hr]
      linarith
    simpa [exercise8_closedUpperHalfPlane_of_upper, Subtype.dist_eq, dist_eq_norm] using hhalf_lt

/-- Helper for Exercise 8: a continuous extension to the closed upper half-plane is unique once it
agrees with the Abel integral on the strict upper slice. -/
lemma exercise8_extension_unique {k : Exercise8Modulus}
    {fbar gbar : ClosedUpperHalfPlane → ℂ}
    (hfbar : IsExercise8Extension k fbar) (hgbar : IsExercise8Extension k gbar) :
    fbar = gbar := by
  -- Route correction: the uniqueness part no longer waits on the boundary-value formulas; it is
  -- isolated as a dense-slice argument on `ClosedUpperHalfPlane`.
  refine exercise8_dense_upper_slice.equalizer hfbar.1 hgbar.1 ?_
  funext z
  simp [exercise8_closedUpperHalfPlane_of_upper, hfbar.2 z, hgbar.2 z]

/-- Helper for Exercise 8: a closed-upper-half-plane point off the real axis actually lies in the
strict upper half-plane. -/
lemma exercise8_im_pos_of_closed_nonreal {z : ClosedUpperHalfPlane} (hz : ((z : ℂ)).im ≠ 0) :
    0 < ((z : ℂ)).im := by
  -- In the closed half-plane, the only nonpositive imaginary value is `0`.
  exact lt_of_le_of_ne z.2 (Ne.symm hz)

/-- Helper for Exercise 8: the canonical owner on the closed half-plane uses the repaired boundary
trace on the real axis and the Abel integral in the interior. -/
def exercise8_closed_extension (k : Exercise8Modulus) : ClosedUpperHalfPlane → ℂ :=
  fun z ↦
    if hz : ((z : ℂ)).im = 0 then
      exercise8_boundary_trace k ((z : ℂ).re)
    else
      exercise8_abel_integral k ⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal hz⟩

/-- Helper for Exercise 8: the canonical closed-half-plane owner restricts to the repaired
boundary trace on the real axis. -/
@[simp] lemma exercise8_closed_extension_of_real (k : Exercise8Modulus) (x : ℝ) :
    exercise8_closed_extension k ⟨(x : ℂ), by simp⟩ = exercise8_boundary_trace k x := by
  -- The real-axis branch is selected because the imaginary part is exactly zero.
  simp [exercise8_closed_extension]

/-- Helper for Exercise 8: the canonical closed-half-plane owner agrees with the Abel integral on
the strict upper half-plane. -/
@[simp] lemma exercise8_closed_extension_of_upper (k : Exercise8Modulus) (z : UpperHalfPlane) :
    exercise8_closed_extension k ⟨(z : ℂ), le_of_lt z.im_pos⟩ = exercise8_abel_integral k z := by
  -- Off the real axis the definition picks the interior Abel-integral branch.
  have hz : (((⟨(z : ℂ), le_of_lt z.im_pos⟩ : ClosedUpperHalfPlane) : ℂ)).im ≠ 0 := ne_of_gt z.im_pos
  have hz0 : ¬ (((⟨(z : ℂ), le_of_lt z.im_pos⟩ : ClosedUpperHalfPlane) : ℂ)).im = 0 := hz
  have hSubtype :
      (⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal (z := ⟨(z : ℂ), le_of_lt z.im_pos⟩) hz⟩ :
        UpperHalfPlane) = z := by
    ext
    rfl
  by_cases hzero : (((⟨(z : ℂ), le_of_lt z.im_pos⟩ : ClosedUpperHalfPlane) : ℂ)).im = 0
  · exact False.elim (hz hzero)
  · rw [exercise8_closed_extension, dif_neg hzero]

/-- Helper for Exercise 8: the repaired boundary owner depends continuously on the real part of a
closed-half-plane point. -/
lemma exercise8_boundary_trace_re_continuous (k : Exercise8Modulus) :
    Continuous (fun z : ClosedUpperHalfPlane ↦ exercise8_boundary_trace k ((z : ℂ).re)) := by
  -- The real-axis owner is already continuous on `ℝ`, and `re` is continuous on the subtype.
  exact exercise8_boundary_trace_continuous k |>.comp (Complex.continuous_re.comp continuous_subtype_val)

/-- Helper for Exercise 8: on points with zero imaginary part, the canonical owner is the repaired
boundary trace. -/
lemma exercise8_closed_extension_eq_boundary_trace_of_im_zero {k : Exercise8Modulus}
    {z : ClosedUpperHalfPlane} (hz : ((z : ℂ)).im = 0) :
    exercise8_closed_extension k z = exercise8_boundary_trace k ((z : ℂ).re) := by
  -- The `if`-branch at `Im z = 0` is definitionally the real-axis owner.
  simp [exercise8_closed_extension, hz]

/-- Helper for Exercise 8: off the real axis, the canonical owner is the interior Abel integral. -/
lemma exercise8_closed_extension_eq_abel_integral_of_im_ne_zero {k : Exercise8Modulus}
    {z : ClosedUpperHalfPlane} (hz : ((z : ℂ)).im ≠ 0) :
    exercise8_closed_extension k z =
      exercise8_abel_integral k ⟨(z : ℂ), exercise8_im_pos_of_closed_nonreal hz⟩ := by
  -- Away from the boundary, the definition selects the interior primitive branch.
  simp [exercise8_closed_extension, hz]
