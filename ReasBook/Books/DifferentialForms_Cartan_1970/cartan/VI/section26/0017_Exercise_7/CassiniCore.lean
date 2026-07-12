import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0015_Remark_II_2_extra_6»
import DifferentialForms_Cartan_1970.III.section12.«0022_Exercise_10»
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»

open Metric Set ComplexOrder
open scoped ComplexConjugate

noncomputable section

/-- The interior of Cassini's oval `|z^2 - a^2| < r^2`. -/
def cassiniOvalInterior (a r : ℝ) : Set ℂ :=
  {z | ‖z ^ 2 - (a : ℂ) ^ 2‖ < r ^ 2}

/-- Membership in the interior of Cassini's oval is the norm inequality `|z^2 - a^2| < r^2`. -/
theorem mem_cassiniOvalInterior {a r : ℝ} {z : ℂ} :
    z ∈ cassiniOvalInterior a r ↔ ‖z ^ 2 - (a : ℂ) ^ 2‖ < r ^ 2 := by
  -- This is the defining predicate of `cassiniOvalInterior`.
  rfl

/-- The interior of Cassini's oval is open. -/
theorem isOpen_cassiniOvalInterior (a r : ℝ) : IsOpen (cassiniOvalInterior a r) := by
  simpa [cassiniOvalInterior] using
    isOpen_lt
      (continuous_norm.comp
        (show Continuous (fun z : ℂ ↦ z ^ 2 - (a : ℂ) ^ 2) by fun_prop))
      continuous_const

/-- The right half `D⁺` of the interior of Cassini's oval. -/
def cassiniOvalRightHalf (a r : ℝ) : Set ℂ :=
  {z | z ∈ cassiniOvalInterior a r ∧ 0 < z.re}

/-- Membership in `D⁺` means lying in the Cassini interior and having positive real part. -/
theorem mem_cassiniOvalRightHalf {a r : ℝ} {z : ℂ} :
    z ∈ cassiniOvalRightHalf a r ↔ z ∈ cassiniOvalInterior a r ∧ 0 < z.re := by
  -- This is the defining predicate of `cassiniOvalRightHalf`.
  rfl

/-- The right half of the Cassini interior is open. -/
theorem isOpen_cassiniOvalRightHalf (a r : ℝ) : IsOpen (cassiniOvalRightHalf a r) := by
  simpa [cassiniOvalRightHalf] using
    (isOpen_cassiniOvalInterior a r).inter (isOpen_lt continuous_const Complex.continuous_re)

/-- The right half `B⁺` of the open unit disc. -/
def rightHalfUnitDisc : Set ℂ :=
  ball (0 : ℂ) 1 ∩ {w | 0 < w.re}

/-- Membership in `B⁺` means lying in the unit disc and having positive real part. -/
theorem mem_rightHalfUnitDisc {w : ℂ} :
    w ∈ rightHalfUnitDisc ↔ w ∈ ball (0 : ℂ) 1 ∧ 0 < w.re := by
  simp [rightHalfUnitDisc]

/-- The right half of the open unit disc is open. -/
theorem isOpen_rightHalfUnitDisc : IsOpen rightHalfUnitDisc := by
  exact isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

/-- The segment of the imaginary axis contained in the Cassini oval, written as `iy` with
`y^2 ≤ r^2 - a^2`. -/
def cassiniOvalImaginaryAxisSegment (a r : ℝ) : Set ℂ :=
  {z | z.re = 0 ∧ z.im ^ 2 ≤ r ^ 2 - a ^ 2}

/-- Membership in the imaginary-axis segment is the stated real-part and quadratic bound. -/
theorem mem_cassiniOvalImaginaryAxisSegment {a r : ℝ} {z : ℂ} :
    z ∈ cassiniOvalImaginaryAxisSegment a r ↔ z.re = 0 ∧ z.im ^ 2 ≤ r ^ 2 - a ^ 2 := by
  -- This is the defining predicate of the Cassini imaginary-axis segment.
  rfl

/-- The segment `iv`, `|v| ≤ 1`, of the imaginary axis in the `w`-plane. -/
def unitDiscImaginaryAxisSegment : Set ℂ :=
  {w | w.re = 0 ∧ ‖w‖ ≤ 1}

/-- Membership in the unit-disc imaginary-axis segment is the stated real-part and norm bound. -/
theorem mem_unitDiscImaginaryAxisSegment {w : ℂ} :
    w ∈ unitDiscImaginaryAxisSegment ↔ w.re = 0 ∧ ‖w‖ ≤ 1 := by
  -- This is the defining predicate of the unit-disc imaginary-axis segment.
  rfl

/-- The real slice of the interior of Cassini's oval. -/
def cassiniOvalInteriorRealSlice (a r : ℝ) : Set ℂ :=
  {z | z ∈ cassiniOvalInterior a r ∧ z.im = 0}

/-- Membership in the real slice of Cassini's oval means lying in the interior with zero
imaginary part. -/
theorem mem_cassiniOvalInteriorRealSlice {a r : ℝ} {z : ℂ} :
    z ∈ cassiniOvalInteriorRealSlice a r ↔ z ∈ cassiniOvalInterior a r ∧ z.im = 0 := by
  -- This is the defining predicate of the real slice.
  rfl

/-- The real slice of the open unit disc. -/
def openUnitDiscRealSlice : Set ℂ :=
  {w | w ∈ ball (0 : ℂ) 1 ∧ w.im = 0}

/-- Membership in the real slice of the unit disc means lying in the unit disc with zero
imaginary part. -/
theorem mem_openUnitDiscRealSlice {w : ℂ} :
    w ∈ openUnitDiscRealSlice ↔ w ∈ ball (0 : ℂ) 1 ∧ w.im = 0 := by
  -- This is the defining predicate of the real slice of the unit disc.
  rfl

/-- The Möbius transformation in the auxiliary variable `ζ = z^2` that sends the circle
`|ζ - a^2| = r^2` to the unit circle and the real segment `[a^2 - r^2, 0]` to `[-1, 0]`. -/
def cassiniOvalMobius (a r : ℝ) (ζ : ℂ) : ℂ :=
  ((r : ℂ) ^ 2 * ζ) / (((a : ℂ) ^ 2) * ζ + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))

/-- The auxiliary Möbius map sends `0` to `0`, matching the source segment normalization. -/
theorem cassiniOvalMobius_zero (a r : ℝ) :
    cassiniOvalMobius a r 0 = 0 := by
  simp [cassiniOvalMobius]

/-- The explicit right-half map from the Cassini oval hint: square, apply the Möbius transform,
then take the principal square root. -/
def cassiniOvalToUnitDisc (a r : ℝ) (z : ℂ) : ℂ :=
  Complex.sqrt (cassiniOvalMobius a r (z ^ 2))

/-- Helper for Exercise 7: on `0` or on the slit plane, the principal square root squares back to
the original number. -/
lemma sq_sqrt_of_mem_slitPlane_or_zero {Z : ℂ} (hZ : Z = 0 ∨ Z ∈ Complex.slitPlane) :
    Complex.sqrt Z ^ 2 = Z := by
  rcases hZ with rfl | hZ
  · -- At the origin the square-root branch is definitionally zero.
    simp
  · -- On the slit plane we can rewrite the principal square root by `exp (log Z / 2)`.
    have hZ0 : Z ≠ 0 := Complex.slitPlane_ne_zero hZ
    rw [sqrt_eq_exp hZ0, ← Complex.exp_nat_mul]
    ring_nf
    exact Complex.exp_log hZ0

/-- Helper for Exercise 7: every complex number lies either in `Complex.slitPlane` or on the
nonpositive real axis. -/
lemma mem_slitPlane_or_eq_neg_ofReal (Z : ℂ) :
    Z ∈ Complex.slitPlane ∨ ∃ x : ℝ, 0 ≤ x ∧ Z = -((x : ℂ)) := by
  by_cases him : Z.im = 0
  · by_cases hre : 0 < Z.re
    · -- A positive real number lies in the slit plane.
      left
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl hre
    · -- A real point outside the slit plane lies on the nonpositive real axis.
      right
      refine ⟨-Z.re, neg_nonneg.mpr (le_of_not_gt hre), ?_⟩
      apply Complex.ext <;> simp [him]
  · -- Any point with nonzero imaginary part lies in the slit plane.
    left
    rw [Complex.mem_slitPlane_iff]
    exact Or.inr him

/-- Helper for Exercise 7: on the slit plane or on the nonpositive real axis, the principal square
root squares back to the original number. -/
lemma sq_sqrt_of_mem_slitPlane_or_nonpos_real {Z : ℂ}
    (hZ : Z ∈ Complex.slitPlane ∨ ∃ x : ℝ, 0 ≤ x ∧ Z = -((x : ℂ))) :
    Complex.sqrt Z ^ 2 = Z := by
  rcases hZ with hZ | ⟨x, hx, rfl⟩
  · -- On the slit plane this is the standard principal-branch identity.
    exact sq_sqrt_of_mem_slitPlane_or_zero (Or.inr hZ)
  · -- On the nonpositive real axis, use the explicit formula `sqrt (-x) = I * sqrt x`.
    have hnonneg : 0 ≤ (x : ℂ) := by
      exact_mod_cast hx
    have hx_mem : (x : ℂ) = 0 ∨ (x : ℂ) ∈ Complex.slitPlane := by
      by_cases hx0 : x = 0
      · left
        simp [hx0]
      · right
        rw [Complex.ofReal_mem_slitPlane]
        exact lt_of_le_of_ne hx (Ne.symm hx0)
    calc
      Complex.sqrt (-((x : ℂ))) ^ 2 = (Complex.I * Complex.sqrt (x : ℂ)) ^ 2 := by
        rw [Complex.sqrt_neg_of_nonneg hnonneg]
      _ = Complex.I ^ 2 * (Complex.sqrt (x : ℂ)) ^ 2 := by
        ring
      _ = -((x : ℂ)) := by
        simp [sq_sqrt_of_mem_slitPlane_or_zero hx_mem]

/-- Helper for Exercise 7: the principal square root squares back to its argument for every
complex number. -/
lemma sq_sqrt_complex (Z : ℂ) : Complex.sqrt Z ^ 2 = Z := by
  -- Split the argument into the slit-plane branch and the nonpositive-real branch.
  exact sq_sqrt_of_mem_slitPlane_or_nonpos_real (mem_slitPlane_or_eq_neg_ofReal Z)

/-- On the source domain, squaring `cassiniOvalToUnitDisc` recovers the auxiliary Möbius
transform of `z^2`. -/
theorem cassiniOvalToUnitDisc_sq {a r : ℝ} {z : ℂ}
    (hz : z ∈ cassiniOvalInterior a r) :
    cassiniOvalToUnitDisc a r z ^ 2 = cassiniOvalMobius a r (z ^ 2) := by
  -- Record the domain hypothesis so the theorem remains source-facing even though this algebraic
  -- square identity is pointwise.
  let _ := hz
  -- The `ζ`-plane branch reduces to the universal identity `(sqrt Z)^2 = Z`.
  simpa [cassiniOvalToUnitDisc] using sq_sqrt_complex (cassiniOvalMobius a r (z ^ 2))

/-- The inverse map obtained by solving the Möbius relation for `z^2` and again taking the
principal square root. -/
def unitDiscToCassiniOval (a r : ℝ) (w : ℂ) : ℂ :=
  Complex.sqrt
    ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))

/-- On the unit disc, squaring `unitDiscToCassiniOval` gives the solved expression for `z^2`. -/
theorem unitDiscToCassiniOval_sq {a r : ℝ} {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) :
    unitDiscToCassiniOval a r w ^ 2 =
      (((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2) := by
  -- Record the source-disc hypothesis so the theorem keeps the intended package interface.
  let _ := hw
  -- The solved inverse branch uses the same universal square-root identity.
  unfold unitDiscToCassiniOval
  exact
    sq_sqrt_complex
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))

/-- Helper for Exercise 7: the source Möbius normalization is exactly the unit-disc
uncentering map applied to the affine coordinate `η = (ζ - a^2) / r^2`. -/
lemma cassiniOvalMobius_eq_discUncenter_normalized
    (a r : ℝ) (hr : r ≠ 0) (ζ : ℂ) :
    cassiniOvalMobius a r ζ =
      discUncenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ))
        ((ζ - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) := by
  -- Clear the common denominator `r^2` and compare the rational forms directly.
  have hR : ((r : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hr)
  have hc :
      ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) = ((a : ℂ) ^ 2) / ((r : ℂ) ^ 2) := by
    rw [Complex.ofReal_div]
    simp
  unfold cassiniOvalMobius discUncenter discCenter
  rw [hc]
  simp [pow_two, div_eq_mul_inv]
  field_simp [hR]
  ring_nf

/-- Helper for Exercise 7: the inverse square argument is the affine recentering of the unit-disc
centering automorphism. -/
lemma unitDiscToCassiniOval_sq_arg_eq_affine_discCenter
    (a r : ℝ) (hr : r ≠ 0) (Z : ℂ)
    (hden : ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * Z ≠ 0) :
    ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * Z) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * Z)) =
      (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) Z := by
  -- Route correction: rewrite the raw quotient as `a^2 + r^2 * discCenter c Z`.
  have hR : ((r : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hr)
  have hc :
      ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) = ((a : ℂ) ^ 2) / ((r : ℂ) ^ 2) := by
    rw [Complex.ofReal_div]
    simp
  rw [hc]
  unfold discCenter
  simp [pow_two, div_eq_mul_inv]
  field_simp [hR, hden]
  ring_nf

/-- Helper for Exercise 7: the normalized square coordinate `η = (z^2 - a^2) / r^2` lands in the
open unit disc for every point of the right-half Cassini interior. -/
lemma normalized_square_mem_unit_ball_of_mem_rightHalf
    {a r : ℝ} {z : ℂ} (hz : z ∈ cassiniOvalRightHalf a r) :
    ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) ∈ ball (0 : ℂ) 1 := by
  rcases mem_cassiniOvalRightHalf.mp hz with ⟨hzCassini, hzre⟩
  let _ := hzre
  have hz_norm :
      ‖z ^ 2 - (a : ℂ) ^ 2‖ < r ^ 2 := (mem_cassiniOvalInterior.mp hzCassini)
  have hr_sq_pos : 0 < r ^ 2 := by
    nlinarith [norm_nonneg (z ^ 2 - (a : ℂ) ^ 2), hz_norm]
  have hR_norm : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    calc
      ‖(r : ℂ) ^ 2‖ = ‖(r : ℂ)‖ ^ 2 := by rw [norm_pow]
      _ = |r| ^ 2 := by simp
      _ = r ^ 2 := by simp [pow_two]
  have hη_norm :
      ‖(z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)‖ < 1 := by
    rw [norm_div, hR_norm]
    exact (div_lt_one hr_sq_pos).2 hz_norm
  exact mem_ball_zero_iff.2 hη_norm

/-- Helper for Exercise 7: the same normalized square coordinate lands in the open unit disc on
the full Cassini interior. -/
lemma normalized_square_mem_unit_ball_of_mem_cassiniOvalInterior
    {a r : ℝ} {z : ℂ} (hz : z ∈ cassiniOvalInterior a r) :
    ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) ∈ ball (0 : ℂ) 1 := by
  have hz_norm :
      ‖z ^ 2 - (a : ℂ) ^ 2‖ < r ^ 2 := mem_cassiniOvalInterior.mp hz
  have hr_sq_pos : 0 < r ^ 2 := by
    -- The interior inequality already forces the real scale `r^2` to be positive.
    nlinarith [norm_nonneg (z ^ 2 - (a : ℂ) ^ 2), hz_norm]
  have hR_norm : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    calc
      ‖(r : ℂ) ^ 2‖ = ‖(r : ℂ)‖ ^ 2 := by rw [norm_pow]
      _ = |r| ^ 2 := by simp
      _ = r ^ 2 := by simp [pow_two]
  have hη_norm :
      ‖(z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)‖ < 1 := by
    rw [norm_div, hR_norm]
    exact (div_lt_one hr_sq_pos).2 hz_norm
  exact mem_ball_zero_iff.2 hη_norm

/-- Helper for Exercise 7: under `0 < a < r`, the inverse Möbius denominator has no pole on the
open unit disc. -/
lemma unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball
    {a r : ℝ} (ha : 0 < a) (har : a < r) {Z : ℂ} (hZ : Z ∈ ball (0 : ℂ) 1) :
    ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * Z ≠ 0 := by
  have hZ_lt : ‖Z‖ < 1 := mem_ball_zero_iff.mp hZ
  have ha_sq_lt : a ^ 2 < r ^ 2 := by
    nlinarith
  have hR_norm : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    calc
      ‖(r : ℂ) ^ 2‖ = ‖(r : ℂ)‖ ^ 2 := by rw [norm_pow]
      _ = |r| ^ 2 := by simp
      _ = r ^ 2 := by simp [pow_two]
  have hA_norm : ‖(a : ℂ) ^ 2‖ = a ^ 2 := by
    calc
      ‖(a : ℂ) ^ 2‖ = ‖(a : ℂ)‖ ^ 2 := by rw [norm_pow]
      _ = |a| ^ 2 := by simp
      _ = a ^ 2 := by simp [pow_two]
  have hAZ_lt : ‖((a : ℂ) ^ 2) * Z‖ < r ^ 2 := by
    rw [norm_mul, hA_norm]
    nlinarith [norm_nonneg Z, hZ_lt, sq_nonneg a, ha_sq_lt]
  intro hden
  have heq : ((r : ℂ) ^ 2) = ((a : ℂ) ^ 2) * Z := sub_eq_zero.mp hden
  have : r ^ 2 < r ^ 2 := by
    calc
      r ^ 2 = ‖(r : ℂ) ^ 2‖ := by simp [hR_norm]
      _ = ‖((a : ℂ) ^ 2) * Z‖ := by simp [heq]
      _ < r ^ 2 := hAZ_lt
  exact (lt_irrefl _ this)

/-- Helper for Exercise 7: the disc automorphism owner already gives the inverse relation
`discCenter c ∘ discUncenter c = id` on the unit disc. -/
lemma discCenter_discUncenter_eq_self_on_unit_ball
    {c u : ℂ} (hc : c ∈ ball (0 : ℂ) 1) (hu : u ∈ ball (0 : ℂ) 1) :
    discCenter c (discUncenter c u) = u := by
  have hneg : -c ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_neg] using hc
  -- Apply the upstream left-inverse statement at the parameter `-c`.
  simpa [discUncenter] using
    (disc_uncenter_leftInvOn_disc_center (a := -c) hneg hu)

/-- Helper for Exercise 7: if the normalized square coordinate is real at a point of the
right-half Cassini interior, then the source point lies on the real axis and the normalized
coordinate stays to the right of `-a^2 / r^2`. -/
lemma normalized_square_real_case_of_mem_rightHalf
    {a r : ℝ} {z : ℂ} (hz : z ∈ cassiniOvalRightHalf a r)
    (hηim : (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))).im = 0) :
    z.im = 0 ∧ -((a ^ 2 / r ^ 2 : ℝ)) < (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))).re := by
  rcases mem_cassiniOvalRightHalf.mp hz with ⟨hzCassini, hzre⟩
  have hz_norm : ‖z ^ 2 - (a : ℂ) ^ 2‖ < r ^ 2 := mem_cassiniOvalInterior.mp hzCassini
  have hr_sq_pos : 0 < r ^ 2 := by
    -- The Cassini inequality forces the real denominator `r^2` to be positive.
    nlinarith [norm_nonneg (z ^ 2 - (a : ℂ) ^ 2), hz_norm]
  have hr_sq_ne : r ^ 2 ≠ 0 := by
    nlinarith
  have hηim' :
      (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))).im = (2 * z.re * z.im) / (r ^ 2) := by
    -- Rewrite the denominator as a real scalar and compute the imaginary part explicitly.
    rw [show ((r : ℂ) ^ 2) = (((r ^ 2 : ℝ) : ℂ)) by simp]
    simp [Complex.div_im, pow_two]
    field_simp [hr_sq_ne]
    ring
  have hz_im : z.im = 0 := by
    -- Since `z.re > 0`, the vanishing of `Im η` forces `z.im = 0`.
    rw [hηim'] at hηim
    have hmul : 2 * z.re * z.im = 0 := by
      exact (div_eq_zero_iff.mp hηim).resolve_right hr_sq_ne
    have hfactor : 2 * z.re ≠ 0 := by
      nlinarith
    exact mul_eq_zero.mp hmul |>.resolve_left hfactor
  have hηre :
      (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))).re = (z.re ^ 2 - a ^ 2) / (r ^ 2) := by
    -- On the real slice, the normalized square reduces to the real quotient.
    rw [show ((r : ℂ) ^ 2) = (((r ^ 2 : ℝ) : ℂ)) by simp]
    simp [Complex.div_re, pow_two, hz_im]
    field_simp [hr_sq_ne]
  refine ⟨hz_im, ?_⟩
  rw [hηre]
  have hzre_sq_pos : 0 < z.re ^ 2 := by
    positivity
  have hdiv : (-a ^ 2) / (r ^ 2) < (z.re ^ 2 - a ^ 2) / (r ^ 2) :=
    (div_lt_div_iff_of_pos_right hr_sq_pos).2 (by nlinarith [hzre_sq_pos])
  simpa [neg_div] using hdiv

/-- Helper for Exercise 7: squaring a point of the right half-disc stays in the unit disc and
lands in the slit plane, so the principal square-root branch can later be inverted there. -/
lemma square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc
    {w : ℂ} (hw : w ∈ rightHalfUnitDisc) :
    w ^ 2 ∈ ball (0 : ℂ) 1 ∧ w ^ 2 ∈ Complex.slitPlane := by
  rcases mem_rightHalfUnitDisc.mp hw with ⟨hw_ball, hw_re⟩
  have hw_norm : ‖w‖ < 1 := mem_ball_zero_iff.mp hw_ball
  have hsq_ball : w ^ 2 ∈ ball (0 : ℂ) 1 := by
    -- Squaring preserves the norm inequality `‖w‖ < 1`.
    rw [mem_ball_zero_iff, norm_pow]
    nlinarith [norm_nonneg w, hw_norm]
  have hw_sq_im : (w ^ 2).im = 2 * w.re * w.im := by
    -- Expand the square to read off the imaginary part.
    simp [pow_two]
    ring
  have hw_sq_re : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    -- Expand the square to read off the real part.
    simp [pow_two]
  have hsq_slit : w ^ 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases him : (w ^ 2).im = 0
    · left
      -- If the square is real, then `w` itself is real and its square is positive.
      have hw_im : w.im = 0 := by
        rw [hw_sq_im] at him
        have hmul : w.im * (2 * w.re) = 0 := by
          nlinarith
        have hfactor : 2 * w.re ≠ 0 := by
          nlinarith
        exact mul_eq_zero.mp hmul |>.resolve_right hfactor
      rw [hw_sq_re, hw_im]
      nlinarith
    · -- A nonreal square is automatically in the slit plane.
      right
      exact him
  exact ⟨hsq_ball, hsq_slit⟩

/-- Helper for Exercise 7: on the slit plane and inside the unit disc, the principal square root
lands in the right half of the unit disc. -/
lemma sqrt_mem_rightHalfUnitDisc_of_mem_ball_and_slitPlane
    {Z : ℂ} (hZball : Z ∈ ball (0 : ℂ) 1) (hZslit : Z ∈ Complex.slitPlane) :
    Complex.sqrt Z ∈ rightHalfUnitDisc := by
  have hsquare : Complex.sqrt Z ^ 2 = Z :=
    sq_sqrt_of_mem_slitPlane_or_zero (Or.inr hZslit)
  have hZ_norm : ‖Z‖ < 1 := mem_ball_zero_iff.mp hZball
  have hsqrt_ball : Complex.sqrt Z ∈ ball (0 : ℂ) 1 := by
    -- Compare norms after squaring to pull the unit-ball bound back through `sqrt`.
    rw [mem_ball_zero_iff]
    have hnorm_sq : ‖Complex.sqrt Z‖ ^ 2 = ‖Z‖ := by
      simpa [norm_pow] using congrArg norm hsquare
    nlinarith [norm_nonneg (Complex.sqrt Z), hZ_norm, hnorm_sq]
  have hsum_pos : 0 < ‖Z‖ + Z.re := by
    -- On the slit plane, either the real part is already positive or the norm strictly dominates
    -- its absolute value because the imaginary part is nonzero.
    rw [Complex.mem_slitPlane_iff] at hZslit
    rcases hZslit with hre | him
    · nlinarith [norm_nonneg Z, hre]
    · have hre_lt : |Z.re| < ‖Z‖ := (Complex.abs_re_lt_norm).2 him
      have hleft : -‖Z‖ < Z.re := (abs_lt.mp hre_lt).1
      nlinarith
  have hre_sqrt : (Complex.sqrt Z).re = Real.sqrt ((‖Z‖ + Z.re) / 2) := by
    -- The principal branch always has the canonical nonnegative real part.
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp
  rw [mem_rightHalfUnitDisc]
  refine ⟨hsqrt_ball, ?_⟩
  rw [hre_sqrt]
  have harg_pos : 0 < (‖Z‖ + Z.re) / 2 := by
    nlinarith
  exact Real.sqrt_pos.mpr harg_pos

/-- Helper for Exercise 7: the principal square root of a point in the unit disc still lies in
the unit disc because its square recovers the argument. -/
lemma sqrt_mem_ball_of_mem_ball {Z : ℂ} (hZball : Z ∈ ball (0 : ℂ) 1) :
    Complex.sqrt Z ∈ ball (0 : ℂ) 1 := by
  have hsquare : Complex.sqrt Z ^ 2 = Z := sq_sqrt_complex Z
  rw [mem_ball_zero_iff]
  have hZ_norm : ‖Z‖ < 1 := mem_ball_zero_iff.mp hZball
  have hnorm_sq : ‖Complex.sqrt Z‖ ^ 2 = ‖Z‖ := by
    simpa [norm_pow] using congrArg norm hsquare
  nlinarith [norm_nonneg (Complex.sqrt Z), hZ_norm, hnorm_sq]

/-- Helper for Exercise 7: squaring preserves membership in the open unit disc. -/
lemma square_mem_ball_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    w ^ 2 ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hw ⊢
  rw [norm_pow]
  nlinarith [norm_nonneg w, hw]

/-- Helper for Exercise 7: on the right half-disc, the normalized square of the inverse branch is
exactly the disc-centering automorphism applied to `w^2`. -/
lemma normalized_square_unitDiscToCassiniOval_eq_discCenter_sq
    {a r : ℝ} (ha : 0 < a) (har : a < r) {w : ℂ} (hw : w ∈ rightHalfUnitDisc) :
    (((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) =
      discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
  rcases mem_rightHalfUnitDisc.mp hw with ⟨hw_ball, _⟩
  obtain ⟨hw_sq_ball, _⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
  have hr : r ≠ 0 := by
    nlinarith
  have hR : ((r : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hr)
  have hden :
      ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2) ≠ 0 :=
    unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
  have hsquare_arg :
      unitDiscToCassiniOval a r w ^ 2 =
        (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) *
          discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
    -- Rewrite the solved square by the affine disc-centering formula from the source route.
    calc
      unitDiscToCassiniOval a r w ^ 2 =
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * (w ^ 2)) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2))) := by
        simpa [pow_mul] using unitDiscToCassiniOval_sq (a := a) (r := r) (w := w) hw_ball
      _ = (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) *
            discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
        simpa using
          unitDiscToCassiniOval_sq_arg_eq_affine_discCenter
            (a := a) (r := r) hr (Z := w ^ 2) hden
  -- Subtract `a^2` and divide by the positive real factor `r^2`.
  calc
    (((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) =
        ((((a : ℂ) ^ 2 + ((r : ℂ) ^ 2) *
            discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2)) -
          (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) := by
      rw [hsquare_arg]
    _ = discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
      field_simp [hR]
      ring

/-- Helper for Exercise 7: the inverse normalized-square identity is algebraic and therefore also
holds on the full unit disc. -/
lemma normalized_square_unitDiscToCassiniOval_eq_discCenter_sq_of_mem_ball
    {a r : ℝ} (ha : 0 < a) (har : a < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) =
      discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
  have hr : r ≠ 0 := by
    nlinarith [ha, har]
  have hR : ((r : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hr)
  have hw_sq_ball : w ^ 2 ∈ ball (0 : ℂ) 1 := square_mem_ball_of_mem_ball hw
  have hden :
      ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2) ≠ 0 :=
    unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
  have hsquare_arg :
      unitDiscToCassiniOval a r w ^ 2 =
        (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) *
          discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
    -- Rewrite the solved square by the same affine disc-center formula as on `B⁺`.
    calc
      unitDiscToCassiniOval a r w ^ 2 =
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * (w ^ 2)) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2))) := by
        simpa [pow_mul] using unitDiscToCassiniOval_sq (a := a) (r := r) (w := w) hw
      _ = (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) *
            discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
        simpa using
          unitDiscToCassiniOval_sq_arg_eq_affine_discCenter
            (a := a) (r := r) hr (Z := w ^ 2) hden
  calc
    (((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) =
        ((((a : ℂ) ^ 2 + ((r : ℂ) ^ 2) *
            discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2)) -
          (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) := by
      rw [hsquare_arg]
    _ = discCenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ)) (w ^ 2) := by
      field_simp [hR]
      ring

/-- Helper for Exercise 7: adding back a real disc center exposes the same affine factor used in
the source normalization. -/
lemma add_real_discCenter_eq_mul_ofReal_div
    {c : ℝ} {Z : ℂ} (hden : 1 - (c : ℂ) * Z ≠ 0) :
    ((c : ℂ) + discCenter (c : ℂ) Z) =
      Z * ((((1 - c ^ 2 : ℝ)) : ℂ) / (1 - (c : ℂ) * Z)) := by
  -- Because the center is real, the conjugation in `discCenter` disappears.
  unfold discCenter
  simp [Complex.conj_ofReal]
  field_simp [hden]
  ring

/-- Helper for Exercise 7: for a real disc center, `discUncenter` rescales the imaginary part by
the positive real factor coming from the standard Möbius denominator. -/
lemma discUncenter_im_of_real_center
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1) {η : ℂ} (hη : η ∈ ball (0 : ℂ) 1) :
    (discUncenter (c : ℂ) η).im =
      η.im * (1 - c ^ 2) / ‖1 + (c : ℂ) * η‖ ^ 2 := by
  have hc_norm : ‖(c : ℂ)‖ < 1 := by
    simpa [abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : (-(c : ℂ)) ∈ ball (0 : ℂ) 1 := by
    -- The inverse disc automorphism is centered at `-c`, which still lies in the unit disc.
    rw [mem_ball_zero_iff]
    simpa [norm_neg] using hc_norm
  have hden : 1 + (c : ℂ) * η ≠ 0 := by
    -- This is exactly the denominator-nonvanishing lemma for `discCenter (-c)`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
      Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hη)
  -- Compute the imaginary part of the explicit quotient and simplify the real-center algebra.
  rw [discUncenter, discCenter, Complex.div_im]
  simp [Complex.conj_ofReal, Complex.normSq_eq_norm_sq, sub_eq_add_neg, mul_comm, mul_left_comm,
    mul_assoc]
  field_simp [hden]
  ring

/-- Helper for Exercise 7: adding back a real disc center rescales the imaginary part by the same
positive real factor as the centered-disc formula. -/
lemma add_real_discCenter_im_of_mem_ball
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1) {Z : ℂ} (hZ : Z ∈ ball (0 : ℂ) 1) :
    (((c : ℂ) + discCenter (c : ℂ) Z).im) =
      Z.im * (1 - c ^ 2) / ‖1 - (c : ℂ) * Z‖ ^ 2 := by
  have hc_norm : ‖(c : ℂ)‖ < 1 := by
    simpa [abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : ((c : ℂ)) ∈ ball (0 : ℂ) 1 := by
    -- The real center lies in the unit disc because `0 < c < 1`.
    rw [mem_ball_zero_iff]
    exact hc_norm
  have hden : 1 - (c : ℂ) * Z ≠ 0 := by
    simpa [Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hZ)
  -- Compute the imaginary part of the affine centered expression directly.
  unfold discCenter
  rw [Complex.add_im, Complex.div_im]
  simp [Complex.conj_ofReal, Complex.normSq_eq_norm_sq, sub_eq_add_neg, mul_comm, mul_left_comm,
    mul_assoc]
  field_simp [hden]
  ring

/-- Helper for Exercise 7: a positive real multiple of a slit-plane point stays in the slit
plane. -/
lemma mul_ofReal_mem_slitPlane_of_pos
    {x : ℝ} (hx : 0 < x) {Z : ℂ} (hZ : Z ∈ Complex.slitPlane) :
    ((x : ℂ) * Z) ∈ Complex.slitPlane := by
  -- Positive real scaling preserves the sign of the real part and the vanishing of the imaginary
  -- part.
  rw [Complex.mem_slitPlane_iff] at hZ ⊢
  rcases hZ with hZre | hZim
  · left
    simpa [mul_comm] using mul_pos hx hZre
  · right
    simpa [Complex.mul_im, hx.ne', mul_comm] using hZim

/-- Helper for Exercise 7: a point whose normalized square lies in the unit disc belongs to the
Cassini interior. -/
lemma mem_cassiniOvalInterior_of_normalized_square_mem_ball
    {a r : ℝ} (hr : 0 < r) {z : ℂ}
    (hη : ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) ∈ ball (0 : ℂ) 1) :
    z ∈ cassiniOvalInterior a r := by
  have hη_norm : ‖(z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)‖ < 1 := mem_ball_zero_iff.mp hη
  have hr_sq_pos : 0 < r ^ 2 := by positivity
  have hR_norm : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    calc
      ‖(r : ℂ) ^ 2‖ = ‖(r : ℂ)‖ ^ 2 := by rw [norm_pow]
      _ = |r| ^ 2 := by simp
      _ = r ^ 2 := by simp [pow_two, abs_of_pos hr]
  have hz_norm : ‖z ^ 2 - (a : ℂ) ^ 2‖ < r ^ 2 := by
    rw [norm_div, hR_norm] at hη_norm
    exact (div_lt_one hr_sq_pos).1 hη_norm
  exact hz_norm

/-- Helper for Exercise 7: the explicit forward branch already maps the full Cassini interior into
the open unit disc. The right-half restriction is only needed to control the square-root sign. -/
lemma cassiniOvalToUnitDisc_mem_ball_of_mem_cassiniOvalInterior
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ} (hz : z ∈ cassiniOvalInterior a r) :
    cassiniOvalToUnitDisc a r z ∈ ball (0 : ℂ) 1 := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
  have hr_pos : 0 < r := lt_trans ha har
  have hr : r ≠ 0 := ne_of_gt hr_pos
  have hc_pos : 0 < cR := by
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hη_ball : η ∈ ball (0 : ℂ) 1 := by
    simpa [η] using normalized_square_mem_unit_ball_of_mem_cassiniOvalInterior hz
  have hmobius_ball : cassiniOvalMobius a r (z ^ 2) ∈ ball (0 : ℂ) 1 := by
    -- The Möbius normalization is the disc uncentering of the normalized square coordinate.
    rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)]
    simpa [c, cR, η] using disc_uncenter_mapsTo_unit_ball hc_ball hη_ball
  simpa [cassiniOvalToUnitDisc] using sqrt_mem_ball_of_mem_ball hmobius_ball

/-- Helper for Exercise 7: the explicit inverse branch maps the full unit disc into the Cassini
interior. The right-half restriction is only needed to select the correct square-root branch. -/
lemma unitDiscToCassiniOval_mem_cassiniOvalInterior_of_mem_ball
    {a r : ℝ} (ha : 0 < a) (har : a < r) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    unitDiscToCassiniOval a r w ∈ cassiniOvalInterior a r := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  have hr_pos : 0 < r := lt_trans ha har
  have hc_pos : 0 < cR := by
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hw_sq_ball : w ^ 2 ∈ ball (0 : ℂ) 1 := square_mem_ball_of_mem_ball hw
  have hnormalized_ball :
      (((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) ∈ ball (0 : ℂ) 1 := by
    rw [normalized_square_unitDiscToCassiniOval_eq_discCenter_sq_of_mem_ball ha har hw]
    exact disc_center_mapsTo_unit_ball hc_ball hw_sq_ball
  exact mem_cassiniOvalInterior_of_normalized_square_mem_ball hr_pos hnormalized_ball

end
