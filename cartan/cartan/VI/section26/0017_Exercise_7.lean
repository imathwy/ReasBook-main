import Mathlib
import cartan.II.section06.«0015_Remark_II_2_extra_6»
import cartan.III.section12.«0022_Exercise_10»
import cartan.VI.section22.«0006_Definition_VI_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Metric Set ComplexOrder
open scoped ComplexConjugate

noncomputable section

-- `lean_leansearch` was unavailable in this session, so the statement surface below was chosen
-- from the local section precedent around `AnalyticOnNhd`, `Set.MapsTo`, and explicit biholomorphic
-- data rather than from semantic search recall.

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

/-- Helper for Exercise 7: the forward normalized square followed by disc uncentering stays on the
principal square-root slit plane on the right-half Cassini domain. -/
lemma discUncenter_normalized_square_mem_slitPlane_of_mem_rightHalf
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ}
    (hz : z ∈ cassiniOvalRightHalf a r) :
    discUncenter ((((a ^ 2 / r ^ 2 : ℝ)) : ℂ))
        (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) ∈ Complex.slitPlane := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
  have hr_pos : 0 < r := lt_trans ha har
  have hc_pos : 0 < cR := by
    -- The Cassini center ratio is positive because `0 < a < r`.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- The ratio is strictly less than `1` because `a^2 < r^2`.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by nlinarith
    have hr_sq_pos : 0 < r ^ 2 := by positivity
    exact (div_lt_one hr_sq_pos).2 ha_sq_lt
  have hη_ball : η ∈ ball (0 : ℂ) 1 := by
    simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hz
  by_cases hηim : η.im = 0
  · -- On the real branch, the source route says the normalized coordinate stays to the right of
    -- `-cR`, so the uncentered Möbius image is a positive real.
    obtain ⟨hz_im, hη_re_lt⟩ := normalized_square_real_case_of_mem_rightHalf hz (by simpa [η] using hηim)
    have hnum_pos : 0 < η.re + cR := by
      nlinarith
    have hden_pos : 0 < 1 + cR * η.re := by
      nlinarith [hc_pos, hc_lt, hη_re_lt]
    have hηeq : η = (η.re : ℂ) := by
      apply Complex.ext <;> simp [hηim]
    have hEq :
        discUncenter (cR : ℂ) η = (((η.re + cR) / (1 + cR * η.re) : ℝ) : ℂ) := by
      -- With `Im η = 0`, the Möbius quotient is a positive real number.
      rw [hηeq]
      simp [discUncenter, discCenter, Complex.conj_ofReal, hden_pos.ne', div_eq_mul_inv]
    rw [show (((a ^ 2 / r ^ 2 : ℝ)) : ℂ) = (cR : ℂ) by simp [cR], show (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) = η by rfl]
    rw [hEq]
    exact Complex.ofReal_mem_slitPlane.2 (by exact div_pos hnum_pos hden_pos)
  · -- Off the real axis, the explicit imaginary-part formula keeps the image off the branch cut.
    have hden : 1 + (cR : ℂ) * η ≠ 0 := by
      have hc_norm : ‖(cR : ℂ)‖ < 1 := by
        simpa [abs_of_nonneg hc_pos.le] using hc_lt
      have hc_ball : (-(cR : ℂ)) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        simpa [norm_neg] using hc_norm
      simpa [η, cR, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc, Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hη_ball)
    have him_eq :
        (discUncenter (cR : ℂ) η).im =
          η.im * (1 - cR ^ 2) / ‖1 + (cR : ℂ) * η‖ ^ 2 :=
      discUncenter_im_of_real_center hc_pos hc_lt hη_ball
    have hnum_ne : η.im * (1 - cR ^ 2) ≠ 0 := by
      apply mul_ne_zero hηim
      nlinarith
    have hden_ne : ‖1 + (cR : ℂ) * η‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hden)
    rw [show (((a ^ 2 / r ^ 2 : ℝ)) : ℂ) = (cR : ℂ) by simp [cR], show (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) = η by rfl]
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_eq]
    exact div_ne_zero hnum_ne hden_ne

/-- Helper for Exercise 7: recentering a slit-plane point by a real disc automorphism stays on
the principal branch cut complement. -/
lemma add_real_discCenter_mem_slitPlane_of_mem_ball_and_slitPlane
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1) {Z : ℂ}
    (hZball : Z ∈ ball (0 : ℂ) 1) (hZslit : Z ∈ Complex.slitPlane) :
    ((c : ℂ) + discCenter (c : ℂ) Z) ∈ Complex.slitPlane := by
  by_cases hZim : Z.im = 0
  · -- On the real branch, the recentered point is a positive real.
    rw [Complex.mem_slitPlane_iff] at hZslit
    have hZre_pos : 0 < Z.re := by
      rcases hZslit with hZre | hZim'
      · exact hZre
      · exact False.elim (hZim' hZim)
    have hZnorm : ‖Z‖ < 1 := mem_ball_zero_iff.mp hZball
    have hZeq : Z = (Z.re : ℂ) := by
      apply Complex.ext <;> simp [hZim]
    have hZre_lt : Z.re < 1 := by
      have habs_lt : |Z.re| < 1 := by
        rw [hZeq] at hZnorm
        simpa using hZnorm
      exact (abs_lt.mp habs_lt).2
    have hden_pos : 0 < 1 - c * Z.re := by
      nlinarith [hc_pos, hc_lt, hZre_lt]
    have hnum_pos : 0 < Z.re * (1 - c ^ 2) := by
      have : 0 < 1 - c ^ 2 := by nlinarith
      exact mul_pos hZre_pos this
    have hc_norm : ‖(c : ℂ)‖ < 1 := by
      simpa [abs_of_nonneg hc_pos.le] using hc_lt
    have hden : 1 - (c : ℂ) * Z ≠ 0 := by
      have hc_ball : ((c : ℂ)) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        exact hc_norm
      simpa [Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hZball)
    have hEq :
        ((c : ℂ) + discCenter (c : ℂ) Z) =
          (((Z.re * (1 - c ^ 2) / (1 - c * Z.re) : ℝ)) : ℂ) := by
      -- After exposing the affine factor, everything is real because `Im Z = 0`.
      rw [add_real_discCenter_eq_mul_ofReal_div hden]
      rw [hZeq]
      simp [Complex.conj_ofReal, hden_pos.ne', div_eq_mul_inv]
      ring_nf
    rw [hEq]
    exact Complex.ofReal_mem_slitPlane.2 (by exact div_pos hnum_pos hden_pos)
  · -- Off the real axis, the explicit imaginary-part formula shows the image stays off the cut.
    have him_eq :
        (((c : ℂ) + discCenter (c : ℂ) Z).im) =
          Z.im * (1 - c ^ 2) / ‖1 - (c : ℂ) * Z‖ ^ 2 :=
      add_real_discCenter_im_of_mem_ball hc_pos hc_lt hZball
    have hc_norm : ‖(c : ℂ)‖ < 1 := by
      simpa [abs_of_nonneg hc_pos.le] using hc_lt
    have hc_ball : ((c : ℂ)) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      exact hc_norm
    have hden : 1 - (c : ℂ) * Z ≠ 0 := by
      simpa [Complex.conj_ofReal] using (disc_center_denom_ne_zero hc_ball hZball)
    have hnum_ne : Z.im * (1 - c ^ 2) ≠ 0 := by
      apply mul_ne_zero hZim
      nlinarith
    have hden_ne : ‖1 - (c : ℂ) * Z‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hden)
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_eq]
    exact div_ne_zero hnum_ne hden_ne

/-- Helper for Exercise 7: the principal square root of a slit-plane point has positive real
part. -/
lemma sqrt_re_pos_of_mem_slitPlane
    {Z : ℂ} (hZ : Z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt Z).re := by
  have hsum_pos : 0 < ‖Z‖ + Z.re := by
    -- Either `Re Z > 0`, or the nonzero imaginary part makes the norm strictly larger than
    -- `|Re Z|`.
    rw [Complex.mem_slitPlane_iff] at hZ
    rcases hZ with hZre | hZim
    · nlinarith [norm_nonneg Z, hZre]
    · have hRe_lt : |Z.re| < ‖Z‖ := (Complex.abs_re_lt_norm).2 hZim
      have hleft : -‖Z‖ < Z.re := (abs_lt.mp hRe_lt).1
      nlinarith
  have hRe_sqrt : (Complex.sqrt Z).re = Real.sqrt ((‖Z‖ + Z.re) / 2) := by
    -- The principal branch always takes the nonnegative real square-root formula.
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp
  rw [hRe_sqrt]
  have harg_pos : 0 < (‖Z‖ + Z.re) / 2 := by nlinarith
  exact Real.sqrt_pos.mpr harg_pos

/-- Helper for Exercise 7: a slit-plane-valued analytic map has an analytic principal square
root. -/
lemma analyticOnNhd_sqrt_of_mapsTo_slitPlane
    {s : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s)
    (hslit : Set.MapsTo f s Complex.slitPlane) :
    AnalyticOnNhd ℂ (fun z ↦ Complex.sqrt (f z)) s := by
  -- Rewrite `sqrt` as the principal half-power and use the slit-plane branch condition.
  simpa [Complex.sqrt] using
    hf.cpow (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ (2⁻¹ : ℂ)) s)
      (by
        intro z hz
        exact hslit hz)

/-- Helper for Exercise 7: the forward square-root argument is holomorphic on the right-half
Cassini domain and stays on the principal slit plane there. -/
lemma cassini_forward_argument_analyticOnNhd
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (fun z ↦ cassiniOvalMobius a r (z ^ 2)) (cassiniOvalRightHalf a r) ∧
      Set.MapsTo (fun z ↦ cassiniOvalMobius a r (z ^ 2))
        (cassiniOvalRightHalf a r) Complex.slitPlane := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  have hr_pos : 0 < r := lt_trans ha har
  have hr : r ≠ 0 := ne_of_gt hr_pos
  have hc_pos : 0 < cR := by
    -- The normalized center is positive because `0 < a < r`.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- The same normalization lies strictly inside the unit disc.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by
      nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_norm : ‖c‖ < 1 := by
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hc_norm
  have hη_diff :
      DifferentiableOn ℂ
        (fun z : ℂ ↦ ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)))
        (cassiniOvalRightHalf a r) := by
    intro z hz
    -- The normalized square coordinate is a polynomial divided by a nonzero constant.
    let _ := hz
    fun_prop
  have hη_analytic :
      AnalyticOnNhd ℂ
        (fun z : ℂ ↦ ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)))
        (cassiniOvalRightHalf a r) :=
    (Complex.analyticOnNhd_iff_differentiableOn (isOpen_cassiniOvalRightHalf a r)).2 hη_diff
  have hη_maps :
      Set.MapsTo
        (fun z : ℂ ↦ ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)))
        (cassiniOvalRightHalf a r) (ball (0 : ℂ) 1) := by
    intro z hz
    simpa using normalized_square_mem_unit_ball_of_mem_rightHalf hz
  have hdisc_analytic : AnalyticOnNhd ℂ (discUncenter c) (ball (0 : ℂ) 1) := by
    exact
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
        (disc_uncenter_differentiableOn hc_ball)
  have hraw_analytic :
      AnalyticOnNhd ℂ
        (fun z ↦ discUncenter c (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))))
        (cassiniOvalRightHalf a r) := by
    -- Compose the normalized square coordinate with the disc automorphism.
    exact hdisc_analytic.comp hη_analytic hη_maps
  refine ⟨?_, ?_⟩
  · -- Replace the normalized disc-automorphism expression with the source Möbius formula.
    convert hraw_analytic using 1
    ext z
    simpa [c, cR] using cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)
  · intro z hz
    -- The slit-plane image has already been established for the normalized source route.
    have hEq := cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)
    simpa [hEq, c, cR] using
      (discUncenter_normalized_square_mem_slitPlane_of_mem_rightHalf ha har hz :
        discUncenter c (((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) ∈ Complex.slitPlane)

/-- Helper for Exercise 7: the inverse square-root argument is holomorphic on the right half-disc
and stays on the principal slit plane there. -/
lemma cassini_inverse_argument_analyticOnNhd
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc ∧
      Set.MapsTo
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc Complex.slitPlane := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  have hr_pos : 0 < r := lt_trans ha har
  have hr : r ≠ 0 := ne_of_gt hr_pos
  have hc_pos : 0 < cR := by
    -- The normalized center is the same positive ratio as in the forward branch.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- It remains strictly inside the unit disc.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by
      nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_norm : ‖c‖ < 1 := by
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hc_norm
  have hraw_diff :
      DifferentiableOn ℂ
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc := by
    intro w hw
    obtain ⟨hw_sq_ball, _⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
    have hnum_diff :
        DifferentiableAt ℂ (fun w : ℂ ↦ (((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2)) w := by
      fun_prop
    have hden_diff :
        DifferentiableAt ℂ (fun w : ℂ ↦ ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2) w := by
      fun_prop
    have hden_ne :
        ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2 ≠ 0 :=
      unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
    exact (hnum_diff.div hden_diff hden_ne).differentiableWithinAt
  have hraw_analytic :
      AnalyticOnNhd ℂ
        (fun w ↦ ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc :=
    (Complex.analyticOnNhd_iff_differentiableOn isOpen_rightHalfUnitDisc).2 hraw_diff
  refine ⟨hraw_analytic, ?_⟩
  intro w hw
  change
    ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) ∈
      Complex.slitPlane
  obtain ⟨hw_sq_ball, hw_sq_slit⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
  have hcenter_slit : (c + discCenter c (w ^ 2)) ∈ Complex.slitPlane := by
    simpa [c] using
      add_real_discCenter_mem_slitPlane_of_mem_ball_and_slitPlane hc_pos hc_lt
        hw_sq_ball hw_sq_slit
  have hden :
      ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2) ≠ 0 :=
    unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
  have hc_eq : ((r : ℂ) ^ 2) * c = (a : ℂ) ^ 2 := by
    -- The affine source coordinate uses the same disc-center parameter `c`.
    dsimp [c, cR]
    have hr_sq_ne : r ^ 2 ≠ 0 := by
      positivity
    have hreal : r ^ 2 * (a ^ 2 / r ^ 2) = a ^ 2 := by
      field_simp [hr_sq_ne]
    simpa using congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
  have hraw_eq :
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
        ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
    -- Rewrite the raw inverse expression to the affine disc-center form from the source route.
    calc
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
          (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
        simpa [c, cR] using
          unitDiscToCassiniOval_sq_arg_eq_affine_discCenter
            (a := a) (r := r) hr (Z := w ^ 2) hden
      _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
        calc
          (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) =
              ((r : ℂ) ^ 2) * c + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
            rw [hc_eq]
          _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
            ring
  have hscale_slit :
      (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) ∈ Complex.slitPlane :=
    mul_ofReal_mem_slitPlane_of_pos (x := r ^ 2) (by positivity) hcenter_slit
  have hcast :
      ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) =
        (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) := by
    simp
  have hscaled_slit :
      ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) ∈ Complex.slitPlane := by
    simpa [hcast] using hscale_slit
  exact hraw_eq.symm ▸ hscaled_slit

/-- Helper for Exercise 7: on the open right half-plane, equality of squares already determines
the principal square-root branch. -/
lemma eq_of_sq_eq_sq_of_re_pos
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hsq : u ^ 2 = v ^ 2) :
    u = v := by
  -- Factor the difference of squares to reduce to the two possible square roots.
  have hfactor : (u - v) * (u + v) = 0 := by
    calc
      (u - v) * (u + v) = u ^ 2 - v ^ 2 := by ring
      _ = 0 := by rw [hsq, sub_self]
  rcases mul_eq_zero.mp hfactor with hsub | hadd
  · exact sub_eq_zero.mp hsub
  · have hre : u.re + v.re = 0 := by
      simpa using congrArg Complex.re hadd
    linarith

/-- Helper for Exercise 7: the auxiliary Möbius map sends the Cassini imaginary-axis segment to
the real interval `[-1, 0]`. -/
lemma cassiniOvalMobius_mem_nonpos_real_unitSegment_of_mem_imaginaryAxisSegment
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ}
    (hz : z ∈ cassiniOvalImaginaryAxisSegment a r) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ cassiniOvalMobius a r (z ^ 2) = -((t : ℂ)) := by
  rcases mem_cassiniOvalImaginaryAxisSegment.mp hz with ⟨hz_re, hz_bound⟩
  let y : ℝ := z.im
  have hr_pos : 0 < r := lt_trans ha har
  have hz_eq : z = Complex.I * y := by
    -- A point on the imaginary axis is exactly `I * y` with `y = Im z`.
    apply Complex.ext <;> simp [y, hz_re]
  have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hden_pos : 0 < r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := by
    -- The interval hypothesis `y^2 ≤ r^2 - a^2` keeps the Möbius denominator positive.
    have hlower : r ^ 2 * (r ^ 2 - a ^ 2) ≤ r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := by
      nlinarith [hz_bound]
    have hbase : 0 < r ^ 2 * (r ^ 2 - a ^ 2) := by
      have hgap : 0 < r ^ 2 - a ^ 2 := by
        nlinarith [ha, har]
      positivity
    nlinarith
  let t : ℝ := (r ^ 2 * y ^ 2) / (r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2)
  have ht_nonneg : 0 ≤ t := by
    -- Both numerator and denominator are nonnegative, with positive denominator.
    dsimp [t]
    positivity
  have ht_le_one : t ≤ 1 := by
    -- After clearing the positive denominator, this is exactly `y^2 ≤ r^2 - a^2`.
    dsimp [t]
    have hden_nonneg : 0 ≤ r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := le_of_lt hden_pos
    have hmul :
        r ^ 2 * y ^ 2 ≤ r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := by
      nlinarith [hz_bound, hy_sq_nonneg, ha, har]
    exact (div_le_one hden_pos).2 hmul
  refine ⟨t, ht_nonneg, ht_le_one, ?_⟩
  have hz_sq : z ^ 2 = -((y ^ 2 : ℝ) : ℂ) := by
    -- Squaring `I * y` sends the imaginary-axis segment to the negative real axis.
    rw [hz_eq]
    calc
      (Complex.I * (y : ℂ)) ^ 2 = Complex.I ^ 2 * ((y : ℂ) ^ 2) := by
        ring
      _ = -((y ^ 2 : ℝ) : ℂ) := by
        simp [pow_two]
  have hden_ne : (((r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hden_pos
  -- Evaluate the Möbius quotient explicitly on the negative real square.
  calc
    cassiniOvalMobius a r (z ^ 2) =
        ((-((r ^ 2 * y ^ 2 : ℝ) : ℂ)) /
          (((r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 : ℝ) : ℂ))) := by
      rw [cassiniOvalMobius, hz_sq]
      simp [pow_two]
      ring
    _ = -((t : ℂ)) := by
      simp [t, div_eq_mul_inv]

/-- The right-half construction in the source: for `0 < a < r`, the explicit map
`z ↦ sqrt ((r^2 z^2) / (a^2 z^2 + r^4 - a^4))` is a biholomorphic isomorphism from `D⁺` onto
`B⁺`, takes real values on the real axis, and maps the boundary segment `iy`, `y^2 ≤ r^2 - a^2`,
onto the segment `iv`, `|v| ≤ 1`. -/
theorem cassiniOvalToUnitDisc_right_half_isomorphism
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    -- Route correction: the package theorem must follow the source chain `z ↦ z^2`, Möbius
    -- normalization in the `ζ`-plane, then the principal square-root branch on the slit plane.
    AnalyticOnNhd ℂ (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) ∧
      Set.MapsTo (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) rightHalfUnitDisc ∧
      AnalyticOnNhd ℂ (unitDiscToCassiniOval a r) rightHalfUnitDisc ∧
      Set.MapsTo (unitDiscToCassiniOval a r) rightHalfUnitDisc (cassiniOvalRightHalf a r) ∧
      Set.EqOn
        ((unitDiscToCassiniOval a r) ∘ (cassiniOvalToUnitDisc a r))
        id (cassiniOvalRightHalf a r) ∧
      Set.EqOn
        ((cassiniOvalToUnitDisc a r) ∘ (unitDiscToCassiniOval a r))
        id rightHalfUnitDisc ∧
      Set.MapsTo (cassiniOvalToUnitDisc a r)
        {z | z ∈ cassiniOvalRightHalf a r ∧ z.im = 0}
        {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} ∧
      Set.MapsTo (cassiniOvalToUnitDisc a r)
        (cassiniOvalImaginaryAxisSegment a r)
        unitDiscImaginaryAxisSegment := by
  let cR : ℝ := a ^ 2 / r ^ 2
  let c : ℂ := (cR : ℂ)
  have hr_pos : 0 < r := lt_trans ha har
  have hr : r ≠ 0 := ne_of_gt hr_pos
  have hc_pos : 0 < cR := by
    -- The disc-automorphism center is the source ratio `a^2 / r^2`.
    dsimp [cR]
    exact div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr_pos)
  have hc_lt : cR < 1 := by
    -- The center lies strictly inside the unit disc because `a < r`.
    dsimp [cR]
    have ha_sq_lt : a ^ 2 < r ^ 2 := by nlinarith
    exact (div_lt_one (sq_pos_of_pos hr_pos)).2 ha_sq_lt
  have hc_norm : ‖c‖ < 1 := by
    dsimp [c]
    simpa [cR, abs_of_nonneg hc_pos.le] using hc_lt
  have hc_ball : c ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hc_norm
  have h_forward_maps :
      Set.MapsTo (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) rightHalfUnitDisc := by
    intro z hz
    let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
    have hη_ball : η ∈ ball (0 : ℂ) 1 := by
      simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hz
    have hmobius_ball : cassiniOvalMobius a r (z ^ 2) ∈ ball (0 : ℂ) 1 := by
      -- The source Möbius normalization is exactly the uncentered disc automorphism on `η`.
      rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)]
      simpa [c, cR, η] using (disc_uncenter_mapsTo_unit_ball hc_ball hη_ball)
    have hmobius_slit : cassiniOvalMobius a r (z ^ 2) ∈ Complex.slitPlane := by
      -- The new forward branch lemma puts the square-root argument on the principal branch.
      rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)]
      simpa [c, cR, η] using
        (discUncenter_normalized_square_mem_slitPlane_of_mem_rightHalf ha har hz)
    exact sqrt_mem_rightHalfUnitDisc_of_mem_ball_and_slitPlane hmobius_ball hmobius_slit
  have h_inverse_maps :
      Set.MapsTo (unitDiscToCassiniOval a r) rightHalfUnitDisc (cassiniOvalRightHalf a r) := by
    intro w hw
    obtain ⟨hw_sq_ball, hw_sq_slit⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
    have hcenter_ball : discCenter c (w ^ 2) ∈ ball (0 : ℂ) 1 :=
      disc_center_mapsTo_unit_ball hc_ball hw_sq_ball
    have hcenter_slit : (c + discCenter c (w ^ 2)) ∈ Complex.slitPlane := by
      simpa [c] using
        (add_real_discCenter_mem_slitPlane_of_mem_ball_and_slitPlane hc_pos hc_lt
          hw_sq_ball hw_sq_slit)
    have hden :
        ((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (w ^ 2) ≠ 0 :=
      unitDiscToCassiniOval_sq_arg_denom_ne_zero_of_mem_ball ha har hw_sq_ball
    have hc_eq : ((r : ℂ) ^ 2) * c = (a : ℂ) ^ 2 := by
      -- This identifies the affine `a^2` term with the same disc center `c`.
      dsimp [c, cR]
      have hr_sq_ne : r ^ 2 ≠ 0 := by positivity
      have hreal : r ^ 2 * (a ^ 2 / r ^ 2) = a ^ 2 := by
        field_simp [hr_sq_ne]
      simpa using congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
    have hraw_eq :
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
          ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
      -- Route correction: rewrite the inverse square-root argument to the affine disc-center form.
      calc
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
            (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
          simpa [c, cR] using
            (unitDiscToCassiniOval_sq_arg_eq_affine_discCenter
              (a := a) (r := r) hr (Z := w ^ 2) hden)
        _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
          calc
            (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) =
                ((r : ℂ) ^ 2) * c + ((r : ℂ) ^ 2) * discCenter c (w ^ 2) := by
              rw [hc_eq]
            _ = ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) := by
              ring
    have hraw_slit :
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) ∈
          Complex.slitPlane := by
      have hscale_slit :
          (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) ∈ Complex.slitPlane :=
        mul_ofReal_mem_slitPlane_of_pos (x := r ^ 2) (by positivity) hcenter_slit
      rw [hraw_eq]
      rw [show ((r : ℂ) ^ 2) * (c + discCenter c (w ^ 2)) =
          (((r ^ 2 : ℝ) : ℂ) * (c + discCenter c (w ^ 2))) by simp]
      exact hscale_slit
    have hre_pos : 0 < (unitDiscToCassiniOval a r w).re := by
      -- The inverse branch keeps positive real part because its square-root argument is on the
      -- slit plane.
      unfold unitDiscToCassiniOval
      simpa using sqrt_re_pos_of_mem_slitPlane hraw_slit
    have hnormalized_ball :
        (((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2)) ∈ ball (0 : ℂ) 1 := by
      rw [normalized_square_unitDiscToCassiniOval_eq_discCenter_sq ha har hw]
      exact hcenter_ball
    have hCassini : unitDiscToCassiniOval a r w ∈ cassiniOvalInterior a r :=
      mem_cassiniOvalInterior_of_normalized_square_mem_ball hr_pos hnormalized_ball
    exact ⟨hCassini, hre_pos⟩
  refine ⟨?_, h_forward_maps, ?_, h_inverse_maps, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hraw_analytic, hraw_slit⟩ := cassini_forward_argument_analyticOnNhd ha har
    -- Apply the principal square-root branch to the forward slit-plane-valued argument.
    simpa [cassiniOvalToUnitDisc] using
      analyticOnNhd_sqrt_of_mapsTo_slitPlane hraw_analytic hraw_slit
  · obtain ⟨hraw_analytic, hraw_slit⟩ := cassini_inverse_argument_analyticOnNhd ha har
    -- The inverse branch is the same slit-plane square-root package for the solved square.
    change
      AnalyticOnNhd ℂ
        (fun w ↦ Complex.sqrt
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
        rightHalfUnitDisc
    exact analyticOnNhd_sqrt_of_mapsTo_slitPlane hraw_analytic hraw_slit
  · intro z hz
    have hzCassini : z ∈ cassiniOvalInterior a r := (mem_cassiniOvalRightHalf.mp hz).1
    have hw : cassiniOvalToUnitDisc a r z ∈ rightHalfUnitDisc := h_forward_maps hz
    have hu :
        unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z) ∈ cassiniOvalRightHalf a r :=
      h_inverse_maps hw
    let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
    have hη_ball : η ∈ ball (0 : ℂ) 1 := by
      simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hz
    have hnormalized :
        (((unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2) /
            ((r : ℂ) ^ 2)) = η := by
      -- Both branches have the same normalized square coordinate.
      calc
        (((unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2) /
            ((r : ℂ) ^ 2)) =
            discCenter c ((cassiniOvalToUnitDisc a r z) ^ 2) := by
          simpa [c, cR] using normalized_square_unitDiscToCassiniOval_eq_discCenter_sq ha har hw
        _ = discCenter c (cassiniOvalMobius a r (z ^ 2)) := by
          rw [cassiniOvalToUnitDisc_sq hzCassini]
        _ = discCenter c (discUncenter c η) := by
          simpa [η, c, cR] using
            congrArg (fun ξ : ℂ ↦ discCenter c ξ)
              (cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2))
        _ = η := by
          simpa [η] using discCenter_discUncenter_eq_self_on_unit_ball hc_ball hη_ball
    have hR : ((r : ℂ) ^ 2) ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast hr)
    have hsub :
        (unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2 =
          z ^ 2 - (a : ℂ) ^ 2 := by
      calc
        (unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2 =
            ((((unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 - (a : ℂ) ^ 2) /
                ((r : ℂ) ^ 2)) * ((r : ℂ) ^ 2)) := by
          field_simp [hR]
        _ = η * ((r : ℂ) ^ 2) := by
          exact congrArg (fun x : ℂ ↦ x * ((r : ℂ) ^ 2)) hnormalized
        _ = z ^ 2 - (a : ℂ) ^ 2 := by
          dsimp [η]
          field_simp [hR]
    have hsq :
        (unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z)) ^ 2 = z ^ 2 := by
      have hadd := congrArg (fun x : ℂ ↦ x + (a : ℂ) ^ 2) hsub
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hadd
    -- Positive real parts force the correct square-root branch.
    exact
      eq_of_sq_eq_sq_of_re_pos
        (mem_cassiniOvalRightHalf.mp hu).2
        (mem_cassiniOvalRightHalf.mp hz).2
        hsq
  · intro w hw
    have hz : unitDiscToCassiniOval a r w ∈ cassiniOvalRightHalf a r := h_inverse_maps hw
    obtain ⟨hw_sq_ball, _⟩ := square_mem_ball_and_slitPlane_of_mem_rightHalfUnitDisc hw
    have hsq :
        (cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w)) ^ 2 = w ^ 2 := by
      -- Normalize through the disc automorphism inverse relation on `w^2`.
      calc
        (cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w)) ^ 2 =
            cassiniOvalMobius a r ((unitDiscToCassiniOval a r w) ^ 2) := by
          exact cassiniOvalToUnitDisc_sq (a := a) (r := r) (z := unitDiscToCassiniOval a r w)
            (mem_cassiniOvalRightHalf.mp hz).1
        _ = discUncenter c
              ((((unitDiscToCassiniOval a r w) ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))) := by
          rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr
            ((unitDiscToCassiniOval a r w) ^ 2)]
        _ = discUncenter c (discCenter c (w ^ 2)) := by
          rw [normalized_square_unitDiscToCassiniOval_eq_discCenter_sq ha har hw]
        _ = w ^ 2 := by
          simpa [c, cR] using
            (disc_uncenter_leftInvOn_disc_center (a := c) hc_ball hw_sq_ball)
    have hw_image : cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w) ∈ rightHalfUnitDisc :=
      h_forward_maps hz
    -- Positive real parts again select the principal branch.
    exact
      eq_of_sq_eq_sq_of_re_pos
        (mem_rightHalfUnitDisc.mp hw_image).2
        (mem_rightHalfUnitDisc.mp hw).2
        hsq
  · intro z hz
    rcases hz with ⟨hzRight, hz_im⟩
    have hw : cassiniOvalToUnitDisc a r z ∈ rightHalfUnitDisc := h_forward_maps hzRight
    let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
    have hη_ball : η ∈ ball (0 : ℂ) 1 := by
      simpa [η] using normalized_square_mem_unit_ball_of_mem_rightHalf hzRight
    have hη_im : η.im = 0 := by
      -- On the real slice, the normalized square remains real.
      dsimp [η]
      rw [show ((r : ℂ) ^ 2) = (((r ^ 2 : ℝ) : ℂ)) by simp]
      simp [Complex.div_im, pow_two, hz_im]
    have hmobius_im : (cassiniOvalMobius a r (z ^ 2)).im = 0 := by
      -- The real-center disc automorphism preserves the real axis.
      rw [cassiniOvalMobius_eq_discUncenter_normalized a r hr (z ^ 2)]
      rw [discUncenter_im_of_real_center hc_pos hc_lt hη_ball, hη_im]
      simp [η, c, cR]
    have hw_sq_im : ((cassiniOvalToUnitDisc a r z) ^ 2).im = 0 := by
      rw [cassiniOvalToUnitDisc_sq (a := a) (r := r) (z := z)
        ((mem_cassiniOvalRightHalf.mp hzRight).1), hmobius_im]
    have hw_re : 0 < (cassiniOvalToUnitDisc a r z).re := (mem_rightHalfUnitDisc.mp hw).2
    have hmul :
        2 * (cassiniOvalToUnitDisc a r z).re * (cassiniOvalToUnitDisc a r z).im = 0 := by
      have hsq_im_formula :
          ((cassiniOvalToUnitDisc a r z) ^ 2).im =
            2 * (cassiniOvalToUnitDisc a r z).re * (cassiniOvalToUnitDisc a r z).im := by
        simp [pow_two]
        ring
      rw [hsq_im_formula] at hw_sq_im
      exact hw_sq_im
    have hfactor : 2 * (cassiniOvalToUnitDisc a r z).re ≠ 0 := by
      nlinarith
    refine ⟨hw, ?_⟩
    exact mul_eq_zero.mp hmul |>.resolve_left hfactor
  · intro z hz
    rcases
      cassiniOvalMobius_mem_nonpos_real_unitSegment_of_mem_imaginaryAxisSegment ha har hz with
      ⟨t, ht_nonneg, ht_le_one, harg⟩
    have hnonneg : 0 ≤ ((t : ℝ) : ℂ) := by
      exact_mod_cast ht_nonneg
    have hsqrt_nonneg : Complex.sqrt ((t : ℝ) : ℂ) = (Real.sqrt t : ℂ) := by
      simpa using Complex.sqrt_of_nonneg hnonneg
    have hw_re_zero : (cassiniOvalToUnitDisc a r z).re = 0 := by
      -- On `[-1, 0]`, the principal square root lands on the imaginary axis.
      unfold cassiniOvalToUnitDisc
      rw [harg, Complex.sqrt_neg_of_nonneg hnonneg, hsqrt_nonneg]
      simp
    have hw_sq : cassiniOvalToUnitDisc a r z ^ 2 = -((t : ℂ)) := by
      -- Squaring the principal square root returns the interval parameter.
      unfold cassiniOvalToUnitDisc
      rw [sq_sqrt_complex, harg]
    have hnorm_sq : ‖cassiniOvalToUnitDisc a r z‖ ^ 2 = t := by
      have hnorm := congrArg norm hw_sq
      simpa [norm_pow, abs_of_nonneg ht_nonneg] using hnorm
    refine ⟨hw_re_zero, ?_⟩
    nlinarith [norm_nonneg (cassiniOvalToUnitDisc a r z), ht_nonneg, ht_le_one, hnorm_sq]

/-- The explicit map and its inverse define the canonical holomorphic isomorphism between the
right half of Cassini's oval and the right half of the unit disc. -/
noncomputable def cassiniOvalRightHalfIso {a r : ℝ} (ha : 0 < a) (har : a < r) :
    HolomorphicIsomorph (cassiniOvalRightHalf a r) rightHalfUnitDisc := by
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨h_toFun, h_mapsTo, h_invFun, h_invMapsTo, h_left, h_right, _, _⟩
  refine ⟨
    { toPartialEquiv :=
        { toFun := cassiniOvalToUnitDisc a r
          invFun := unitDiscToCassiniOval a r
          source := cassiniOvalRightHalf a r
          target := rightHalfUnitDisc
          map_source' := h_mapsTo
          map_target' := h_invMapsTo
          left_inv' := h_left
          right_inv' := h_right }
      open_source := isOpen_cassiniOvalRightHalf a r
      open_target := isOpen_rightHalfUnitDisc
      continuousOn_toFun := h_toFun.continuousOn
      continuousOn_invFun := h_invFun.continuousOn },
    ⟨rfl, rfl, h_toFun, h_invFun⟩⟩

@[simp] theorem cassiniOvalRightHalfIso_toFun {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ((cassiniOvalRightHalfIso ha har).1 : ℂ → ℂ) = cassiniOvalToUnitDisc a r := by
  -- This is the defining `toFun` field of the packaged right-half isomorphism.
  unfold cassiniOvalRightHalfIso
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨h_toFun, h_mapsTo, h_invFun, h_invMapsTo, h_left, h_right, h_real, h_imag⟩
  rfl

/-- On the right-half source, the canonical holomorphic isomorphism sends the real slice to the
real slice of the right half-disc. -/
theorem cassiniOvalRightHalfIso_mapsTo_realSlice
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo ((cassiniOvalRightHalfIso ha har).1 : ℂ → ℂ)
      {z | z ∈ cassiniOvalRightHalf a r ∧ z.im = 0}
      {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} := by
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, h_real, _⟩
  simpa using h_real

/-- On the right-half source, the canonical holomorphic isomorphism sends the Cassini imaginary
axis segment to the unit-disc imaginary axis segment. -/
theorem cassiniOvalRightHalfIso_mapsTo_imaginaryAxis
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo ((cassiniOvalRightHalfIso ha har).1 : ℂ → ℂ)
      (cassiniOvalImaginaryAxisSegment a r)
      unitDiscImaginaryAxisSegment := by
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, _, h_imag⟩
  simpa using h_imag

/-- Exercise 7, explicit branch: for `0 < a < r`, the map
`z ↦ sqrt ((r^2 z^2) / (a^2 z^2 + r^4 - a^4))` is the right-half branch from the source hint.
It is not a global map on the whole Cassini oval, since the displayed formula depends on `z^2`. -/
theorem cassiniOvalToUnitDisc_isomorphism_analytic
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) := by
  -- This is the first component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨h_analytic, _, _, _, _, _, _, _⟩
  exact h_analytic

/-- Exercise 7, explicit branch: the right-half branch maps `D⁺` into `B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_mapsTo
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (cassiniOvalToUnitDisc a r) (cassiniOvalRightHalf a r) rightHalfUnitDisc :=
    by
  -- This is the second component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, h_mapsTo, _, _, _, _, _, _⟩
  exact h_mapsTo

/-- Exercise 7, explicit branch: the right-half inverse is analytic on `B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_inv_analytic
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (unitDiscToCassiniOval a r) rightHalfUnitDisc := by
  -- This is the third component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, h_inv_analytic, _, _, _, _, _⟩
  exact h_inv_analytic

/-- Exercise 7, explicit branch: the right-half inverse maps `B⁺` back into `D⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_inv_mapsTo
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (unitDiscToCassiniOval a r) rightHalfUnitDisc (cassiniOvalRightHalf a r) :=
    by
  -- This is the fourth component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, h_inv_mapsTo, _, _, _, _⟩
  exact h_inv_mapsTo

/-- Exercise 7, explicit branch: composing the inverse with the forward map gives the identity on
the right half `D⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_left_inv
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.EqOn
      ((unitDiscToCassiniOval a r) ∘ (cassiniOvalToUnitDisc a r))
      id (cassiniOvalRightHalf a r) := by
  -- This is the left-inverse component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, h_left, _, _, _⟩
  exact h_left

/-- Exercise 7, explicit branch: composing the forward map with the inverse gives the identity on
the right half-disc `B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_right_inv
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.EqOn
      ((cassiniOvalToUnitDisc a r) ∘ (unitDiscToCassiniOval a r))
      id rightHalfUnitDisc := by
  -- This is the right-inverse component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, h_right, _, _⟩
  exact h_right

/-- The explicit map and its inverse define the canonical holomorphic isomorphism between the
right half of Cassini's oval and the right half of the open unit disc. -/
noncomputable def cassiniOvalIso {a r : ℝ} (ha : 0 < a) (har : a < r) :
    HolomorphicIsomorph (cassiniOvalRightHalf a r) rightHalfUnitDisc := by
  refine ⟨
    { toPartialEquiv :=
        { toFun := cassiniOvalToUnitDisc a r
          invFun := unitDiscToCassiniOval a r
          source := cassiniOvalRightHalf a r
          target := rightHalfUnitDisc
          map_source' := cassiniOvalToUnitDisc_isomorphism_mapsTo ha har
          map_target' := cassiniOvalToUnitDisc_isomorphism_inv_mapsTo ha har
          left_inv' := cassiniOvalToUnitDisc_isomorphism_left_inv ha har
          right_inv' := cassiniOvalToUnitDisc_isomorphism_right_inv ha har }
      open_source := isOpen_cassiniOvalRightHalf a r
      open_target := isOpen_rightHalfUnitDisc
      continuousOn_toFun := (cassiniOvalToUnitDisc_isomorphism_analytic ha har).continuousOn
      continuousOn_invFun := (cassiniOvalToUnitDisc_isomorphism_inv_analytic ha har).continuousOn },
    ⟨rfl, rfl,
      cassiniOvalToUnitDisc_isomorphism_analytic ha har,
      cassiniOvalToUnitDisc_isomorphism_inv_analytic ha har⟩⟩

/-- Exercise 7, explicit branch: the map sends the real slice of `D⁺` into the real slice of
`B⁺`. -/
theorem cassiniOvalToUnitDisc_isomorphism_real_slice
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (cassiniOvalToUnitDisc a r)
      {z | z ∈ cassiniOvalRightHalf a r ∧ z.im = 0}
      {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} := by
  -- This is the real-slice component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, h_real, _⟩
  exact h_real

/-- Exercise 7, explicit branch: the limiting boundary branch sends the Cassini imaginary-axis
segment into the unit-disc imaginary-axis segment. -/
theorem cassiniOvalToUnitDisc_isomorphism_imaginary_axis
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (cassiniOvalToUnitDisc a r)
      (cassiniOvalImaginaryAxisSegment a r)
      unitDiscImaginaryAxisSegment := by
  -- This is the imaginary-axis component of the right-half package theorem.
  rcases cassiniOvalToUnitDisc_right_half_isomorphism ha har with
    ⟨_, _, _, _, _, _, _, h_imag⟩
  exact h_imag

/-- Helper for Exercise 7: the Cassini interior is stable under the symmetry `z ↦ -conj z`. -/
lemma cassiniOvalInterior_mapsTo_negConj {a r : ℝ} :
    Set.MapsTo (fun z : ℂ ↦ -conj z) (cassiniOvalInterior a r) (cassiniOvalInterior a r) := by
  intro z hz
  -- Conjugation preserves the norm of `z^2 - a^2`, so the Cassini inequality is unchanged.
  rw [mem_cassiniOvalInterior] at hz ⊢
  have hconj_eq : (-conj z) ^ 2 - (a : ℂ) ^ 2 = conj (z ^ 2 - (a : ℂ) ^ 2) := by
    simp [pow_two, sub_eq_add_neg, mul_comm]
  calc
    ‖(-conj z) ^ 2 - (a : ℂ) ^ 2‖ = ‖conj (z ^ 2 - (a : ℂ) ^ 2)‖ := by
      rw [hconj_eq]
    _ = ‖z ^ 2 - (a : ℂ) ^ 2‖ := by
      rw [Complex.norm_conj]
    _ < r ^ 2 := hz

/-- Helper for Exercise 7: the inverse branch sends the unit-disc imaginary-axis segment back to
the Cassini imaginary-axis segment. -/
lemma unitDiscToCassiniOval_mapsTo_imaginary_axis
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    Set.MapsTo (unitDiscToCassiniOval a r) unitDiscImaginaryAxisSegment
      (cassiniOvalImaginaryAxisSegment a r) := by
  intro w hw
  rcases mem_unitDiscImaginaryAxisSegment.mp hw with ⟨hw_re, hw_norm⟩
  let t : ℝ := w.im
  let s : ℝ := ((r ^ 4 - a ^ 4) * t ^ 2) / (r ^ 2 + a ^ 2 * t ^ 2)
  have hr_pos : 0 < r := lt_trans ha har
  have hw_eq : w = Complex.I * t := by
    -- A point on the unit-disc imaginary axis is exactly `I * t` with `t = Im w`.
    apply Complex.ext <;> simp [t, hw_re]
  have ht_sq_le_one : t ^ 2 ≤ 1 := by
    -- The unit-disc bound becomes `t^2 ≤ 1` on the imaginary axis.
    have hnorm_sq_le : ‖w‖ ^ 2 ≤ 1 := by
      nlinarith [hw_norm, norm_nonneg w]
    rw [hw_eq] at hnorm_sq_le
    simpa [pow_two, t] using hnorm_sq_le
  have hden_pos : 0 < r ^ 2 + a ^ 2 * t ^ 2 := by
    nlinarith [sq_pos_of_pos hr_pos, sq_nonneg a, sq_nonneg t]
  have hs_nonneg : 0 ≤ s := by
    -- The solved square parameter is nonnegative because both numerator and denominator are.
    dsimp [s]
    have hnum_nonneg : 0 ≤ (r ^ 4 - a ^ 4) * t ^ 2 := by
      have hcoeff_pos : 0 < r ^ 4 - a ^ 4 := by
        have hgap : 0 < r ^ 2 - a ^ 2 := by
          nlinarith
        have hsum : 0 < r ^ 2 + a ^ 2 := by
          positivity
        nlinarith
      positivity
    exact div_nonneg hnum_nonneg hden_pos.le
  have harg :
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
        -((s : ℂ)) := by
    -- On the imaginary axis the inverse square-root argument becomes a negative real number.
    have hw_sq : w ^ 2 = -(((t ^ 2 : ℝ) : ℂ)) := by
      rw [hw_eq]
      calc
        (Complex.I * (t : ℂ)) ^ 2 = Complex.I ^ 2 * ((t : ℂ) ^ 2) := by
          ring
        _ = -(((t ^ 2 : ℝ) : ℂ)) := by
          simp [pow_two]
    have hden_ne : (((r ^ 2 + a ^ 2 * t ^ 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast ne_of_gt hden_pos
    calc
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) / (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) =
          (-(((r ^ 4 - a ^ 4) * t ^ 2 : ℝ) : ℂ)) /
            (((r ^ 2 + a ^ 2 * t ^ 2 : ℝ) : ℂ)) := by
        rw [hw_sq]
        simp
      _ = -((s : ℂ)) := by
        rw [neg_div]
        simp [s]
  have hvalue :
      unitDiscToCassiniOval a r w = Complex.I * (Real.sqrt s : ℂ) := by
    -- The principal square root of a nonpositive real number lies on the imaginary axis.
    unfold unitDiscToCassiniOval
    rw [harg, Complex.sqrt_neg_of_nonneg]
    · simpa using (Complex.sqrt_of_nonneg (show 0 ≤ (s : ℂ) by exact_mod_cast hs_nonneg))
    · exact_mod_cast hs_nonneg
  refine (mem_cassiniOvalImaginaryAxisSegment).2 ?_
  refine ⟨?_, ?_⟩
  · -- Multiplying a real number by `I` kills the real part.
    rw [hvalue]
    simp
  · -- The imaginary-axis bound is exactly the inequality `s ≤ r^2 - a^2`.
    rw [hvalue]
    simp [pow_two, hs_nonneg, Real.sq_sqrt]
    have hs_le : s ≤ r ^ 2 - a ^ 2 := by
      -- Clearing the positive denominator reduces this to `t^2 ≤ 1`.
      dsimp [s]
      have hmul :
          (r ^ 4 - a ^ 4) * t ^ 2 ≤ (r ^ 2 - a ^ 2) * (r ^ 2 + a ^ 2 * t ^ 2) := by
        have hgap_nonneg : 0 ≤ r ^ 2 - a ^ 2 := by
          nlinarith [ha, har]
        have hone_nonneg : 0 ≤ 1 - t ^ 2 := by
          nlinarith [ht_sq_le_one]
        have hfactor_nonneg : 0 ≤ r ^ 2 * (r ^ 2 - a ^ 2) * (1 - t ^ 2) := by
          positivity
        have hidentity :
            (r ^ 2 - a ^ 2) * (r ^ 2 + a ^ 2 * t ^ 2) - (r ^ 4 - a ^ 4) * t ^ 2 =
              r ^ 2 * (r ^ 2 - a ^ 2) * (1 - t ^ 2) := by
          ring
        nlinarith [hfactor_nonneg, hidentity]
      exact (div_le_iff₀ hden_pos).2 hmul
    simpa [pow_two] using hs_le

/-- Helper for Exercise 7: if the rotated real point `-I * x` lies in the Cassini interior, then
the source inequality reduces to the scalar bound `x^2 < r^2 - a^2`. -/
lemma cassini_rotated_real_bound
    {a r x : ℝ} (hx : -Complex.I * (x : ℂ) ∈ cassiniOvalInterior a r) :
    x ^ 2 < r ^ 2 - a ^ 2 := by
  rw [mem_cassiniOvalInterior] at hx
  have hrewrite :
      (-Complex.I * (x : ℂ)) ^ 2 - (a : ℂ) ^ 2 = -(((x ^ 2 + a ^ 2 : ℝ)) : ℂ) := by
    -- Squaring `-I * x` turns the Cassini expression into a negative real scalar.
    calc
      (-Complex.I * (x : ℂ)) ^ 2 - (a : ℂ) ^ 2 =
          (-Complex.I) ^ 2 * (x : ℂ) ^ 2 - (a : ℂ) ^ 2 := by ring
      _ = -(((x ^ 2 + a ^ 2 : ℝ)) : ℂ) := by
        simp [pow_two]
        ring
  have hscalar : x ^ 2 + a ^ 2 < r ^ 2 := by
    -- The norm of that negative real number is just the underlying nonnegative scalar.
    rw [hrewrite] at hx
    rw [norm_neg] at hx
    let s : ℝ := x ^ 2 + a ^ 2
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      positivity
    have hnorm_eq : ‖((s : ℝ) : ℂ)‖ = s := by
      have hsq : ‖((s : ℝ) : ℂ)‖ ^ 2 = s ^ 2 := by
        calc
          ‖((s : ℝ) : ℂ)‖ ^ 2 = Complex.normSq ((s : ℂ)) := Complex.sq_norm _
          _ = s ^ 2 := by
            simpa [pow_two] using Complex.normSq_ofReal s
      have hnorm_nonneg : 0 ≤ ‖((s : ℝ) : ℂ)‖ := norm_nonneg _
      nlinarith
    have hx' : ‖((s : ℝ) : ℂ)‖ < r ^ 2 := by
      simpa [s] using hx
    rw [hnorm_eq] at hx'
    simpa [s] using hx'
  nlinarith

/-- Helper for Exercise 7: a rotated real point lying in the Cassini interior already lies on the
imaginary-axis segment used in the source reflection argument. -/
lemma cassini_imaginary_axisSegment_of_rotated_real_mem
    {a r : ℝ} {x : ℝ} (hx : -Complex.I * (x : ℂ) ∈ cassiniOvalInterior a r) :
    -Complex.I * (x : ℂ) ∈ cassiniOvalImaginaryAxisSegment a r := by
  refine (mem_cassiniOvalImaginaryAxisSegment).2 ?_
  refine ⟨by simp, ?_⟩
  -- The rotated point has imaginary part `-x`, so the segment bound is exactly the scalar lemma.
  have hbound : x ^ 2 ≤ r ^ 2 - a ^ 2 := le_of_lt (cassini_rotated_real_bound hx)
  simpa [pow_two] using hbound

/-- Helper for Exercise 7: rotating a real point of the unit disc by `-I` lands on the unit-disc
imaginary-axis segment. -/
lemma unitDisc_imaginaryAxisSegment_of_rotated_real_mem_ball {x : ℝ}
    (hx : (x : ℂ) ∈ ball (0 : ℂ) 1) :
    -Complex.I * (x : ℂ) ∈ unitDiscImaginaryAxisSegment := by
  refine (mem_unitDiscImaginaryAxisSegment).2 ?_
  refine ⟨by simp, ?_⟩
  -- Rotation by `-I` preserves the norm, so the unit-disc bound is unchanged.
  have hnorm : ‖-Complex.I * (x : ℂ)‖ < 1 := by
    simpa [mem_ball_zero_iff] using hx
  exact le_of_lt hnorm

/-- Helper for Exercise 7: the rotated Cassini domain is open and stable under conjugation, which
is the domain input for Schwarz reflection after rotating the imaginary axis to the real axis. -/
lemma cassini_rotated_domain_symm {a r : ℝ} :
    let Drot : Set ℂ := (fun ζ : ℂ ↦ -Complex.I * ζ) ⁻¹' cassiniOvalInterior a r
    IsOpen Drot ∧ Set.MapsTo conj Drot Drot := by
  dsimp
  refine ⟨?_, ?_⟩
  · -- The rotated domain is the preimage of the open Cassini interior under a linear map.
    simpa using
      (isOpen_cassiniOvalInterior a r).preimage
        (show Continuous (fun ζ : ℂ ↦ -Complex.I * ζ) by fun_prop)
  · intro ζ hζ
    -- Route correction: transport the `z ↦ -conj z` symmetry through the rotation `ζ ↦ -I * ζ`.
    have hsymm :
        -conj (-Complex.I * ζ) ∈ cassiniOvalInterior a r :=
      cassiniOvalInterior_mapsTo_negConj hζ
    simpa using hsymm

/-- Helper for Exercise 7: on the rotated real axis, the forward branch takes real values after
the compensating factor `I`, which is the boundary condition for Schwarz reflection. -/
lemma cassini_rotated_forward_real_axis
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    let Drot : Set ℂ := (fun ζ : ℂ ↦ -Complex.I * ζ) ⁻¹' cassiniOvalInterior a r
    let u : ℂ → ℂ := fun ζ ↦ Complex.I * cassiniOvalToUnitDisc a r (-Complex.I * ζ)
    ∀ x : ℝ, (x : ℂ) ∈ Drot → conj (u (x : ℂ)) = u (x : ℂ) := by
  dsimp
  intro x hx
  have hseg :
      -Complex.I * (x : ℂ) ∈ cassiniOvalImaginaryAxisSegment a r :=
    cassini_imaginary_axisSegment_of_rotated_real_mem hx
  have hw_seg :
      cassiniOvalToUnitDisc a r (-Complex.I * (x : ℂ)) ∈ unitDiscImaginaryAxisSegment :=
    cassiniOvalToUnitDisc_isomorphism_imaginary_axis ha har hseg
  have hw_re :
      (cassiniOvalToUnitDisc a r (-Complex.I * (x : ℂ))).re = 0 :=
    (mem_unitDiscImaginaryAxisSegment.mp hw_seg).1
  have harg : -(Complex.I * (x : ℂ)) = -Complex.I * (x : ℂ) := by
    ring
  have hw_re' :
      (cassiniOvalToUnitDisc a r (-(Complex.I * (x : ℂ)))).re = 0 := by
    rw [harg]
    exact hw_re
  -- A point on the imaginary axis becomes real after multiplication by `I`.
  have him :
      (Complex.I * cassiniOvalToUnitDisc a r (-(Complex.I * (x : ℂ)))).im = 0 := by
    simp [Complex.mul_im, hw_re']
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, hw_re']
  · simp [Complex.mul_im, hw_re']

/-- Helper for Exercise 7: on the rotated real axis, the inverse branch also takes real values
after the compensating factor `I`, giving the inverse-side boundary condition for Schwarz
reflection. -/
lemma cassini_rotated_inverse_real_axis
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    let v : ℂ → ℂ := fun ξ ↦ Complex.I * unitDiscToCassiniOval a r (-Complex.I * ξ)
    ∀ x : ℝ, (x : ℂ) ∈ ball (0 : ℂ) 1 → conj (v (x : ℂ)) = v (x : ℂ) := by
  dsimp
  intro x hx
  have hseg :
      -Complex.I * (x : ℂ) ∈ unitDiscImaginaryAxisSegment :=
    unitDisc_imaginaryAxisSegment_of_rotated_real_mem_ball hx
  have hz_seg :
      unitDiscToCassiniOval a r (-Complex.I * (x : ℂ)) ∈ cassiniOvalImaginaryAxisSegment a r :=
    unitDiscToCassiniOval_mapsTo_imaginary_axis ha har hseg
  have hz_re :
      (unitDiscToCassiniOval a r (-Complex.I * (x : ℂ))).re = 0 :=
    (mem_cassiniOvalImaginaryAxisSegment.mp hz_seg).1
  have harg : -(Complex.I * (x : ℂ)) = -Complex.I * (x : ℂ) := by
    ring
  have hz_re' :
      (unitDiscToCassiniOval a r (-(Complex.I * (x : ℂ)))).re = 0 := by
    rw [harg]
    exact hz_re
  -- The inverse branch satisfies the same rotated real-axis boundary condition.
  have him :
      (Complex.I * unitDiscToCassiniOval a r (-(Complex.I * (x : ℂ)))).im = 0 := by
    simp [Complex.mul_im, hz_re']
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, hz_re']
  · simp [Complex.mul_im, hz_re']

/-- Helper for Exercise 7: the symmetry `z ↦ -conj z` sends the left half of the Cassini interior
to the right half, which is the point where the already constructed branch can be reused. -/
lemma negConj_mem_cassiniOvalRightHalf_of_mem_left
    {a r : ℝ} {z : ℂ} (hz : z ∈ cassiniOvalInterior a r) (hzre : z.re < 0) :
    -conj z ∈ cassiniOvalRightHalf a r := by
  refine (mem_cassiniOvalRightHalf).2 ?_
  refine ⟨cassiniOvalInterior_mapsTo_negConj hz, ?_⟩
  simpa [Complex.conj_re] using neg_pos.mpr hzre

/-- Helper for Exercise 7: the symmetry `w ↦ -conj w` sends the left half of the unit disc to the
right half-disc. -/
lemma negConj_mem_rightHalfUnitDisc_of_mem_left
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hwre : w.re < 0) :
    -conj w ∈ rightHalfUnitDisc := by
  rw [mem_rightHalfUnitDisc]
  refine ⟨?_, ?_⟩
  · -- Conjugation and multiplication by `-1` preserve the norm.
    rw [mem_ball_zero_iff] at hw ⊢
    simpa [Complex.norm_conj] using hw
  · simpa [Complex.conj_re] using neg_pos.mpr hwre

/-- Helper for Exercise 7: after rotating Schwarz reflection back, the nonnegative-real-part
formula is exactly the original forward branch on the Cassini side. -/
lemma cassini_reflected_forward_of_nonneg_re
    {a r : ℝ} {z : ℂ} (hzre : 0 ≤ z.re) :
    let u : ℂ → ℂ := fun ζ ↦ Complex.I * cassiniOvalToUnitDisc a r (-Complex.I * ζ)
    let F : ℂ → ℂ := fun z ↦ -Complex.I * schwarzReflection u (Complex.I * z)
    F z = cassiniOvalToUnitDisc a r z := by
  dsimp
  -- On `Re z ≥ 0`, the rotated point `I * z` lies in the closed upper half-plane.
  have hIm : 0 ≤ (Complex.I * z).im := by simpa using hzre
  rw [schwarzReflection_apply_of_nonneg_im (f := fun ζ ↦
    Complex.I * cassiniOvalToUnitDisc a r (-Complex.I * ζ)) (z := Complex.I * z) hIm]
  calc
    -Complex.I * (Complex.I * cassiniOvalToUnitDisc a r (-Complex.I * (Complex.I * z))) =
        ((-Complex.I) * Complex.I) *
          cassiniOvalToUnitDisc a r (-Complex.I * (Complex.I * z)) := by
      ring
    _ = cassiniOvalToUnitDisc a r z := by
      have harg : -Complex.I * (Complex.I * z) = z := by
        calc
          -Complex.I * (Complex.I * z) = ((-Complex.I) * Complex.I) * z := by ring
          _ = z := by simp
      simp [harg]

/-- Helper for Exercise 7: on the left half of the Cassini interior, the reflected forward branch
reduces to the explicit formula `-conj (f (-conj z))`. -/
lemma cassini_reflected_forward_of_neg_re
    {a r : ℝ} {z : ℂ} (hzre : z.re < 0) :
    let u : ℂ → ℂ := fun ζ ↦ Complex.I * cassiniOvalToUnitDisc a r (-Complex.I * ζ)
    let F : ℂ → ℂ := fun z ↦ -Complex.I * schwarzReflection u (Complex.I * z)
    F z = -conj (cassiniOvalToUnitDisc a r (-conj z)) := by
  dsimp
  -- On `Re z < 0`, Schwarz reflection uses the conjugated lower-half formula.
  have hIm : (Complex.I * z).im < 0 := by simpa using hzre
  rw [schwarzReflection_apply_of_neg_im (f := fun ζ ↦
    Complex.I * cassiniOvalToUnitDisc a r (-Complex.I * ζ)) (z := Complex.I * z) hIm]
  have harg : -Complex.I * conj (Complex.I * z) = -conj z := by
    calc
      -Complex.I * conj (Complex.I * z) = -Complex.I * (-Complex.I * conj z) := by
        simp
      _ = ((-Complex.I) * (-Complex.I)) * conj z := by
        ring
      _ = -conj z := by
        simp
  rw [harg]
  calc
    -Complex.I * conj (Complex.I * cassiniOvalToUnitDisc a r (-conj z)) =
        -Complex.I * (-Complex.I * conj (cassiniOvalToUnitDisc a r (-conj z))) := by
      simp
    _ = ((-Complex.I) * (-Complex.I)) *
          conj (cassiniOvalToUnitDisc a r (-conj z)) := by
      ring
    _ = -conj (cassiniOvalToUnitDisc a r (-conj z)) := by
      simp

/-- Helper for Exercise 7: after rotating Schwarz reflection back, the nonnegative-real-part
formula is exactly the original inverse branch on the unit-disc side. -/
lemma cassini_reflected_inverse_of_nonneg_re
    {a r : ℝ} {w : ℂ} (hwre : 0 ≤ w.re) :
    let v : ℂ → ℂ := fun ξ ↦ Complex.I * unitDiscToCassiniOval a r (-Complex.I * ξ)
    let G : ℂ → ℂ := fun w ↦ -Complex.I * schwarzReflection v (Complex.I * w)
    G w = unitDiscToCassiniOval a r w := by
  dsimp
  -- The same upper-half evaluation gives the original inverse branch on `Re w ≥ 0`.
  have hIm : 0 ≤ (Complex.I * w).im := by simpa using hwre
  rw [schwarzReflection_apply_of_nonneg_im (f := fun ξ ↦
    Complex.I * unitDiscToCassiniOval a r (-Complex.I * ξ)) (z := Complex.I * w) hIm]
  calc
    -Complex.I * (Complex.I * unitDiscToCassiniOval a r (-Complex.I * (Complex.I * w))) =
        ((-Complex.I) * Complex.I) *
          unitDiscToCassiniOval a r (-Complex.I * (Complex.I * w)) := by
      ring
    _ = unitDiscToCassiniOval a r w := by
      have harg : -Complex.I * (Complex.I * w) = w := by
        calc
          -Complex.I * (Complex.I * w) = ((-Complex.I) * Complex.I) * w := by ring
          _ = w := by simp
      simp [harg]

/-- Helper for Exercise 7: on the left half of the unit disc, the reflected inverse branch
reduces to the explicit formula `-conj (g (-conj w))`. -/
lemma cassini_reflected_inverse_of_neg_re
    {a r : ℝ} {w : ℂ} (hwre : w.re < 0) :
    let v : ℂ → ℂ := fun ξ ↦ Complex.I * unitDiscToCassiniOval a r (-Complex.I * ξ)
    let G : ℂ → ℂ := fun w ↦ -Complex.I * schwarzReflection v (Complex.I * w)
    G w = -conj (unitDiscToCassiniOval a r (-conj w)) := by
  dsimp
  -- On `Re w < 0`, Schwarz reflection switches to the conjugated lower-half formula.
  have hIm : (Complex.I * w).im < 0 := by simpa using hwre
  rw [schwarzReflection_apply_of_neg_im (f := fun ξ ↦
    Complex.I * unitDiscToCassiniOval a r (-Complex.I * ξ)) (z := Complex.I * w) hIm]
  have harg : -Complex.I * conj (Complex.I * w) = -conj w := by
    calc
      -Complex.I * conj (Complex.I * w) = -Complex.I * (-Complex.I * conj w) := by
        simp
      _ = ((-Complex.I) * (-Complex.I)) * conj w := by
        ring
      _ = -conj w := by
        simp
  rw [harg]
  calc
    -Complex.I * conj (Complex.I * unitDiscToCassiniOval a r (-conj w)) =
        -Complex.I * (-Complex.I * conj (unitDiscToCassiniOval a r (-conj w))) := by
      simp
    _ = ((-Complex.I) * (-Complex.I)) *
          conj (unitDiscToCassiniOval a r (-conj w)) := by
      ring
    _ = -conj (unitDiscToCassiniOval a r (-conj w)) := by
      simp

/-- Helper for Exercise 7: the remaining global step is the reflected gluing package that rotates
the right-half isomorphism, applies Schwarz reflection, and rotates back. -/
theorem cassini_rotated_reflection_package
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ∃ F G : ℂ → ℂ,
      AnalyticOnNhd ℂ F (cassiniOvalInterior a r) ∧
        Set.MapsTo F (cassiniOvalInterior a r) (ball (0 : ℂ) 1) ∧
        AnalyticOnNhd ℂ G (ball (0 : ℂ) 1) ∧
        Set.MapsTo G (ball (0 : ℂ) 1) (cassiniOvalInterior a r) ∧
        Set.EqOn (G ∘ F) id (cassiniOvalInterior a r) ∧
        Set.EqOn (F ∘ G) id (ball (0 : ℂ) 1) ∧
        Set.MapsTo F (cassiniOvalInteriorRealSlice a r) openUnitDiscRealSlice ∧
        Set.MapsTo F (cassiniOvalImaginaryAxisSegment a r) unitDiscImaginaryAxisSegment := by
  -- Route correction: the right-half branch is already complete; the only remaining work is the
  -- source-faithful rotation-plus-Schwarz-reflection package that glues it to the left half.
  let Drot : Set ℂ := (fun ζ : ℂ ↦ -Complex.I * ζ) ⁻¹' cassiniOvalInterior a r
  let u : ℂ → ℂ := fun ζ ↦ Complex.I * cassiniOvalToUnitDisc a r (-Complex.I * ζ)
  let v : ℂ → ℂ := fun ξ ↦ Complex.I * unitDiscToCassiniOval a r (-Complex.I * ξ)
  let F : ℂ → ℂ := fun z ↦ -Complex.I * schwarzReflection u (Complex.I * z)
  let G : ℂ → ℂ := fun w ↦ -Complex.I * schwarzReflection v (Complex.I * w)
  have hDrot : IsOpen Drot ∧ Set.MapsTo conj Drot Drot := by
    simpa [Drot] using (cassini_rotated_domain_symm (a := a) (r := r))
  have hu_real :
      ∀ x : ℝ, (x : ℂ) ∈ Drot → conj (u (x : ℂ)) = u (x : ℂ) := by
    simpa [Drot, u] using cassini_rotated_forward_real_axis (a := a) (r := r) ha har
  have hv_real :
      ∀ x : ℝ, (x : ℂ) ∈ ball (0 : ℂ) 1 → conj (v (x : ℂ)) = v (x : ℂ) := by
    simpa [v] using cassini_rotated_inverse_real_axis (a := a) (r := r) ha har
  have hF_maps : Set.MapsTo F (cassiniOvalInterior a r) (ball (0 : ℂ) 1) := by
    intro z hz
    by_cases hzre : 0 ≤ z.re
    · -- On the nonnegative side, the reflected formula is just the original branch.
      rw [show F z = cassiniOvalToUnitDisc a r z by
        simpa [F, u] using cassini_reflected_forward_of_nonneg_re
          (a := a) (r := r) (z := z) hzre]
      exact cassiniOvalToUnitDisc_mem_ball_of_mem_cassiniOvalInterior ha har hz
    · have hzre' : z.re < 0 := lt_of_not_ge hzre
      -- On the left half, reflect to the already solved right-half branch.
      rw [show F z = -conj (cassiniOvalToUnitDisc a r (-conj z)) by
        simpa [F, u] using cassini_reflected_forward_of_neg_re
          (a := a) (r := r) (z := z) hzre']
      have hz_right : -conj z ∈ cassiniOvalRightHalf a r :=
        negConj_mem_cassiniOvalRightHalf_of_mem_left hz hzre'
      have hw_right :
          cassiniOvalToUnitDisc a r (-conj z) ∈ rightHalfUnitDisc :=
        cassiniOvalToUnitDisc_isomorphism_mapsTo ha har hz_right
      have hw_ball : cassiniOvalToUnitDisc a r (-conj z) ∈ ball (0 : ℂ) 1 :=
        (mem_rightHalfUnitDisc.mp hw_right).1
      rw [mem_ball_zero_iff] at hw_ball ⊢
      simpa [Complex.norm_conj] using hw_ball
  have hG_maps : Set.MapsTo G (ball (0 : ℂ) 1) (cassiniOvalInterior a r) := by
    intro w hw
    by_cases hwre : 0 ≤ w.re
    · -- On the nonnegative side, the reflected inverse is the original inverse branch.
      rw [show G w = unitDiscToCassiniOval a r w by
        simpa [G, v] using cassini_reflected_inverse_of_nonneg_re
          (a := a) (r := r) (w := w) hwre]
      exact unitDiscToCassiniOval_mem_cassiniOvalInterior_of_mem_ball ha har hw
    · have hwre' : w.re < 0 := lt_of_not_ge hwre
      -- On the left half of the disc, reduce to the right-half inverse and reflect back.
      rw [show G w = -conj (unitDiscToCassiniOval a r (-conj w)) by
        simpa [G, v] using cassini_reflected_inverse_of_neg_re
          (a := a) (r := r) (w := w) hwre']
      have hw_right : -conj w ∈ rightHalfUnitDisc :=
        negConj_mem_rightHalfUnitDisc_of_mem_left hw hwre'
      have hz_right :
          unitDiscToCassiniOval a r (-conj w) ∈ cassiniOvalRightHalf a r :=
        cassiniOvalToUnitDisc_isomorphism_inv_mapsTo ha har hw_right
      exact cassiniOvalInterior_mapsTo_negConj (mem_cassiniOvalRightHalf.mp hz_right).1
  have hreal : Set.MapsTo F (cassiniOvalInteriorRealSlice a r) openUnitDiscRealSlice := by
    intro z hz
    rcases mem_cassiniOvalInteriorRealSlice.mp hz with ⟨hzCassini, hz_im⟩
    by_cases hzre : 0 ≤ z.re
    · rw [show F z = cassiniOvalToUnitDisc a r z by
        simpa [F, u] using cassini_reflected_forward_of_nonneg_re
          (a := a) (r := r) (z := z) hzre]
      by_cases hzre_pos : 0 < z.re
      · have hz_right : z ∈ cassiniOvalRightHalf a r := (mem_cassiniOvalRightHalf).2 ⟨hzCassini, hzre_pos⟩
        have hw_real :
            cassiniOvalToUnitDisc a r z ∈ {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} :=
          cassiniOvalToUnitDisc_isomorphism_real_slice ha har ⟨hz_right, hz_im⟩
        exact ⟨(mem_rightHalfUnitDisc.mp hw_real.1).1, hw_real.2⟩
      · have hz_re_zero : z.re = 0 := le_antisymm (le_of_not_gt hzre_pos) hzre
        have hz_zero : z = 0 := by
          apply Complex.ext <;> simp [hz_re_zero, hz_im]
        rw [hz_zero]
        -- The origin is fixed by the explicit square-root formula.
        simp [openUnitDiscRealSlice, cassiniOvalToUnitDisc, cassiniOvalMobius_zero]
    · have hzre' : z.re < 0 := lt_of_not_ge hzre
      rw [show F z = -conj (cassiniOvalToUnitDisc a r (-conj z)) by
        simpa [F, u] using cassini_reflected_forward_of_neg_re
          (a := a) (r := r) (z := z) hzre']
      have hz_right : -conj z ∈ cassiniOvalRightHalf a r :=
        negConj_mem_cassiniOvalRightHalf_of_mem_left hzCassini hzre'
      have hw_real :
          cassiniOvalToUnitDisc a r (-conj z) ∈ {w | w ∈ rightHalfUnitDisc ∧ w.im = 0} :=
        cassiniOvalToUnitDisc_isomorphism_real_slice ha har
          ⟨hz_right, by simpa [hz_im]⟩
      have hw_ball : cassiniOvalToUnitDisc a r (-conj z) ∈ ball (0 : ℂ) 1 :=
        (mem_rightHalfUnitDisc.mp hw_real.1).1
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff] at hw_ball ⊢
        simpa [Complex.norm_conj] using hw_ball
      · simp [hw_real.2]
  have himag : Set.MapsTo F (cassiniOvalImaginaryAxisSegment a r) unitDiscImaginaryAxisSegment := by
    intro z hz
    have hzre : 0 ≤ z.re := by
      simpa [(mem_cassiniOvalImaginaryAxisSegment.mp hz).1]
    rw [show F z = cassiniOvalToUnitDisc a r z by
      simpa [F, u] using cassini_reflected_forward_of_nonneg_re
        (a := a) (r := r) (z := z) hzre]
    exact cassiniOvalToUnitDisc_isomorphism_imaginary_axis ha har hz
  have hF_analytic : AnalyticOnNhd ℂ F (cassiniOvalInterior a r) := by
    -- TODO: the proof route is stable, but the remaining blocker is a clean proof that the
    -- rotated branch `u` is continuous on `Drot ∩ {ζ | 0 ≤ ζ.im}`. The strict-upper-slice
    -- analyticity is clear from the right-half package; the missing input is the one-sided
    -- continuity of the principal square-root branch on the rotated real axis.
    sorry
  have hG_analytic : AnalyticOnNhd ℂ G (ball (0 : ℂ) 1) := by
    -- TODO: the inverse side has the same stable blocker as the forward side: continuity of the
    -- rotated branch `v` on the closed upper half-disc. The strict-upper-slice analyticity is
    -- already available from the right-half inverse package.
    sorry
  have hGF : Set.EqOn (G ∘ F) id (cassiniOvalInterior a r) := by
    intro z hz
    by_cases hz_pos : 0 < z.re
    · have hz_right : z ∈ cassiniOvalRightHalf a r := (mem_cassiniOvalRightHalf).2 ⟨hz, hz_pos⟩
      have hF_eq : F z = cassiniOvalToUnitDisc a r z := by
        -- On the open right half, the reflected branch is the original forward branch.
        simpa [F, u] using cassini_reflected_forward_of_nonneg_re
          (a := a) (r := r) (z := z) (le_of_lt hz_pos)
      have hw_right : cassiniOvalToUnitDisc a r z ∈ rightHalfUnitDisc :=
        cassiniOvalToUnitDisc_isomorphism_mapsTo ha har hz_right
      have hG_eq :
          G (cassiniOvalToUnitDisc a r z) =
            unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z) := by
        simpa [G, v] using cassini_reflected_inverse_of_nonneg_re
          (a := a) (r := r) (w := cassiniOvalToUnitDisc a r z)
          (le_of_lt (mem_rightHalfUnitDisc.mp hw_right).2)
      have hleft :
          unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z) = z := by
        simpa [Function.comp] using
          cassiniOvalToUnitDisc_isomorphism_left_inv (a := a) (r := r) ha har hz_right
      calc
        (G ∘ F) z = G (cassiniOvalToUnitDisc a r z) := by
          simp [Function.comp, hF_eq]
        _ = unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r z) := hG_eq
        _ = z := hleft
    · by_cases hz_neg : z.re < 0
      · have hz_right : -conj z ∈ cassiniOvalRightHalf a r :=
          negConj_mem_cassiniOvalRightHalf_of_mem_left hz hz_neg
        have hw_right :
            cassiniOvalToUnitDisc a r (-conj z) ∈ rightHalfUnitDisc :=
          cassiniOvalToUnitDisc_isomorphism_mapsTo ha har hz_right
        have hF_eq : F z = -conj (cassiniOvalToUnitDisc a r (-conj z)) := by
          -- On the open left half, reflection gives the conjugated branch formula.
          simpa [F, u] using cassini_reflected_forward_of_neg_re
            (a := a) (r := r) (z := z) hz_neg
        have hF_re_neg : (F z).re < 0 := by
          rw [hF_eq]
          have hpos : 0 < (cassiniOvalToUnitDisc a r (-conj z)).re :=
            (mem_rightHalfUnitDisc.mp hw_right).2
          have hneg : -((cassiniOvalToUnitDisc a r (-conj z)).re) < 0 := by
            linarith
          simpa [Complex.conj_re] using hneg
        have hG_eq :
            G (F z) = -conj (unitDiscToCassiniOval a r (-conj (F z))) := by
          simpa [G, v] using cassini_reflected_inverse_of_neg_re
            (a := a) (r := r) (w := F z) hF_re_neg
        have hleft :
            unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r (-conj z)) = -conj z := by
          simpa [Function.comp] using
            cassiniOvalToUnitDisc_isomorphism_left_inv (a := a) (r := r) ha har hz_right
        calc
          (G ∘ F) z = -conj (unitDiscToCassiniOval a r (-conj (F z))) := hG_eq
          _ = -conj (unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r (-conj z))) := by
            rw [hF_eq]
            simp
          _ = -conj (-conj z) := by rw [hleft]
          _ = z := by simp
      · have hz_axis : z.re = 0 := by
          exact le_antisymm (le_of_not_gt hz_pos) (le_of_not_gt hz_neg)
        rcases Metric.mem_nhds_iff.mp ((isOpen_cassiniOvalInterior a r).mem_nhds hz) with
          ⟨ε, hεpos, hεsub⟩
        let B : Set ℂ := ball z ε
        let z₀ : ℂ := z + ((ε / 2 : ℝ) : ℂ)
        have hz₀_mem : z₀ ∈ B ∩ {w : ℂ | 0 < w.re} := by
          refine ⟨?_, ?_⟩
          · -- Move a short distance to the right inside the containing ball.
            rw [mem_ball, dist_eq_norm]
            have hhalf : 0 < ε / 2 := by linarith
            have hhalf_nonneg : 0 ≤ ε / 2 := by linarith
            have hshift : z₀ - z = ((ε / 2 : ℝ) : ℂ) := by
              simp [z₀]
            rw [hshift, Complex.norm_real, Real.norm_of_nonneg hhalf_nonneg]
            linarith
          · -- The shifted point has strictly positive real part because `Re z = 0`.
            simp [z₀, hz_axis, hεpos]
        have hGF_ball_analytic : AnalyticOnNhd ℂ (G ∘ F) B := by
          -- Restrict the global analytic maps to the small ball inside the Cassini interior.
          exact hG_analytic.comp (hF_analytic.mono hεsub) (by
            intro w hw
            exact hF_maps (hεsub hw))
        have hEqOn_right : Set.EqOn (G ∘ F) id (B ∩ {w : ℂ | 0 < w.re}) := by
          intro w hw
          have hwCassini : w ∈ cassiniOvalInterior a r := hεsub hw.1
          have hw_right : w ∈ cassiniOvalRightHalf a r :=
            (mem_cassiniOvalRightHalf).2 ⟨hwCassini, hw.2⟩
          have hF_eq : F w = cassiniOvalToUnitDisc a r w := by
            simpa [F, u] using cassini_reflected_forward_of_nonneg_re
              (a := a) (r := r) (z := w) (le_of_lt hw.2)
          have hw_image : cassiniOvalToUnitDisc a r w ∈ rightHalfUnitDisc :=
            cassiniOvalToUnitDisc_isomorphism_mapsTo ha har hw_right
          have hG_eq :
              G (cassiniOvalToUnitDisc a r w) =
                unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r w) := by
            simpa [G, v] using cassini_reflected_inverse_of_nonneg_re
              (a := a) (r := r) (w := cassiniOvalToUnitDisc a r w)
              (le_of_lt (mem_rightHalfUnitDisc.mp hw_image).2)
          have hleft :
              unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r w) = w := by
            simpa [Function.comp] using
              cassiniOvalToUnitDisc_isomorphism_left_inv (a := a) (r := r) ha har hw_right
          calc
            (G ∘ F) w = G (cassiniOvalToUnitDisc a r w) := by
              simp [Function.comp, hF_eq]
            _ = unitDiscToCassiniOval a r (cassiniOvalToUnitDisc a r w) := hG_eq
            _ = w := hleft
        have heventually : (G ∘ F) =ᶠ[nhds z₀] id := by
          -- Equality on the open right slice of the ball is enough to start analytic continuation.
          exact hEqOn_right.eventuallyEq_of_mem
            ((Metric.isOpen_ball.inter
              (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds hz₀_mem)
        have hEqOn_ball : Set.EqOn (G ∘ F) id B := by
          exact hGF_ball_analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id
            Metric.isPreconnected_ball hz₀_mem.1 heventually
        exact hEqOn_ball (mem_ball_self hεpos)
  have hFG : Set.EqOn (F ∘ G) id (ball (0 : ℂ) 1) := by
    intro w hw
    by_cases hw_pos : 0 < w.re
    · have hw_right : w ∈ rightHalfUnitDisc := (mem_rightHalfUnitDisc).2 ⟨hw, hw_pos⟩
      have hG_eq : G w = unitDiscToCassiniOval a r w := by
        -- On the open right half-disc, the reflected inverse is the original inverse branch.
        simpa [G, v] using cassini_reflected_inverse_of_nonneg_re
          (a := a) (r := r) (w := w) (le_of_lt hw_pos)
      have hz_right : unitDiscToCassiniOval a r w ∈ cassiniOvalRightHalf a r :=
        cassiniOvalToUnitDisc_isomorphism_inv_mapsTo ha har hw_right
      have hF_eq :
          F (unitDiscToCassiniOval a r w) =
            cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w) := by
        simpa [F, u] using cassini_reflected_forward_of_nonneg_re
          (a := a) (r := r) (z := unitDiscToCassiniOval a r w)
          (le_of_lt (mem_cassiniOvalRightHalf.mp hz_right).2)
      have hright :
          cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w) = w := by
        simpa [Function.comp] using
          cassiniOvalToUnitDisc_isomorphism_right_inv (a := a) (r := r) ha har hw_right
      calc
        (F ∘ G) w = F (unitDiscToCassiniOval a r w) := by
          simp [Function.comp, hG_eq]
        _ = cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r w) := hF_eq
        _ = w := hright
    · by_cases hw_neg : w.re < 0
      · have hw_right : -conj w ∈ rightHalfUnitDisc :=
          negConj_mem_rightHalfUnitDisc_of_mem_left hw hw_neg
        have hz_right :
            unitDiscToCassiniOval a r (-conj w) ∈ cassiniOvalRightHalf a r :=
          cassiniOvalToUnitDisc_isomorphism_inv_mapsTo ha har hw_right
        have hG_eq : G w = -conj (unitDiscToCassiniOval a r (-conj w)) := by
          -- On the left half-disc, reflection gives the conjugated inverse formula.
          simpa [G, v] using cassini_reflected_inverse_of_neg_re
            (a := a) (r := r) (w := w) hw_neg
        have hG_re_neg : (G w).re < 0 := by
          rw [hG_eq]
          have hpos : 0 < (unitDiscToCassiniOval a r (-conj w)).re :=
            (mem_cassiniOvalRightHalf.mp hz_right).2
          have hneg : -((unitDiscToCassiniOval a r (-conj w)).re) < 0 := by
            linarith
          simpa [Complex.conj_re] using hneg
        have hF_eq :
            F (G w) = -conj (cassiniOvalToUnitDisc a r (-conj (G w))) := by
          simpa [F, u] using cassini_reflected_forward_of_neg_re
            (a := a) (r := r) (z := G w) hG_re_neg
        have hright :
            cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r (-conj w)) = -conj w := by
          simpa [Function.comp] using
            cassiniOvalToUnitDisc_isomorphism_right_inv (a := a) (r := r) ha har hw_right
        calc
          (F ∘ G) w = -conj (cassiniOvalToUnitDisc a r (-conj (G w))) := hF_eq
          _ = -conj (cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r (-conj w))) := by
            rw [hG_eq]
            simp
          _ = -conj (-conj w) := by rw [hright]
          _ = w := by simp
      · have hw_axis : w.re = 0 := by
          exact le_antisymm (le_of_not_gt hw_pos) (le_of_not_gt hw_neg)
        rcases Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hw) with
          ⟨ε, hεpos, hεsub⟩
        let B : Set ℂ := ball w ε
        let w₀ : ℂ := w + ((ε / 2 : ℝ) : ℂ)
        have hw₀_mem : w₀ ∈ B ∩ {ζ : ℂ | 0 < ζ.re} := by
          refine ⟨?_, ?_⟩
          · -- Shift slightly into the open right half-disc while staying inside the ball.
            rw [mem_ball, dist_eq_norm]
            have hhalf : 0 < ε / 2 := by linarith
            have hhalf_nonneg : 0 ≤ ε / 2 := by linarith
            have hshift : w₀ - w = ((ε / 2 : ℝ) : ℂ) := by
              simp [w₀]
            rw [hshift, Complex.norm_real, Real.norm_of_nonneg hhalf_nonneg]
            linarith
          · -- The chosen comparison point has positive real part.
            simp [w₀, hw_axis, hεpos]
        have hFG_ball_analytic : AnalyticOnNhd ℂ (F ∘ G) B := by
          -- Restrict the global analytic maps to the small ball inside the unit disc.
          exact hF_analytic.comp (hG_analytic.mono hεsub) (by
            intro ζ hζ
            exact hG_maps (hεsub hζ))
        have hEqOn_right : Set.EqOn (F ∘ G) id (B ∩ {ζ : ℂ | 0 < ζ.re}) := by
          intro ζ hζ
          have hζ_disc : ζ ∈ ball (0 : ℂ) 1 := hεsub hζ.1
          have hζ_right : ζ ∈ rightHalfUnitDisc := (mem_rightHalfUnitDisc).2 ⟨hζ_disc, hζ.2⟩
          have hG_eq : G ζ = unitDiscToCassiniOval a r ζ := by
            simpa [G, v] using cassini_reflected_inverse_of_nonneg_re
              (a := a) (r := r) (w := ζ) (le_of_lt hζ.2)
          have hz_right : unitDiscToCassiniOval a r ζ ∈ cassiniOvalRightHalf a r :=
            cassiniOvalToUnitDisc_isomorphism_inv_mapsTo ha har hζ_right
          have hF_eq :
              F (unitDiscToCassiniOval a r ζ) =
                cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r ζ) := by
            simpa [F, u] using cassini_reflected_forward_of_nonneg_re
              (a := a) (r := r) (z := unitDiscToCassiniOval a r ζ)
              (le_of_lt (mem_cassiniOvalRightHalf.mp hz_right).2)
          have hright :
              cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r ζ) = ζ := by
            simpa [Function.comp] using
              cassiniOvalToUnitDisc_isomorphism_right_inv (a := a) (r := r) ha har hζ_right
          calc
            (F ∘ G) ζ = F (unitDiscToCassiniOval a r ζ) := by
              simp [Function.comp, hG_eq]
            _ = cassiniOvalToUnitDisc a r (unitDiscToCassiniOval a r ζ) := hF_eq
            _ = ζ := hright
        have heventually : (F ∘ G) =ᶠ[nhds w₀] id := by
          -- Equality on the right slice of the ball gives a local coincidence point.
          exact hEqOn_right.eventuallyEq_of_mem
            ((Metric.isOpen_ball.inter
              (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds hw₀_mem)
        have hEqOn_ball : Set.EqOn (F ∘ G) id B := by
          exact hFG_ball_analytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id
            Metric.isPreconnected_ball hw₀_mem.1 heventually
        exact hEqOn_ball (mem_ball_self hεpos)
  exact ⟨F, G, hF_analytic, hF_maps, hG_analytic, hG_maps, hGF, hFG, hreal, himag⟩

/-- Exercise 7, global source-facing form: the whole Cassini oval is biholomorphic to the unit
disc by gluing the right-half branch with its reflected branch, preserving the symmetry axes. The
global map is not the single even formula `cassiniOvalToUnitDisc`; that formula is only the
right-half branch used in the construction. -/
theorem exists_cassiniOvalInterior_iso_unitDisc_preserving_axes
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ∃ e : HolomorphicIsomorph (cassiniOvalInterior a r) (ball (0 : ℂ) 1),
      Set.MapsTo (e : ℂ → ℂ) (cassiniOvalInteriorRealSlice a r) openUnitDiscRealSlice ∧
        Set.MapsTo (e : ℂ → ℂ)
          (cassiniOvalImaginaryAxisSegment a r) unitDiscImaginaryAxisSegment := by
  -- Package the reflected forward and inverse branches into the chapter owner.
  rcases cassini_rotated_reflection_package ha har with
    ⟨F, G, hF_analytic, hF_maps, hG_analytic, hG_maps, hGF, hFG, hreal, himag⟩
  refine ⟨⟨
    { toFun := F
      invFun := G
      source := cassiniOvalInterior a r
      target := ball (0 : ℂ) 1
      map_source' := hF_maps
      map_target' := hG_maps
      left_inv' := hGF
      right_inv' := hFG
      open_source := isOpen_cassiniOvalInterior a r
      open_target := Metric.isOpen_ball
      continuousOn_toFun := hF_analytic.continuousOn
      continuousOn_invFun := hG_analytic.continuousOn },
    { source_eq := rfl
      target_eq := rfl
      analyticOn_toFun := hF_analytic
      analyticOn_symm := hG_analytic }⟩, hreal, himag⟩

end
