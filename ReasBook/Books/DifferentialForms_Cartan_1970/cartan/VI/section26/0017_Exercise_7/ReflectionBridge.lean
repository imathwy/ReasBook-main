import DifferentialForms_Cartan_1970.VI.section26.«0017_Exercise_7».RightHalfBranch

open Metric Set ComplexOrder
open scoped ComplexConjugate

noncomputable section

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

end
