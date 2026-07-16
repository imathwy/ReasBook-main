import Mathlib
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import DifferentialForms_Cartan_1970.cartan.III.section11.PeriodLattice
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»

open Set
open scoped UpperHalfPlane

noncomputable section

/-- The modulus parameter `k` from Exercise 8, constrained by `0 < k < 1`. -/
abbrev Exercise8Modulus := Set.Ioo (0 : ℝ) 1

namespace Exercise8Modulus

/-- An Exercise 8 modulus is positive. -/
theorem pos (k : Exercise8Modulus) : 0 < (k : ℝ) :=
  k.2.1

/-- An Exercise 8 modulus is strictly smaller than `1`. -/
theorem lt_one (k : Exercise8Modulus) : (k : ℝ) < 1 :=
  k.2.2

end Exercise8Modulus

/-- The closed upper half-plane `Im z ≥ 0`. -/
abbrev ClosedUpperHalfPlane :=
  {z : ℂ // 0 ≤ z.im}

/-- The radicand appearing in Cartan Exercise 8. -/
def exercise8_radicand (k : Exercise8Modulus) (z : ℂ) : ℂ :=
  ((1 : ℂ) - z ^ (2 : ℕ)) * ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ))

/-- Source-faithful data for the square-root branch in Cartan Exercise 8.

The text does not use the global principal square root. It asks for the simple branch of
`sqrt ((1 - z^2) (1 - k^2 z^2))` on the upper half-plane, normalized to take value `1` at
`z = 0`. The function is represented on all of `ℂ` only so the path integral can be written with
the existing curve-integral API; the branch laws below are the intended domain-specific content. -/
structure Exercise8SimpleSqrtBranch (k : Exercise8Modulus) where
  branch : ℂ → ℂ
  branch_sq_eq_on_upper :
    ∀ ⦃z : ℂ⦄, 0 < z.im → branch z ^ (2 : ℕ) = exercise8_radicand k z
  branch_ne_zero_on_upper : ∀ ⦃z : ℂ⦄, 0 < z.im → branch z ≠ 0
  continuousOn_upper : ContinuousOn branch {z : ℂ | 0 < z.im}
  differentiableOn_upper : DifferentiableOn ℂ branch {z : ℂ | 0 < z.im}
  branch_eq_principal_at_I : branch Complex.I = Complex.sqrt (exercise8_radicand k Complex.I)
  branch_zero : branch 0 = 1

/-- Existence of the normalized simple square-root branch used in Cartan Exercise 8. -/
theorem exercise8_simple_sqrt_branch_exists (k : Exercise8Modulus) :
    Nonempty (Exercise8SimpleSqrtBranch k) := by
  -- The upper half-plane is convex, hence simply connected. On a simply connected open set a
  -- nonvanishing holomorphic function admits a continuous square root branch, and differentiability
  -- follows by differentiating the identity `branch^2 = radicand`.
  have hconv : Convex ℝ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using convex_halfSpace_im_gt (0 : ℝ)
  have hnonempty : (UpperHalfPlane.upperHalfPlaneSet).Nonempty := by
    refine ⟨Complex.I, ?_⟩
    simp [UpperHalfPlane.upperHalfPlaneSet]
  have hrad_ne_zero_upper : ∀ ⦃z : ℂ⦄, 0 < z.im → exercise8_radicand k z ≠ 0 := by
    intro z hz
    refine mul_ne_zero ?_ ?_
    · intro hfactor
      have hz_sq : z ^ (2 : ℕ) = ((1 : ℂ) ^ (2 : ℕ)) := by
        have : (1 : ℂ) = z ^ (2 : ℕ) := sub_eq_zero.mp hfactor
        simpa using this.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz_sq with hreal | hreal
      · have : z.im = 0 := by simpa [hreal]
        exact hz.ne' this
      · have : z.im = 0 := by simpa [hreal]
        exact hz.ne' this
    · intro hfactor
      have hk_ne : (k : ℂ) ≠ 0 := by
        exact_mod_cast (Exercise8Modulus.pos k).ne'
      have hk_sq_ne : ((k : ℂ) ^ (2 : ℕ)) ≠ 0 := pow_ne_zero _ hk_ne
      have hz_sq : z ^ (2 : ℕ) = (1 / (k : ℂ)) ^ (2 : ℕ) := by
        apply mul_left_cancel₀ hk_sq_ne
        calc
          ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) = 1 := by
            exact (sub_eq_zero.mp hfactor).symm
          _ = ((k : ℂ) ^ (2 : ℕ)) * (1 / (k : ℂ)) ^ (2 : ℕ) := by
            field_simp [hk_ne]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz_sq with hreal | hreal
      · have : z.im = 0 := by simpa [hreal]
        exact hz.ne' this
      · have : z.im = 0 := by simpa [hreal]
        exact hz.ne' this
  have hsimply : IsSimplyConnected UpperHalfPlane.upperHalfPlaneSet := by
    letI : ContractibleSpace UpperHalfPlane.upperHalfPlaneSet := hconv.contractibleSpace hnonempty
    exact (show SimplyConnectedSpace UpperHalfPlane.upperHalfPlaneSet from inferInstance)
  have hopen : IsOpen UpperHalfPlane.upperHalfPlaneSet :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hrad_cont : ContinuousOn (exercise8_radicand k) UpperHalfPlane.upperHalfPlaneSet := by
    simpa [exercise8_radicand] using
      ((continuous_const.sub (continuous_id.pow 2)).mul
        (continuous_const.sub (continuous_const.mul (continuous_id.pow 2)))).continuousOn
  have hrad_nonzero :
      0 ∉ exercise8_radicand k '' UpperHalfPlane.upperHalfPlaneSet := by
    intro hzero
    rcases hzero with ⟨z, hz, hz0⟩
    exact hrad_ne_zero_upper hz hz0
  rcases Complex.exists_continuousOn_pow_eq hsimply hopen hrad_cont hrad_nonzero two_ne_zero with
    ⟨f, hfc, hpow⟩
  let principalI : ℂ := Complex.sqrt (exercise8_radicand k Complex.I)
  let signedBranch : ℂ → ℂ := fun z ↦ if f Complex.I = principalI then f z else -f z
  let branch : ℂ → ℂ := fun z ↦ if z = 0 then 1 else signedBranch z
  have hprincipalI_sq : principalI ^ (2 : ℕ) = exercise8_radicand k Complex.I := by
    have hradI_eq :
        exercise8_radicand k Complex.I =
          ((((2 : ℝ) * (1 + (k : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) := by
      calc
        exercise8_radicand k Complex.I =
            (((1 : ℂ) - Complex.I ^ (2 : ℕ)) *
              ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * Complex.I ^ (2 : ℕ))) := by
                simp [exercise8_radicand]
        _ = (((1 : ℂ) - (-1)) * ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (-1))) := by
              simp
        _ = ((((2 : ℝ) * (1 + (k : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) := by
              norm_num
    have hI_nonneg : 0 ≤ (2 : ℝ) * (1 + (k : ℝ) ^ (2 : ℕ)) := by
      positivity
    dsimp [principalI]
    rw [hradI_eq, Complex.sqrt_of_nonneg]
    · exact_mod_cast (Real.sq_sqrt hI_nonneg)
    · exact_mod_cast hI_nonneg
  have hI_sq : f Complex.I ^ (2 : ℕ) = principalI ^ (2 : ℕ) := by
    calc
      f Complex.I ^ (2 : ℕ) = exercise8_radicand k Complex.I := by
        simpa using hpow Complex.I
      _ = principalI ^ (2 : ℕ) := hprincipalI_sq.symm
  have hI_sign : f Complex.I = principalI ∨ f Complex.I = -principalI := by
    exact eq_or_eq_neg_of_sq_eq_sq _ _ (by simpa [pow_two] using hI_sq)
  have hfdiff : DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    let hzdiff : DifferentiableAt ℂ (exercise8_radicand k) z := by
      fun_prop [exercise8_radicand]
    let hz' : HasDerivAt (exercise8_radicand k) (deriv (exercise8_radicand k) z) z :=
      hzdiff.hasDerivAt
    let hsq :
        HasDerivAt (fun w : ℂ ↦ w ^ (2 : ℕ)) (2 * f z) (f z) := by
          simpa using hasDerivAt_pow 2 (f z)
    let hfnz : f z ≠ 0 := by
      intro hfz
      exact hrad_ne_zero_upper hz <| by
        simpa [hfz] using (hpow z).symm
    let hcomp :
        (fun w : ℂ ↦ w ^ (2 : ℕ)) ∘ f =ᶠ[nhds z] exercise8_radicand k :=
      Filter.Eventually.of_forall hpow
    have hderivf :
        HasDerivAt f (deriv (exercise8_radicand k) z / (2 * f z)) z :=
      hsq.of_comp_left (hfc.continuousAt <| hopen.mem_nhds hz) hz' (by
        simpa [two_mul] using mul_ne_zero two_ne_zero hfnz) hcomp
    exact hderivf.differentiableAt.differentiableWithinAt
  have hsigned_diff : DifferentiableOn ℂ signedBranch UpperHalfPlane.upperHalfPlaneSet := by
    by_cases hsign : f Complex.I = principalI
    · simpa [signedBranch, hsign] using hfdiff
    · simpa [signedBranch, hsign] using hfdiff.neg
  have hsigned_cont : ContinuousOn signedBranch UpperHalfPlane.upperHalfPlaneSet := by
    by_cases hsign : f Complex.I = principalI
    · simpa [signedBranch, hsign] using hfc
    · simpa [signedBranch, hsign] using hfc.neg
  have hbranch_diff : DifferentiableOn ℂ branch UpperHalfPlane.upperHalfPlaneSet := by
    refine hsigned_diff.congr ?_
    intro z hz
    have hz_im : 0 < z.im := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      exact hz_im.ne' (by simpa [hz0] using hz_im)
    simp [branch, hz_ne, signedBranch]
  have hbranch_cont : ContinuousOn branch UpperHalfPlane.upperHalfPlaneSet := by
    refine hsigned_cont.congr ?_
    intro z hz
    have hz_im : 0 < z.im := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      exact hz_im.ne' (by simpa [hz0] using hz_im)
    simp [branch, hz_ne, signedBranch]
  have hbranch_I : branch Complex.I = principalI := by
    have hI_ne : (Complex.I : ℂ) ≠ 0 := by simp
    by_cases hsign : f Complex.I = principalI
    · simp [branch, hI_ne, signedBranch, hsign, principalI]
    · rcases hI_sign with hEq | hEq
      · exact False.elim (hsign hEq)
      · simp [branch, hI_ne, signedBranch, hsign, principalI, hEq]
  refine ⟨{
    branch := branch
    branch_sq_eq_on_upper := ?_
    branch_ne_zero_on_upper := ?_
    continuousOn_upper := by simpa [UpperHalfPlane.upperHalfPlaneSet] using hbranch_cont
    differentiableOn_upper := by simpa [UpperHalfPlane.upperHalfPlaneSet] using hbranch_diff
    branch_eq_principal_at_I := by simpa [principalI] using hbranch_I
    branch_zero := ?_ }⟩
  · intro z hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      exact hz.ne' (by simpa [hz0] using hz)
    by_cases hsign : f Complex.I = principalI
    · simpa [branch, hz_ne, signedBranch, hsign] using hpow z
    · simpa [branch, hz_ne, signedBranch, hsign] using hpow z
  · intro z hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      exact hz.ne' (by simpa [hz0] using hz)
    by_cases hsign : f Complex.I = principalI
    · intro hbranch_zero
      have hfz : f z = 0 := by
        simpa [branch, hz_ne, signedBranch, hsign] using hbranch_zero
      exact hrad_ne_zero_upper hz <| by
        simpa [hfz] using (hpow z).symm
    · intro hbranch_zero
      have hfz : f z = 0 := by
        simpa [branch, hz_ne, signedBranch, hsign] using hbranch_zero
      exact hrad_ne_zero_upper hz <| by
        simpa [hfz] using (hpow z).symm
  · simp [branch]

/-- The normalized simple square-root branch from Cartan Exercise 8. -/
def exercise8_simple_sqrt_branch (k : Exercise8Modulus) : ℂ → ℂ :=
  (Classical.choice (exercise8_simple_sqrt_branch_exists k)).branch

/-- The normalized branch squares to the Exercise 8 radicand on the upper half-plane. -/
theorem exercise8_simple_sqrt_branch_sq_eq_on_upper {k : Exercise8Modulus} {z : ℂ}
    (hz : 0 < z.im) :
    exercise8_simple_sqrt_branch k z ^ (2 : ℕ) = exercise8_radicand k z :=
  (Classical.choice (exercise8_simple_sqrt_branch_exists k)).branch_sq_eq_on_upper hz

/-- The normalized branch is nonzero on the upper half-plane. -/
theorem exercise8_simple_sqrt_branch_ne_zero_on_upper {k : Exercise8Modulus} {z : ℂ}
    (hz : 0 < z.im) :
    exercise8_simple_sqrt_branch k z ≠ 0 :=
  (Classical.choice (exercise8_simple_sqrt_branch_exists k)).branch_ne_zero_on_upper hz

/-- The normalized branch is continuous on the upper half-plane. -/
theorem exercise8_simple_sqrt_branch_continuousOn_upper (k : Exercise8Modulus) :
    ContinuousOn (exercise8_simple_sqrt_branch k) {z : ℂ | 0 < z.im} :=
  (Classical.choice (exercise8_simple_sqrt_branch_exists k)).continuousOn_upper

/-- The normalized branch is holomorphic on the upper half-plane. -/
theorem exercise8_simple_sqrt_branch_differentiableOn_upper (k : Exercise8Modulus) :
    DifferentiableOn ℂ (exercise8_simple_sqrt_branch k) {z : ℂ | 0 < z.im} :=
  (Classical.choice (exercise8_simple_sqrt_branch_exists k)).differentiableOn_upper

/-- The normalized branch takes the source value `1` at the base point `0`. -/
theorem exercise8_simple_sqrt_branch_zero (k : Exercise8Modulus) :
    exercise8_simple_sqrt_branch k 0 = 1 :=
  (Classical.choice (exercise8_simple_sqrt_branch_exists k)).branch_zero

/-- The normalized branch is anchored to the principal square root at the interior point `i`. -/
theorem exercise8_simple_sqrt_branch_eq_principalSqrt_at_I (k : Exercise8Modulus) :
    exercise8_simple_sqrt_branch k Complex.I = Complex.sqrt (exercise8_radicand k Complex.I) :=
  (Classical.choice (exercise8_simple_sqrt_branch_exists k)).branch_eq_principal_at_I

/-- The elliptic integrand from Exercise 8, using Cartan's simple branch rather than the global
principal square root. -/
def exercise8_integrand (k : Exercise8Modulus) (z : ℂ) : ℂ :=
  (exercise8_simple_sqrt_branch k z)⁻¹

/-- The Abelian integral from Exercise 8, computed along the straight segment from `0` to `z`. -/
def exercise8_abel_integral (k : Exercise8Modulus) (z : UpperHalfPlane) : ℂ :=
  ∫ᶜ w in Path.segment (0 : ℂ) (z : ℂ), (exercise8_integrand k dz) w

/-- Normal form for the Exercise 8 Abelian integral. -/
theorem exercise8_abel_integral_def (k : Exercise8Modulus) (z : UpperHalfPlane) :
    exercise8_abel_integral k z =
      ∫ᶜ w in Path.segment (0 : ℂ) (z : ℂ), (exercise8_integrand k dz) w := rfl

/-- Helper for Exercise 8: the elliptic radicand has no zeros in the strict upper half-plane. -/
lemma exercise8_integrand_radicand_ne_zero_of_im_pos {k : Exercise8Modulus} {z : ℂ}
    (hz : 0 < z.im) :
    exercise8_radicand k z ≠ 0 := by
  -- Each factor would force `z` to be one of the four real branch points, impossible for
  -- a strict upper-half-plane point.
  refine mul_ne_zero ?_ ?_
  · intro hfactor
    have hz_sq : z ^ (2 : ℕ) = ((1 : ℂ) ^ (2 : ℕ)) := by
      have : (1 : ℂ) = z ^ (2 : ℕ) := sub_eq_zero.mp hfactor
      simpa using this.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz_sq with hreal | hreal
    · have : z.im = 0 := by simpa [hreal]
      exact hz.ne' this
    · have : z.im = 0 := by simpa [hreal]
      exact hz.ne' this
  · intro hfactor
    have hk_ne : (k : ℂ) ≠ 0 := by
      exact_mod_cast (Exercise8Modulus.pos k).ne'
    have hk_sq_ne : ((k : ℂ) ^ (2 : ℕ)) ≠ 0 := pow_ne_zero _ hk_ne
    have hz_sq : z ^ (2 : ℕ) = (1 / (k : ℂ)) ^ (2 : ℕ) := by
      apply (mul_left_cancel₀ hk_sq_ne)
      calc
        ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) = 1 := by
          exact (sub_eq_zero.mp hfactor).symm
        _ = ((k : ℂ) ^ (2 : ℕ)) * (1 / (k : ℂ)) ^ (2 : ℕ) := by
          field_simp [hk_ne]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz_sq with hreal | hreal
    · have : z.im = 0 := by simpa [hreal]
      exact hz.ne' this
    · have : z.im = 0 := by simpa [hreal]
      exact hz.ne' this

/-- Helper for Exercise 8: the radicand is even in the variable `z`.

The corresponding integrand is not defined with the global principal square root; its branch is the
source-normalized simple branch on the upper half-plane. -/
lemma exercise8_radicand_neg (k : Exercise8Modulus) (z : ℂ) :
    exercise8_radicand k (-z) = exercise8_radicand k z := by
  simp [exercise8_radicand]

/-- The complete real period `K` from Exercise 8. -/
def exercise8_complete_real_period (k : Exercise8Modulus) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)))

/-- Normal form for the complete real period from Exercise 8. -/
theorem exercise8_complete_real_period_def (k : Exercise8Modulus) :
    exercise8_complete_real_period k =
      ∫ t in (0 : ℝ)..1,
        1 / Real.sqrt ((1 - t ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) := rfl

/-- The complete imaginary period `K'` from Exercise 8. -/
def exercise8_complete_imaginary_period (k : Exercise8Modulus) : ℝ :=
  ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
    1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)))

/-- Normal form for the complete imaginary period from Exercise 8. -/
theorem exercise8_complete_imaginary_period_def (k : Exercise8Modulus) :
    exercise8_complete_imaginary_period k =
      ∫ t in (1 : ℝ)..(1 / (k : ℝ)),
        1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) := rfl

/-- Helper for Exercise 8: on `[0, 1]`, the radicand `1 - k^2 x^2` stays strictly positive. -/
lemma exercise8_real_factor_radicand_pos {k : Exercise8Modulus} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < 1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) := by
  -- The source proof first isolates the continuous multiplier `1 / √(1 - k² x²)` on `[0, 1]`.
  have hk2 : (k : ℝ) ^ (2 : ℕ) < 1 := by
    nlinarith [Exercise8Modulus.pos k, Exercise8Modulus.lt_one k]
  have hx2le : x ^ (2 : ℕ) ≤ 1 := by
    nlinarith [hx.1, hx.2]
  have hmulle : (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ) ≤ (k : ℝ) ^ (2 : ℕ) := by
    exact mul_le_of_le_one_right (by positivity) hx2le
  exact sub_pos.mpr (lt_of_le_of_lt hmulle hk2)

/-- Helper for Exercise 8: the factor `1 / √(1 - k^2 x^2)` is positive on `(0, 1)`. -/
lemma exercise8_real_factor_pos {k : Exercise8Modulus} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < 1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)) := by
  -- Once the radicand is positive, the factor is a positive reciprocal square root.
  exact one_div_pos.mpr <|
    Real.sqrt_pos.2 <|
      exercise8_real_factor_radicand_pos (k := k) ⟨le_of_lt hx.1, hx.2.le⟩

/-- Helper for Exercise 8: the continuous multiplier `1 / √(1 - k^2 x^2)` is well-defined on
`[0, 1]`. -/
lemma exercise8_real_factor_continuousOn (k : Exercise8Modulus) :
    ContinuousOn
      (fun x : ℝ => 1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)))
      (Icc (0 : ℝ) 1) := by
  -- The multiplier is the inverse of a square root whose radicand stays positive on the interval.
  -- We prove continuity for the inverse form and then rewrite `1 / a` as `a⁻¹`.
  simpa [one_div] using
    (ContinuousOn.inv₀
      (Real.continuous_sqrt.continuousOn.comp
        (by
          simpa using
            (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow (2 : ℕ)))))
        (by
          intro x hx
          exact (exercise8_real_factor_radicand_pos (k := k) hx).le))
      (by
        intro x hx
        exact Real.sqrt_ne_zero'.2 (exercise8_real_factor_radicand_pos (k := k) hx)) :
      ContinuousOn
        (fun x : ℝ => (Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)))⁻¹)
        (Icc (0 : ℝ) 1))

/-- Helper for Exercise 8: on `[0, 1]`, the real-period kernel factors through the Chebyshev
model kernel `1 / √(1 - x^2)`. -/
lemma exercise8_real_kernel_eq_factored {k : Exercise8Modulus} {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    1 / Real.sqrt ((1 - x ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))) =
      (1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))) *
        (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by
  -- This puts the Exercise 8 kernel into the exact shape needed for mathlib's model integral.
  have hx_nonneg : 0 ≤ 1 - x ^ (2 : ℕ) := by
    nlinarith [hx.1, hx.2]
  rw [Real.sqrt_mul hx_nonneg (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ)), one_div, mul_inv_rev]
  rw [one_div]

/-- The complete real period `K` from Exercise 8 is positive. -/
theorem exercise8_complete_real_period_pos (k : Exercise8Modulus) :
    0 < exercise8_complete_real_period k := by
  -- Route correction: we follow the source route by factoring the kernel into a continuous
  -- positive multiplier times the standard Chebyshev kernel `1 / √(1 - x^2)`.
  rw [exercise8_complete_real_period_def]
  have hbase :
      IntervalIntegrable
        (fun x : ℝ => (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcheb01 :
        IntervalIntegrable
          (fun x : ℝ => Real.sqrt (1 - x ^ (2 : ℕ))⁻¹)
          MeasureTheory.volume (0 : ℝ) 1 := by
      let hcheb := Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
      refine hcheb.mono_set' (c := (0 : ℝ)) (d := (1 : ℝ)) ?_
      intro x hx
      have hx' : x ∈ Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hx
      have hx'' : x ∈ Ioc (-1 : ℝ) 1 := by
        exact ⟨by linarith [hx'.1], hx'.2⟩
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx''
    simpa using hcheb01
  have hfactored :
      IntervalIntegrable
        (fun x : ℝ =>
          (1 / Real.sqrt (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))) *
            (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (0 : ℝ) 1 := by
    -- The extra factor is continuous on `[0, 1]`, so it preserves interval integrability.
    exact hbase.continuousOn_mul <|
      by simpa [Set.uIcc_of_le zero_le_one] using exercise8_real_factor_continuousOn k
  have hkernel :
      IntervalIntegrable
        (fun x : ℝ =>
          1 / Real.sqrt ((1 - x ^ (2 : ℕ)) * (1 - (k : ℝ) ^ (2 : ℕ) * x ^ (2 : ℕ))))
        MeasureTheory.volume (0 : ℝ) 1 := by
    refine hfactored.congr ?_
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      have hxIoc : x ∈ Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hx
      exact ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    simpa using (exercise8_real_kernel_eq_factored (k := k) hx').symm
  refine intervalIntegral.intervalIntegral_pos_of_pos_on hkernel ?_ zero_lt_one
  intro x hx
  have hx_sqrt : 0 < Real.sqrt (1 - x ^ (2 : ℕ)) := by
    have hx_rad : 0 < 1 - x ^ (2 : ℕ) := by
      nlinarith [hx.1, hx.2]
    exact Real.sqrt_pos.2 hx_rad
  -- The factored form shows the kernel is a product of two positive real factors.
  rw [exercise8_real_kernel_eq_factored (k := k) ⟨le_of_lt hx.1, hx.2.le⟩]
  exact mul_pos (exercise8_real_factor_pos (k := k) hx) (inv_pos.2 hx_sqrt)

/-- Helper for Exercise 8: the endpoint model kernel `1 / √((t - a) (b - t))` is interval
integrable on every compact interval `[a, b]` with `a < b`. -/
lemma exercise8_endpoint_sqrt_kernel_intervalIntegrable {a b : ℝ} (hab : a < b) :
    IntervalIntegrable
      (fun t : ℝ => (Real.sqrt ((t - a) * (b - t)))⁻¹)
      MeasureTheory.volume a b := by
  let c : ℝ := (b - a) / 2
  let d : ℝ := (a + b) / 2
  have hc_pos : 0 < c := by
    -- The affine transport from `[-1, 1]` to `[a, b]` uses the positive half-length `c`.
    dsimp [c]
    linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hmodel :
      IntervalIntegrable
        (fun x : ℝ => (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (-1) 1 := by
    -- This is mathlib's Chebyshev-model endpoint singularity.
    simpa using Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hscaled :
      IntervalIntegrable
        (fun x : ℝ => c⁻¹ * (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹)
        MeasureTheory.volume (-1) 1 := by
    -- Multiplying by the constant Jacobian factor preserves interval integrability.
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hmodel.const_mul c⁻¹
  have hcomp :
      IntervalIntegrable
        (fun x : ℝ =>
          (Real.sqrt (((c * x + d) - a) * (b - (c * x + d))))⁻¹)
        MeasureTheory.volume (-1) 1 := by
    -- After the affine substitution, the transported kernel is exactly the scaled Chebyshev model.
    refine hscaled.congr ?_
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := by
      have hxIoc : x ∈ Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      exact ⟨le_of_lt hxIoc.1, hxIoc.2⟩
    have hx_nonneg : 0 ≤ 1 - x ^ (2 : ℕ) := by
      nlinarith [hx'.1, hx'.2]
    have hprod :
        (((c * x + d) - a) * (b - (c * x + d))) = c ^ (2 : ℕ) * (1 - x ^ (2 : ℕ)) := by
      dsimp [c, d]
      ring
    have hsqrtc : Real.sqrt (c ^ (2 : ℕ)) = c := by
      simpa [pow_two, abs_of_nonneg hc_pos.le] using Real.sqrt_sq_eq_abs c
    change c⁻¹ * (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ =
      (Real.sqrt (((c * x + d) - a) * (b - (c * x + d))))⁻¹
    symm
    calc
      (Real.sqrt (((c * x + d) - a) * (b - (c * x + d))))⁻¹
          = (Real.sqrt (c ^ (2 : ℕ) * (1 - x ^ (2 : ℕ))))⁻¹ := by rw [hprod]
      _ = (Real.sqrt (c ^ (2 : ℕ)) * Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by
            rw [Real.sqrt_mul (pow_nonneg hc_pos.le _) (1 - x ^ (2 : ℕ))]
      _ = (c * Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by rw [hsqrtc]
      _ = (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ * c⁻¹ := by rw [mul_inv_rev]
      _ = c⁻¹ * (Real.sqrt (1 - x ^ (2 : ℕ)))⁻¹ := by ring
  have hshift :
      IntervalIntegrable
        (fun y : ℝ => (Real.sqrt ((y + d - a) * (b - (y + d))))⁻¹)
        MeasureTheory.volume (-c) c := by
    -- Undo the multiplicative part of the affine substitution.
    refine (IntervalIntegrable.comp_mul_left_iff
      (f := fun y : ℝ => (Real.sqrt ((y + d - a) * (b - (y + d))))⁻¹)
      (a := -c) (b := c) hc_ne).mp ?_
    simpa [hc_ne, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using hcomp
  -- Undo the translational part of the affine substitution.
  have htranslate :
      IntervalIntegrable
        (fun t : ℝ => (Real.sqrt ((t - a) * (b - t)))⁻¹)
        MeasureTheory.volume (-c + d) (c + d) := by
    refine (IntervalIntegrable.comp_add_right_iff
      (f := fun t : ℝ => (Real.sqrt ((t - a) * (b - t)))⁻¹)
      (a := -c) (b := c) (c := d)).mp ?_
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
  have hleft : -c + d = a := by
    dsimp [c, d]
    ring
  have hright : c + d = b := by
    dsimp [c, d]
    ring
  simpa [hleft, hright] using htranslate

/-- Helper for Exercise 8: on `[1, 1 / k]`, the auxiliary factor `(t + 1) (1 / k + t)` stays
strictly positive. -/
lemma exercise8_imaginary_factor_radicand_pos {k : Exercise8Modulus} {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    0 < (t + 1) * (1 / (k : ℝ) + t) := by
  -- The source proof isolates the harmless positive factor away from the endpoint singularities.
  have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
  have ht_add_one : 0 < t + 1 := by
    linarith [ht.1]
  have ht_add_inv : 0 < 1 / (k : ℝ) + t := by
    have hk_inv_pos : 0 < 1 / (k : ℝ) := one_div_pos.mpr hk_pos
    linarith [hk_inv_pos, ht.1]
  exact mul_pos ht_add_one ht_add_inv

/-- Helper for Exercise 8: the positive multiplier in the `[1, 1 / k]` kernel factorization is
strictly positive on the open interval. -/
lemma exercise8_imaginary_factor_pos {k : Exercise8Modulus} {t : ℝ}
    (ht : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ))) :
    0 < (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) := by
  -- Positivity follows from the positivity of `k` and the positive square-root radicand.
  exact inv_pos.2 <|
    mul_pos (Exercise8Modulus.pos k) <|
      Real.sqrt_pos.2 <|
        exercise8_imaginary_factor_radicand_pos (k := k) ⟨ht.1.le, ht.2.le⟩

/-- Helper for Exercise 8: the positive multiplier in the `[1, 1 / k]` kernel factorization is
continuous on the closed interval. -/
lemma exercise8_imaginary_factor_continuousOn (k : Exercise8Modulus) :
    ContinuousOn
      (fun t : ℝ => ((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹)
      (Icc (1 : ℝ) (1 / (k : ℝ))) := by
  -- The multiplier is the inverse of a nonvanishing continuous square-root factor.
  refine ContinuousOn.inv₀ ?_ ?_
  · exact
      (continuousOn_const.mul <|
        Real.continuous_sqrt.continuousOn.comp
          ((continuousOn_id.add continuousOn_const).mul
            (continuousOn_const.add continuousOn_id))
          (by
            intro t ht
            exact (exercise8_imaginary_factor_radicand_pos (k := k) ht).le))
  · intro t ht
    exact mul_ne_zero (Exercise8Modulus.pos k).ne'
      (Real.sqrt_ne_zero'.2 <| exercise8_imaginary_factor_radicand_pos (k := k) ht)

/-- Helper for Exercise 8: on `[1, 1 / k]`, the imaginary-period kernel factors into a positive
continuous multiplier times the endpoint model kernel. -/
lemma exercise8_imaginary_kernel_eq_factored {k : Exercise8Modulus} {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) (1 / (k : ℝ))) :
    1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) =
      (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) *
        (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹ := by
  -- The source normalization separates the endpoint singularities from the positive multiplier.
  have hk_ne : (k : ℝ) ≠ 0 := (Exercise8Modulus.pos k).ne'
  have hA_nonneg : 0 ≤ (t - 1) * (1 / (k : ℝ) - t) := by
    nlinarith [ht.1, ht.2]
  have hB_nonneg :
      0 ≤ (k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t)) := by
    exact mul_nonneg (pow_nonneg (Exercise8Modulus.pos k).le _) <|
      (exercise8_imaginary_factor_radicand_pos (k := k) ht).le
  have hprod :
      (t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) =
        ((t - 1) * (1 / (k : ℝ) - t)) *
          ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))) := by
    field_simp [pow_two, hk_ne]
    ring
  have hsqrtB :
      Real.sqrt ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))) =
        (k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)) := by
    calc
      Real.sqrt ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))) =
          Real.sqrt ((k : ℝ) ^ (2 : ℕ)) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)) := by
            rw [Real.sqrt_mul (pow_nonneg (Exercise8Modulus.pos k).le _)
              ((t + 1) * (1 / (k : ℝ) + t))]
      _ = (k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)) := by
            rw [show Real.sqrt ((k : ℝ) ^ (2 : ℕ)) = (k : ℝ) by
              simpa [pow_two, abs_of_nonneg (Exercise8Modulus.pos k).le] using
                Real.sqrt_sq_eq_abs (k : ℝ)]
  calc
    1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) =
        (Real.sqrt
          (((t - 1) * (1 / (k : ℝ) - t)) *
            ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t)))))⁻¹ := by
          rw [hprod, one_div]
    _ =
        (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)) *
          Real.sqrt ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t))))⁻¹ := by
          rw [Real.sqrt_mul hA_nonneg
            ((k : ℝ) ^ (2 : ℕ) * ((t + 1) * (1 / (k : ℝ) + t)))]
    _ =
        (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)) *
          ((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t))))⁻¹ := by
          rw [hsqrtB]
    _ =
        (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) *
          (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹ := by
          rw [mul_inv_rev]

/-- The complete imaginary period `K'` from Exercise 8 is positive. -/
theorem exercise8_complete_imaginary_period_pos (k : Exercise8Modulus) :
    0 < exercise8_complete_imaginary_period k := by
  -- Route correction: we now mirror the `K > 0` proof after factoring the kernel into a positive
  -- continuous multiplier times the transported endpoint model on `[1, 1 / k]`.
  rw [exercise8_complete_imaginary_period_def]
  have hk_inv_gt_one : 1 < 1 / (k : ℝ) := by
    simpa [one_div] using (one_lt_inv₀ (Exercise8Modulus.pos k)).2 (Exercise8Modulus.lt_one k)
  have hendpoint :
      IntervalIntegrable
        (fun t : ℝ => (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹)
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) :=
    exercise8_endpoint_sqrt_kernel_intervalIntegrable hk_inv_gt_one
  have hfactored :
      IntervalIntegrable
        (fun t : ℝ =>
          (((k : ℝ) * Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹) *
            (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹)
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) := by
    -- The isolated multiplier is continuous on the whole interval, so it preserves integrability.
    have hcont :
        ContinuousOn
          (fun t : ℝ =>
            (Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹ * (k : ℝ)⁻¹)
          (Set.uIcc (1 : ℝ) (1 / (k : ℝ))) := by
      have hcontIcc :
          ContinuousOn
            (fun t : ℝ =>
              (Real.sqrt ((t + 1) * (1 / (k : ℝ) + t)))⁻¹ * (k : ℝ)⁻¹)
            (Icc (1 : ℝ) (1 / (k : ℝ))) := by
        simpa [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
          exercise8_imaginary_factor_continuousOn k
      rw [Set.uIcc_of_le hk_inv_gt_one.le]
      exact hcontIcc
    simpa [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      hendpoint.continuousOn_mul hcont
  have hkernel :
      IntervalIntegrable
        (fun t : ℝ =>
          1 / Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))))
        MeasureTheory.volume (1 : ℝ) (1 / (k : ℝ)) := by
    refine hfactored.congr ?_
    intro t ht
    have ht' : t ∈ Icc (1 : ℝ) (1 / (k : ℝ)) := by
      have htIoc : t ∈ Ioc (1 : ℝ) (1 / (k : ℝ)) := by
        rw [Set.uIoc_of_le hk_inv_gt_one.le] at ht
        exact ht
      exact ⟨le_of_lt htIoc.1, htIoc.2⟩
    simpa using (exercise8_imaginary_kernel_eq_factored (k := k) ht').symm
  refine intervalIntegral.intervalIntegral_pos_of_pos_on hkernel ?_ hk_inv_gt_one
  intro t ht
  -- The factored form reduces strict positivity to the positivity of its two real factors.
  have htIoo : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ)) := by
    simpa [one_div, Set.uIoo_of_lt hk_inv_gt_one] using ht
  rw [exercise8_imaginary_kernel_eq_factored (k := k) ⟨le_of_lt htIoo.1, htIoo.2.le⟩]
  have hendpoint_pos : 0 < (Real.sqrt ((t - 1) * (1 / (k : ℝ) - t)))⁻¹ := by
    have hrad : 0 < (t - 1) * (1 / (k : ℝ) - t) := by
      nlinarith [htIoo.1, htIoo.2]
    exact inv_pos.2 (Real.sqrt_pos.2 hrad)
  exact mul_pos (exercise8_imaginary_factor_pos (k := k) htIoo) hendpoint_pos

/-- The complex number `i K' / K` lies in the upper half-plane. -/
theorem exercise8_tau_im_pos (k : Exercise8Modulus) :
    0 <
      (Complex.I *
        (exercise8_complete_imaginary_period k / exercise8_complete_real_period k)).im := by
  -- The imaginary part of `i * (K' / K)` is exactly the positive ratio `K' / K`.
  have hquot :
      0 <
        exercise8_complete_imaginary_period k / exercise8_complete_real_period k := by
    exact div_pos (exercise8_complete_imaginary_period_pos k) (exercise8_complete_real_period_pos k)
  simpa using hquot

/-- The Jacobi parameter `τ = i K' / K` attached to Exercise 8, viewed in the upper half-plane. -/
def exercise8_tau (k : Exercise8Modulus) : ℍ :=
  ⟨Complex.I * (exercise8_complete_imaginary_period k / exercise8_complete_real_period k),
    exercise8_tau_im_pos k⟩

/-- Normal form for the Exercise 8 parameter `τ`. -/
theorem exercise8_tau_def (k : Exercise8Modulus) :
    (exercise8_tau k : ℂ) =
      Complex.I * (exercise8_complete_imaginary_period k / exercise8_complete_real_period k) := rfl

/-- The open rectangle with vertices `-K`, `K`, `K + i K'`, and `-K + i K'`. -/
def exercise8_open_rectangle (k : Exercise8Modulus) : Set ℂ :=
  Set.Ioo (-exercise8_complete_real_period k) (exercise8_complete_real_period k) ×ℂ
    Set.Ioo (0 : ℝ) (exercise8_complete_imaginary_period k)

/-- Membership in the Exercise 8 rectangle is given by the expected inequalities on real and
imaginary parts. -/
theorem mem_exercise8_open_rectangle_iff {k : Exercise8Modulus} {u : ℂ} :
    u ∈ exercise8_open_rectangle k ↔
      u.re ∈ Ioo (-exercise8_complete_real_period k) (exercise8_complete_real_period k) ∧
        u.im ∈ Ioo (0 : ℝ) (exercise8_complete_imaginary_period k) :=
  Complex.mem_reProdIm

/-- The full period pair `4 K`, `2 i K'` for the meromorphic inverse in Exercise 8. -/
theorem exercise8_period_pair_indep (k : Exercise8Modulus) :
    LinearIndependent ℝ
      ![(((4 * exercise8_complete_real_period k : ℝ) : ℂ)),
        (((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)] := by
  -- The imaginary part forces the coefficient of the purely imaginary generator to vanish.
  refine LinearIndependent.pair_iff.2 ?_
  intro a b hab
  have himag : b * (2 * exercise8_complete_imaginary_period k) = 0 := by
    have hab_im := congrArg Complex.im hab
    simpa [Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using hab_im
  have hb : b = 0 := by
    nlinarith [exercise8_complete_imaginary_period_pos k, himag]
  -- With the imaginary coefficient gone, the real part forces the remaining coefficient to vanish.
  have hreal : a * (4 * exercise8_complete_real_period k) = 0 := by
    have hab_re := congrArg Complex.re hab
    simpa [hb, Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using
      hab_re
  have ha : a = 0 := by
    nlinarith [exercise8_complete_real_period_pos k, hreal]
  exact ⟨ha, hb⟩

/-- The canonical period-data owner for the doubly-periodic inverse from Exercise 8. -/
def exercise8_period_pair (k : Exercise8Modulus) : PeriodPair :=
  { ω₁ := ((4 * exercise8_complete_real_period k : ℝ) : ℂ)
    ω₂ := ((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I
    indep := exercise8_period_pair_indep k }

/-- The half-real-period pair whose lattice is the zero locus of the Exercise 8 inverse. -/
theorem exercise8_half_period_pair_indep (k : Exercise8Modulus) :
    LinearIndependent ℝ
      ![(((2 * exercise8_complete_real_period k : ℝ) : ℂ)),
        (((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)] := by
  -- The same real-versus-purely-imaginary decomposition works for the half-period pair.
  refine LinearIndependent.pair_iff.2 ?_
  intro a b hab
  have himag : b * (2 * exercise8_complete_imaginary_period k) = 0 := by
    have hab_im := congrArg Complex.im hab
    simpa [Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using hab_im
  have hb : b = 0 := by
    nlinarith [exercise8_complete_imaginary_period_pos k, himag]
  -- The first generator is a positive real number, so the real part kills its coefficient.
  have hreal : a * (2 * exercise8_complete_real_period k) = 0 := by
    have hab_re := congrArg Complex.re hab
    simpa [hb, Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using
      hab_re
  have ha : a = 0 := by
    nlinarith [exercise8_complete_real_period_pos k, hreal]
  exact ⟨ha, hb⟩

/-- The source-facing zero-lattice owner for Exercise 8, obtained by halving the real period. -/
def exercise8_half_period_pair (k : Exercise8Modulus) : PeriodPair :=
  { ω₁ := ((2 * exercise8_complete_real_period k : ℝ) : ℂ)
    ω₂ := ((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I
    indep := exercise8_half_period_pair_indep k }

/-- The pole lattice is the translate of the zero lattice by the half imaginary period `i K'`. -/
def exercise8_pole_shift (k : Exercise8Modulus) : ℂ :=
  (exercise8_half_period_pair k).ω₂ / 2

/-- Membership in the zero lattice is the expected even-period coordinate condition. -/
theorem mem_exercise8_half_period_pair_lattice_iff {k : Exercise8Modulus} {u : ℂ} :
    u ∈ (exercise8_half_period_pair k).lattice ↔
      ∃ m n : ℤ,
        u =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
  -- Unfold the lattice description to identify the integer coordinates in the chosen basis.
  rw [exercise8_half_period_pair, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    -- Rewrite the basis combination into the source-facing even-period formula.
    calc
      u = m * (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) +
            n * ((((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)) := hmn.symm
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
          norm_num [mul_assoc, mul_left_comm, mul_comm]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    -- The source-facing even-period coordinates are exactly the lattice coordinates for `ω₁, ω₂`.
    calc
      m * (((2 * exercise8_complete_real_period k : ℝ) : ℂ)) +
          n * ((((2 * exercise8_complete_imaginary_period k : ℝ) : ℂ) * Complex.I)) =
            ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
            norm_num [mul_assoc, mul_left_comm, mul_comm]
      _ = u := hmn.symm

/-- Membership in the translated pole lattice is the expected odd-half-period condition. -/
theorem mem_exercise8_pole_shift_sub_lattice_iff {k : Exercise8Modulus} {u : ℂ} :
    u - exercise8_pole_shift k ∈ (exercise8_half_period_pair k).lattice ↔
      ∃ m n : ℤ,
        u =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
  have hpole :
      exercise8_pole_shift k = exercise8_complete_imaginary_period k * Complex.I := by
    -- The pole shift is the half imaginary period `ω₂ / 2 = i K'`.
    simp [exercise8_pole_shift, exercise8_half_period_pair]
    ring
  constructor
  · intro hu
    rcases (mem_exercise8_half_period_pair_lattice_iff).1 hu with ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    -- Add back the half imaginary period to move from the even lattice to the pole translate.
    calc
      u = (u - exercise8_pole_shift k) + exercise8_pole_shift k := by ring
      _ =
          (((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I) +
            exercise8_complete_imaginary_period k * Complex.I := by rw [hmn, hpole]
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
          norm_num [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm]
  · rintro ⟨m, n, hu⟩
    -- Subtracting the half imaginary period recovers the even lattice coordinates.
    apply (mem_exercise8_half_period_pair_lattice_iff).2
    refine ⟨m, n, ?_⟩
    calc
      u - exercise8_pole_shift k =
          (((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
              (((2 * n + 1 : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I) -
            exercise8_complete_imaginary_period k * Complex.I := by rw [hu, hpole]
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            ((((2 * n + 1 : ℤ) : ℂ) - 1) * exercise8_complete_imaginary_period k) * Complex.I := by
          ring
      _ =
          ((2 * m : ℤ) : ℂ) * exercise8_complete_real_period k +
            (((2 * n : ℤ) : ℂ) * exercise8_complete_imaginary_period k) * Complex.I := by
          norm_num

/-- The theta quotient appearing in the Exercise 8 representation formula. -/
def exercise8_theta_quotient (k : Exercise8Modulus) (u : ℂ) : ℂ :=
  let τ : ℂ := exercise8_tau k
  let v := u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ)
  (-Complex.I) * Complex.exp (Real.pi * Complex.I * (v + τ / 4)) *
      jacobiTheta₂ (v + (1 + τ) / 2) τ / jacobiTheta₂ (v + 1 / 2) τ

/-- Normal form for the Exercise 8 theta quotient. -/
theorem exercise8_theta_quotient_def (k : Exercise8Modulus) (u : ℂ) :
    exercise8_theta_quotient k u =
      (-Complex.I) *
          Complex.exp
            (Real.pi * Complex.I *
              (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ) + exercise8_tau k / 4)) *
          jacobiTheta₂
            (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ) + (1 + exercise8_tau k) / 2)
            (exercise8_tau k) /
        jacobiTheta₂
          (u / ((2 * exercise8_complete_real_period k : ℝ) : ℂ) + 1 / 2) (exercise8_tau k) := by
  rfl
