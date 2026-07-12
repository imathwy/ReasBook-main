import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».AbelIntegralCore

open Set
open scoped UpperHalfPlane

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: pointwise Schwarz reflection for the source
integrand on the strict upper half-plane. -/
lemma exercise8_integrand_reflection_upper
    (k : Exercise8Modulus) {z : ℂ} (hz : 0 < z.im) :
    exercise8_integrand k (-star z) = star (exercise8_integrand k z) := by
  -- Route correction: instead of asking for a new ambient reflection axiom, compare the reflected
  -- branch with the original branch on `UpperHalfPlane` and use connectedness to rule out the
  -- global sign change.
  let reflectedBranch : UpperHalfPlane → ℂ :=
    fun w ↦ star (exercise8_simple_sqrt_branch k (-star (w : ℂ)))
  let originalBranch : UpperHalfPlane → ℂ :=
    fun w ↦ exercise8_simple_sqrt_branch k (w : ℂ)
  have hnegStar_cont : Continuous fun w : UpperHalfPlane ↦ -star (w : ℂ) := by
    simpa using (continuous_star.comp UpperHalfPlane.continuous_coe).neg
  have hnegStar_mem : ∀ w : UpperHalfPlane, -star (w : ℂ) ∈ {u : ℂ | 0 < u.im} := by
    intro w
    simpa using w.im_pos
  have hreflected_cont : Continuous reflectedBranch := by
    -- The reflected branch is continuous because `z ↦ -conj z` preserves the strict upper
    -- half-plane, and complex conjugation is continuous.
    have hbase :
        Continuous fun w : UpperHalfPlane ↦ exercise8_simple_sqrt_branch k (-star (w : ℂ)) :=
      (exercise8_simple_sqrt_branch_continuousOn_upper k).comp_continuous
        hnegStar_cont hnegStar_mem
    simpa [reflectedBranch] using continuous_star.comp hbase
  have horiginal_cont : Continuous originalBranch := by
    -- The original source branch is continuous on the whole upper-half-plane subtype.
    exact (exercise8_simple_sqrt_branch_continuousOn_upper k).comp_continuous
      UpperHalfPlane.continuous_coe fun w ↦ w.2
  have hsquare :
      ∀ w : UpperHalfPlane, reflectedBranch w ^ (2 : ℕ) = originalBranch w ^ (2 : ℕ) := by
    intro w
    have hneg_im : 0 < (-star (w : ℂ)).im := by
      simpa using w.im_pos
    -- Both branches square to the same radicand because the radicand has real coefficients and is
    -- even in `z`.
    calc
      reflectedBranch w ^ (2 : ℕ) =
          star ((exercise8_simple_sqrt_branch k (-star (w : ℂ))) ^ (2 : ℕ)) := by
            simp [reflectedBranch]
      _ = star (exercise8_radicand k (-star (w : ℂ))) := by
            rw [exercise8_simple_sqrt_branch_sq_eq_on_upper hneg_im]
      _ = exercise8_radicand k (w : ℂ) := by
            simp [exercise8_radicand]
      _ = originalBranch w ^ (2 : ℕ) := by
            symm
            exact exercise8_simple_sqrt_branch_sq_eq_on_upper w.im_pos
  let agreeSet : Set UpperHalfPlane := {w | reflectedBranch w = originalBranch w}
  let flipSet : Set UpperHalfPlane := {w | reflectedBranch w = -originalBranch w}
  have hagree_closed : IsClosed agreeSet := by
    exact isClosed_eq hreflected_cont horiginal_cont
  have hflip_closed : IsClosed flipSet := by
    exact isClosed_eq hreflected_cont horiginal_cont.neg
  have hcover :
      agreeSet ∪ flipSet = Set.univ := by
    ext w
    constructor
    · intro _
      simp
    · intro _
      have hsq : reflectedBranch w ^ (2 : ℕ) = originalBranch w ^ (2 : ℕ) := hsquare w
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa [pow_two] using hsq) with hEq | hEq
      · exact Or.inl hEq
      · exact Or.inr hEq
  have hdisjoint :
      agreeSet ∩ flipSet = (∅ : Set UpperHalfPlane) := by
    ext w
    constructor
    · rintro ⟨hwAgree, hwFlip⟩
      have hzero_branch : exercise8_simple_sqrt_branch k (w : ℂ) = 0 := by
        have hEq :
            exercise8_simple_sqrt_branch k (w : ℂ) =
              -exercise8_simple_sqrt_branch k (w : ℂ) := hwAgree.symm.trans hwFlip
        have htwo :
            (2 : ℂ) * exercise8_simple_sqrt_branch k (w : ℂ) = 0 := by
          have hsum :=
            congrArg
              (fun u : ℂ ↦ u + exercise8_simple_sqrt_branch k (w : ℂ))
              hEq
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using hsum
        exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      exact False.elim (exercise8_simple_sqrt_branch_ne_zero_on_upper w.im_pos hzero_branch)
    · intro hw
      simpa using hw
  have hagree_clopen : IsClopen agreeSet := by
    refine ⟨hagree_closed, ?_⟩
    rw [← isClosed_compl_iff]
    have hcompl : agreeSetᶜ = flipSet := by
      ext w
      constructor
      · intro hw
        rcases show w ∈ agreeSet ∪ flipSet by simpa [hcover] with hwAgree | hwFlip
        · exact False.elim (hw hwAgree)
        · exact hwFlip
      · intro hwFlip hwAgree
        have : w ∈ agreeSet ∩ flipSet := ⟨hwAgree, hwFlip⟩
        simpa [hdisjoint] using this
    simpa [hcompl] using hflip_closed
  have hagree_nonempty : agreeSet.Nonempty := by
    -- The sign cannot flip globally, because at `i` that would force a nonzero square root of a
    -- positive real number to be purely imaginary.
    let branchI : ℂ := exercise8_simple_sqrt_branch k Complex.I
    have hI_cover : (UpperHalfPlane.I : UpperHalfPlane) ∈ agreeSet ∪ flipSet := by
      simpa [hcover]
    have hI_not_flip : (UpperHalfPlane.I : UpperHalfPlane) ∉ flipSet := by
      intro hflip
      have hre_zero : branchI.re = 0 := by
        have hEq : star branchI = -branchI := by
          simpa [flipSet, reflectedBranch, originalBranch, branchI] using hflip
        have hre' : branchI.re = -branchI.re := by
          simpa using congrArg Complex.re hEq
        nlinarith
      have hsq_nonpos : (branchI ^ (2 : ℕ)).re ≤ 0 := by
        have hsq_re : (branchI ^ (2 : ℕ)).re = -(branchI.im ^ (2 : ℕ)) := by
          simp [branchI, pow_two, Complex.mul_re, hre_zero]
        rw [hsq_re]
        nlinarith
      have hrad_pos : 0 < (exercise8_radicand k Complex.I).re := by
        have hk_sq_re : (((k : ℂ) ^ (2 : ℕ)).re) = (k : ℝ) ^ (2 : ℕ) := by
          simpa using (Complex.ofReal_re ((k : ℝ) ^ (2 : ℕ)))
        have hpos : 0 < 1 + (((k : ℂ) ^ (2 : ℕ)).re) := by
          rw [hk_sq_re]
          positivity
        simpa [exercise8_radicand] using hpos
      have hsq_eq : branchI ^ (2 : ℕ) = exercise8_radicand k Complex.I := by
        simpa [branchI] using
          exercise8_simple_sqrt_branch_sq_eq_on_upper (k := k) (z := Complex.I) (by simp)
      have : (exercise8_radicand k Complex.I).re ≤ 0 := by
        simpa [hsq_eq] using hsq_nonpos
      linarith
    rcases hI_cover with hI_agree | hI_flip
    · exact ⟨UpperHalfPlane.I, hI_agree⟩
    · exact False.elim (hI_not_flip hI_flip)
  have hagree_univ : agreeSet = Set.univ := hagree_clopen.eq_univ hagree_nonempty
  have hbranch_reflect :
      star (exercise8_simple_sqrt_branch k (-star z)) = exercise8_simple_sqrt_branch k z := by
    have hz_mem :
        (⟨z, hz⟩ : UpperHalfPlane) ∈ agreeSet := by
      simpa [hagree_univ]
    simpa [agreeSet, reflectedBranch, originalBranch] using hz_mem
  have hbranch_neg :
      exercise8_simple_sqrt_branch k (-star z) = star (exercise8_simple_sqrt_branch k z) := by
    simpa using congrArg star hbranch_reflect
  -- Rewriting the reflected branch is now enough to transport the reciprocal source integrand.
  rw [exercise8_integrand, exercise8_integrand, hbranch_neg]
  simp

/-- Helper for Cartan section26 0018_Exercise_8: Schwarz reflection of the source branch should
transport the Abel integral from `w` to `-conj w` inside the upper half-plane. -/
lemma exercise8_abel_integral_reflection_upper
    (k : Exercise8Modulus) {w : ℂ} (hw : 0 < w.im) :
    exercise8_abel_integral k (UpperHalfPlane.ofComplex (-star w)) =
      -star (exercise8_abel_integral k (UpperHalfPlane.ofComplex w)) := by
  -- Route correction: this is the only negative-side transport theorem the wrappers should need.
  have hneg_im : 0 < (-star w).im := by
    -- Schwarz reflection preserves the positive imaginary part of the strict upper half-plane.
    simpa using hw
  have hof_neg : (((UpperHalfPlane.ofComplex (-star w) : UpperHalfPlane) : ℂ)) = -star w := by
    -- On reflected strict upper-half-plane points, `ofComplex` is just the subtype constructor.
    simpa [hneg_im] using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply (⟨-star w, hneg_im⟩ : UpperHalfPlane))
  have hof_pos : (((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)) = w := by
    -- The same identification holds for the original strict upper-half-plane point.
    simpa [hw] using
      congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
        (UpperHalfPlane.ofComplex_apply (⟨w, hw⟩ : UpperHalfPlane))
  -- Rewrite both Abel integrals as straight-segment interval integrals before reflecting.
  rw [exercise8_abel_integral_def, exercise8_abel_integral_def, curveIntegral_segment,
    curveIntegral_segment, hof_neg, hof_pos]
  have hpoint :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        ((exercise8_integrand k dz) ((AffineMap.lineMap (0 : ℂ) (-star w)) t)) (-star w - 0) =
          -star (((exercise8_integrand k dz) ((AffineMap.lineMap (0 : ℂ) w) t)) (w - 0)) := by
    intro t ht
    by_cases h0 : t = 0
    · -- At the basepoint the segment integrand is `1`, so the sign comes entirely from the
      -- reflected velocity vector.
      subst h0
      simp [exercise8_integrand, exercise8_simple_sqrt_branch_zero, map_mul]
    · have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le zero_le_one] using ht
      have ht_pos : 0 < t := lt_of_le_of_ne ht'.1 (Ne.symm h0)
      have ht_im : 0 < (((AffineMap.lineMap (0 : ℂ) w) t)).im := by
        -- On the interval core `0 < t ≤ 1`, the segment point stays in the strict upper
        -- half-plane.
        simp [AffineMap.lineMap_apply, hw, ht_pos, mul_pos, mul_comm, mul_left_comm, mul_assoc]
      have hbase :
          exercise8_integrand k ((AffineMap.lineMap (0 : ℂ) (-star w)) t) =
            star (exercise8_integrand k ((AffineMap.lineMap (0 : ℂ) w) t)) := by
        simpa [AffineMap.lineMap_apply, mul_comm, mul_left_comm, mul_assoc] using
          exercise8_integrand_reflection_upper k (z := ((AffineMap.lineMap (0 : ℂ) w) t)) ht_im
      calc
        ((exercise8_integrand k dz) ((AffineMap.lineMap (0 : ℂ) (-star w)) t)) (-star w - 0)
            = exercise8_integrand k ((AffineMap.lineMap (0 : ℂ) (-star w)) t) * (-star w) := by
                simp [mul_comm]
        _ = star (exercise8_integrand k ((AffineMap.lineMap (0 : ℂ) w) t)) * (-star w) := by
              rw [hbase]
        _ = -star (((exercise8_integrand k dz) ((AffineMap.lineMap (0 : ℂ) w) t)) (w - 0)) := by
              calc
                star (exercise8_integrand k ((AffineMap.lineMap (0 : ℂ) w) t)) * (-star w)
                    = -(star (exercise8_integrand k ((AffineMap.lineMap (0 : ℂ) w) t)) *
                        star w) := by
                          ring
                _ = -star (exercise8_integrand k ((AffineMap.lineMap (0 : ℂ) w) t) * w) := by
                      simp [map_mul]
                _ = -star (((exercise8_integrand k dz) ((AffineMap.lineMap (0 : ℂ) w) t))
                      (w - 0)) := by
                      simp [mul_comm]
  -- Conjugate the interval integral pointwise, then pull the outer endpoint factor through `star`
  -- to recover the reflected Abel integral.
  rw [intervalIntegral.integral_congr hpoint]
  let g : ℝ → ℂ :=
    fun t ↦ (((exercise8_integrand k dz) ((AffineMap.lineMap (0 : ℂ) w) t)) (w - 0))
  have hconj : ∫ x in (0 : ℝ)..1, star (g x) = star (∫ t in (0 : ℝ)..1, g t) := by
    rw [intervalIntegral, intervalIntegral]
    simp [integral_conj]
  simpa [g] using congrArg Neg.neg hconj

/-- Helper for Cartan section26 0018_Exercise_8: the reflection `w ↦ -conj w` preserves the
complex metric. -/
lemma exercise8_dist_negStar_eq (a b : ℂ) : dist (-star a) (-star b) = dist a b := by
  -- Negation and complex conjugation are both isometries, so their composite preserves distance.
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖(-star a) - (-star b)‖ = ‖star b - star a‖ := by
      simp [sub_eq_add_neg, add_comm]
    _ = ‖b - a‖ := by
      simpa using norm_star (b - a)
    _ = ‖a - b‖ := by
      simpa using (norm_sub_rev a b).symm

/-- Helper for Cartan section26 0018_Exercise_8: once the pointwise Schwarz reflection formula is
known, a boundary limit at `y` transports to the reflected boundary limit at `-y`. -/
lemma exercise8_abel_integral_tendsto_boundary_trace_reflected
    (k : Exercise8Modulus) (y : ℝ)
    (hpos :
      Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        (nhdsWithin (y : ℂ) UpperHalfPlane.upperHalfPlaneSet)
        (nhds (exercise8_boundary_trace k y))) :
    Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
      (nhdsWithin (((-y : ℝ) : ℂ)) UpperHalfPlane.upperHalfPlaneSet)
      (nhds (exercise8_boundary_trace k (-y))) := by
  let f : ℂ → ℂ := fun w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)
  have hboundary :
      exercise8_boundary_trace k (-y) = -star (exercise8_boundary_trace k y) := by
    simpa [exercise8_boundary_value] using exercise8_boundary_value_reflection k y
  rw [Metric.tendsto_nhdsWithin_nhds] at hpos ⊢
  intro ε hε
  rcases hpos ε hε with ⟨δ, hδpos, hδε⟩
  refine ⟨δ, hδpos, ?_⟩
  intro w hwU hdist
  have hwim : 0 < w.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hwU
  have hdist_reflected :
      dist (-star w) (y : ℂ) < δ := by
    calc
      dist (-star w) (y : ℂ) = dist (-star w) (-star (((-y : ℝ) : ℂ))) := by
        simp
      _ = dist w (((-y : ℝ) : ℂ)) := exercise8_dist_negStar_eq w (((-y : ℝ) : ℂ))
      _ < δ := hdist
  have hupper_reflected : (-star w) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using (show 0 < (-star w).im by simpa using hwim)
  have hclose :
      dist (f (-star w)) (exercise8_boundary_trace k y) < ε :=
    hδε (x := -star w) hupper_reflected hdist_reflected
  have hreflect :
      f w = -star (f (-star w)) := by
    have hstarim : 0 < (-star w).im := by
      simpa using hwim
    -- Apply the pointwise reflection formula to the reflected point `-conj w`.
    simpa [f] using exercise8_abel_integral_reflection_upper k (w := -star w) hstarim
  have hclose_reflected :
      dist (-star (f (-star w))) (-star (exercise8_boundary_trace k y)) < ε := by
    rw [exercise8_dist_negStar_eq]
    exact hclose
  -- Rewrite both the function value and the boundary value through Schwarz reflection.
  simpa [f, hreflect, hboundary] using hclose_reflected
