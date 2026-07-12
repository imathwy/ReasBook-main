import DifferentialForms_Cartan_1970.VI.section26.«0017_Exercise_7».CassiniCore
import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».AbelIntegralCore
import DifferentialForms_Cartan_1970.VI.section26.«0018_Exercise_8».BoundaryTrace

open Set
open scoped UpperHalfPlane

noncomputable section

/-- Helper for Cartan section26 0018_Exercise_8: an ambient upper-half-plane boundary limit for
`w ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w)` transports directly to the canonical
closed-half-plane owner along the strict upper slice. -/
lemma exercise8_closed_extension_tendsto_from_ambient_upper_slice
    (k : Exercise8Modulus) (z : ClosedUpperHalfPlane) {L : ℂ}
    (hambient :
      Filter.Tendsto (fun w : ℂ ↦ exercise8_abel_integral k (UpperHalfPlane.ofComplex w))
        (nhdsWithin (z : ℂ) UpperHalfPlane.upperHalfPlaneSet)
        (nhds L)) :
    Filter.Tendsto (exercise8_closed_extension k)
      (nhdsWithin z {w : ClosedUpperHalfPlane | 0 < ((w : ℂ)).im})
      (nhds L) := by
  let upperSlice : Set ClosedUpperHalfPlane := {w : ClosedUpperHalfPlane | 0 < ((w : ℂ)).im}
  have himage : Subtype.val '' upperSlice = UpperHalfPlane.upperHalfPlaneSet := by
    -- The strict upper slice of the closed half-plane is exactly the ambient open upper half-plane.
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [upperSlice, UpperHalfPlane.upperHalfPlaneSet] using hu
    · intro hw
      refine ⟨⟨w, le_of_lt ?_⟩, ?_, rfl⟩
      · simpa [UpperHalfPlane.upperHalfPlaneSet] using hw
      · simpa [upperSlice, UpperHalfPlane.upperHalfPlaneSet] using hw
  have hcoe :
      Filter.Tendsto (Subtype.val : ClosedUpperHalfPlane → ℂ)
        (nhdsWithin z upperSlice)
        (nhdsWithin (z : ℂ) UpperHalfPlane.upperHalfPlaneSet) := by
    -- The subtype coercion is an embedding, so its `nhdsWithin` image is the ambient upper filter.
    change
      Filter.map (Subtype.val : ClosedUpperHalfPlane → ℂ) (nhdsWithin z upperSlice) ≤
        nhdsWithin (z : ℂ) UpperHalfPlane.upperHalfPlaneSet
    rw [← himage]
    simpa using
      (le_of_eq (Topology.IsEmbedding.map_nhdsWithin_eq
        (f := (Subtype.val : ClosedUpperHalfPlane → ℂ))
        Topology.IsEmbedding.subtypeVal upperSlice z))
  have hambient' :
      Filter.Tendsto
        (fun w : ClosedUpperHalfPlane ↦
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (w : ℂ)))
        (nhdsWithin z upperSlice)
        (nhds L) := by
    -- Reindex the ambient limit along the subtype coercion.
    simpa using hambient.comp hcoe
  have heq :
      Filter.EventuallyEq (nhdsWithin z upperSlice)
        (fun w : ClosedUpperHalfPlane ↦
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (w : ℂ)))
        (exercise8_closed_extension k) := by
    -- On the strict upper slice, the canonical owner is definitionally the Abel integral branch.
    change
      {w : ClosedUpperHalfPlane |
          exercise8_abel_integral k (UpperHalfPlane.ofComplex (w : ℂ)) =
            exercise8_closed_extension k w} ∈
        nhdsWithin z upperSlice
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    have hwne : ((w : ℂ)).im ≠ 0 := ne_of_gt hw
    have h_ofComplex :
        (UpperHalfPlane.ofComplex (w : ℂ) : UpperHalfPlane) =
          ⟨(w : ℂ), exercise8_im_pos_of_closed_nonreal hwne⟩ := by
      simpa using
        (UpperHalfPlane.ofComplex_apply
          (⟨(w : ℂ), exercise8_im_pos_of_closed_nonreal hwne⟩ : UpperHalfPlane))
    -- Compare the two owners after rewriting both to the same interior subtype point.
    change exercise8_abel_integral k (UpperHalfPlane.ofComplex (w : ℂ)) =
      exercise8_closed_extension k w
    rw [exercise8_closed_extension_eq_abel_integral_of_im_ne_zero (k := k) hwne, ← h_ofComplex]
  exact hambient'.congr' heq

/-- Helper for Cartan section26 0018_Exercise_8: the already-solved ambient origin estimate gives
the from-above boundary limit of the canonical closed-half-plane owner at `0`. -/
lemma exercise8_closed_extension_tendsto_boundary_trace_from_above_zero
    (k : Exercise8Modulus) :
    Filter.Tendsto (exercise8_closed_extension k)
      (nhdsWithin (⟨(0 : ℂ), by simp⟩ : ClosedUpperHalfPlane)
        {w : ClosedUpperHalfPlane | 0 < ((w : ℂ)).im})
      (nhds (exercise8_boundary_trace k 0)) := by
  -- The ambient zero theorem already has the correct limit value; only the subtype transport
  -- from the strict upper slice remains.
  exact exercise8_closed_extension_tendsto_from_ambient_upper_slice k ⟨(0 : ℂ), by simp⟩
    (exercise8_abel_integral_tendsto_boundary_trace_zero k)

/-- Helper for Cartan section26 0018_Exercise_8: if a strip approaches a real point through
strictly positive imaginary part, then evaluating the Abel integral at the vertical lift
`Im w * I` tends to the origin value `0`. -/
lemma exercise8_abel_integral_verticalLift_tendsto_zero_of_im_pos
    (k : Exercise8Modulus) {x : ℝ} {s : Set ℂ}
    (hs : ∀ ⦃w : ℂ⦄, w ∈ s → 0 < w.im) :
    Filter.Tendsto
      (fun w : ℂ ↦
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)))
      (nhdsWithin (x : ℂ) s)
      (nhds 0) := by
  let g : ℂ → ℂ := fun w ↦ (w.im : ℂ) * Complex.I
  have hg_cont : Continuous g := by
    -- The vertical-lift map is the continuous composite `w ↦ ofReal (Im w) * I`.
    simpa [g] using
      (Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const
  have hg_tendsto_center :
      Filter.Tendsto g (nhdsWithin (x : ℂ) s) (nhds (g (x : ℂ))) := by
    -- Continuity gives the ordinary limit of the vertical-lift map at the real boundary point.
    exact hg_cont.continuousAt.continuousWithinAt.tendsto
  have hg_tendsto : Filter.Tendsto g (nhdsWithin (x : ℂ) s) (nhds 0) := by
    -- For a real base point, that center value is exactly `0`.
    simpa [g] using hg_tendsto_center
  have hg_within :
      ∀ᶠ w in nhdsWithin (x : ℂ) s, g w ∈ UpperHalfPlane.upperHalfPlaneSet := by
    -- Every point of the source strip lifts to the strict upper half-plane.
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro w hw
    simpa [g, UpperHalfPlane.upperHalfPlaneSet] using hs hw
  have hg_upper :
      Filter.Tendsto g (nhdsWithin (x : ℂ) s) (nhdsWithin (0 : ℂ) UpperHalfPlane.upperHalfPlaneSet) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within g hg_tendsto hg_within
  -- Reindex the solved ambient origin estimate along the vertical-lift map.
  simpa [g, exercise8_boundary_value_zero] using
    (exercise8_abel_integral_tendsto_boundary_trace_zero k).comp hg_upper

/-- Helper for Cartan section26 0018_Exercise_8: on the closed inner strip, the Abel integral of
the vertical lift `Im w * I` tends to `0`. -/
lemma exercise8_abel_integral_verticalLift_tendsto_zero_on_innerStrip
    (k : Exercise8Modulus) {x : ℝ} :
    Filter.Tendsto
      (fun w : ℂ ↦
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)))
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
      (nhds 0) := by
  -- This is the generic vertical-lift estimate specialized to the inner strip.
  refine exercise8_abel_integral_verticalLift_tendsto_zero_of_im_pos k ?_
  intro w hw
  exact hw.1

/-- Helper for Cartan section26 0018_Exercise_8: on the closed right strip, the Abel integral of
the vertical lift `Im w * I` tends to `0`. -/
lemma exercise8_abel_integral_verticalLift_tendsto_zero_on_rightStrip
    (k : Exercise8Modulus) {x : ℝ} :
    Filter.Tendsto
      (fun w : ℂ ↦
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)))
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 ≤ w.re ∧ w.re ≤ 1 / (k : ℝ)})
      (nhds 0) := by
  -- The right strip still approaches the real axis through `Im w > 0`, so the same origin limit
  -- applies.
  refine exercise8_abel_integral_verticalLift_tendsto_zero_of_im_pos k ?_
  intro w hw
  exact hw.1

/-- Helper for Cartan section26 0018_Exercise_8: on the closed top strip, the Abel integral of the
vertical lift `Im w * I` tends to `0`. -/
lemma exercise8_abel_integral_verticalLift_tendsto_zero_on_topStrip
    (k : Exercise8Modulus) {x : ℝ} :
    Filter.Tendsto
      (fun w : ℂ ↦
        exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)))
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 1 / (k : ℝ) ≤ w.re})
      (nhds 0) := by
  -- The top strip differs only in its real-part constraint; the vertical lift still lands in the
  -- same strict upper half-plane.
  refine exercise8_abel_integral_verticalLift_tendsto_zero_of_im_pos k ?_
  intro w hw
  exact hw.1

/-- Helper for Cartan section26 0018_Exercise_8: on the strict upper half-plane, the factor
`1 - z^2` of the radicand always stays in the slit plane of the principal square root. -/
lemma exercise8_one_sub_sq_mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    (1 : ℂ) - z ^ (2 : ℕ) ∈ Complex.slitPlane := by
  by_cases hre : z.re = 0
  · rw [Complex.mem_slitPlane_iff]
    left
    have hz_eq : z = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre]
    have hpos : 0 < 1 + z.im ^ (2 : ℕ) := by positivity
    rw [hz_eq]
    simpa [pow_two] using hpos
  · rw [Complex.mem_slitPlane_iff]
    right
    have him :
        (((1 : ℂ) - z ^ (2 : ℕ)).im : ℝ) = -2 * z.re * z.im := by
      simp [pow_two]
      ring
    rw [him]
    have hcoeff : (-2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero hcoeff hre) hz.ne'

/-- Helper for Cartan section26 0018_Exercise_8: on the strict upper half-plane, the factor
`1 - k^2 z^2` of the radicand also stays in the slit plane of the principal square root. -/
lemma exercise8_one_sub_kSq_sq_mem_slitPlane_of_im_pos
    (k : Exercise8Modulus) {z : ℂ} (hz : 0 < z.im) :
    (1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) ∈ Complex.slitPlane := by
  by_cases hre : z.re = 0
  · rw [Complex.mem_slitPlane_iff]
    left
    have hz_eq : z = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre]
    have hpos : 0 < 1 + (k : ℝ) ^ (2 : ℕ) * z.im ^ (2 : ℕ) := by positivity
    rw [hz_eq]
    simpa [pow_two] using hpos
  · rw [Complex.mem_slitPlane_iff]
    right
    have him :
        (((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ)).im : ℝ) =
          -2 * (k : ℝ) ^ (2 : ℕ) * z.re * z.im := by
      simp [pow_two]
      ring
    rw [him]
    have hcoeff : -2 * (k : ℝ) ^ (2 : ℕ) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Exercise8Modulus.pos k).ne')
    have hmul : z.re * z.im ≠ 0 := mul_ne_zero hre hz.ne'
    simpa [mul_assoc] using mul_ne_zero hcoeff hmul

/-- Helper for Cartan section26 0018_Exercise_8: the explicit product of the two principal square
roots squares back to the Exercise 8 radicand on `Im z > 0`. -/
lemma exercise8_principalFactorization_sq_eq_radicand_on_upper
    (k : Exercise8Modulus) {z : ℂ} (hz : 0 < z.im) :
    (Complex.sqrt ((1 : ℂ) - z ^ (2 : ℕ)) *
        Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ))) ^ (2 : ℕ) =
      exercise8_radicand k z := by
  have hslit_left : (1 : ℂ) - z ^ (2 : ℕ) ∈ Complex.slitPlane :=
    exercise8_one_sub_sq_mem_slitPlane_of_im_pos hz
  have hslit_right :
      (1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ) ∈ Complex.slitPlane :=
    exercise8_one_sub_kSq_sq_mem_slitPlane_of_im_pos k hz
  -- Each principal factor squares back to its radicand factor on the slit plane.
  calc
    (Complex.sqrt ((1 : ℂ) - z ^ (2 : ℕ)) *
          Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ))) ^ (2 : ℕ) =
        (Complex.sqrt ((1 : ℂ) - z ^ (2 : ℕ))) ^ (2 : ℕ) *
          (Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ))) ^ (2 : ℕ) := by
            ring
    _ = ((1 : ℂ) - z ^ (2 : ℕ)) *
          ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ)) := by
            rw [sq_sqrt_of_mem_slitPlane_or_zero (Z := (1 : ℂ) - z ^ (2 : ℕ)) (Or.inr hslit_left)]
            rw [sq_sqrt_of_mem_slitPlane_or_zero
              (Z := (1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ)) (Or.inr hslit_right)]
    _ = exercise8_radicand k z := by
          simp [exercise8_radicand]

/-- Helper for Cartan section26 0018_Exercise_8: the chosen source branch is the product of the
principal square roots of the two radicand factors on the whole strict upper half-plane. -/
lemma exercise8_simpleSqrtBranch_eq_principalFactorization_on_upper
    (k : Exercise8Modulus) {z : ℂ} (hz : 0 < z.im) :
    exercise8_simple_sqrt_branch k z =
      Complex.sqrt ((1 : ℂ) - z ^ (2 : ℕ)) *
        Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * z ^ (2 : ℕ)) := by
  let originalBranch : UpperHalfPlane → ℂ := fun w ↦ exercise8_simple_sqrt_branch k (w : ℂ)
  let principalFactor : UpperHalfPlane → ℂ := fun w ↦
    Complex.sqrt ((1 : ℂ) - (w : ℂ) ^ (2 : ℕ)) *
      Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (w : ℂ) ^ (2 : ℕ))
  have horiginal_cont : Continuous originalBranch := by
    -- The source branch is already continuous on the whole strict upper-half-plane subtype.
    exact (exercise8_simple_sqrt_branch_continuousOn_upper k).comp_continuous
      UpperHalfPlane.continuous_coe fun w ↦ w.2
  have hleft_cont :
      Continuous (fun w : UpperHalfPlane ↦ Complex.sqrt ((1 : ℂ) - (w : ℂ) ^ (2 : ℕ))) := by
    -- The left radicand factor stays inside the slit plane everywhere on the upper half-plane.
    refine Complex.continuousOn_sqrt.comp_continuous
      (continuous_const.sub (UpperHalfPlane.continuous_coe.pow 2)) ?_
    intro w
    exact exercise8_one_sub_sq_mem_slitPlane_of_im_pos w.im_pos
  have hright_cont :
      Continuous
        (fun w : UpperHalfPlane ↦
          Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (w : ℂ) ^ (2 : ℕ))) := by
    -- The same slit-plane control applies to the `1 - k^2 z^2` factor.
    refine Complex.continuousOn_sqrt.comp_continuous
      (continuous_const.sub
        ((continuous_const : Continuous fun _ : UpperHalfPlane ↦ (k : ℂ) ^ (2 : ℕ)).mul
          (UpperHalfPlane.continuous_coe.pow 2))) ?_
    intro w
    exact exercise8_one_sub_kSq_sq_mem_slitPlane_of_im_pos k w.im_pos
  have hprincipal_cont : Continuous principalFactor := by
    -- The explicit principal-factor model is a product of the two slit-plane square-root factors.
    exact hleft_cont.mul hright_cont
  have hsquare :
      ∀ w : UpperHalfPlane, originalBranch w ^ (2 : ℕ) = principalFactor w ^ (2 : ℕ) := by
    intro w
    calc
      originalBranch w ^ (2 : ℕ) = exercise8_radicand k (w : ℂ) := by
        exact exercise8_simple_sqrt_branch_sq_eq_on_upper w.im_pos
      _ = principalFactor w ^ (2 : ℕ) := by
        symm
        simpa [principalFactor] using
          exercise8_principalFactorization_sq_eq_radicand_on_upper k w.im_pos
  let agreeSet : Set UpperHalfPlane := {w | originalBranch w = principalFactor w}
  let flipSet : Set UpperHalfPlane := {w | originalBranch w = -principalFactor w}
  have hagree_closed : IsClosed agreeSet := isClosed_eq horiginal_cont hprincipal_cont
  have hflip_closed : IsClosed flipSet := isClosed_eq horiginal_cont hprincipal_cont.neg
  have hcover : agreeSet ∪ flipSet = Set.univ := by
    ext w
    constructor
    · intro _
      simp
    · intro _
      rcases eq_or_eq_neg_of_sq_eq_sq (originalBranch w) (principalFactor w)
          (by simpa [pow_two] using hsquare w) with hEq | hEq
      · exact Or.inl hEq
      · exact Or.inr hEq
  have hdisjoint : agreeSet ∩ flipSet = (∅ : Set UpperHalfPlane) := by
    ext w
    constructor
    · rintro ⟨hwAgree, hwFlip⟩
      have hzero_principal : principalFactor w = 0 := by
        have hEq : principalFactor w = -principalFactor w := hwAgree.symm.trans hwFlip
        have htwo : (2 : ℂ) * principalFactor w = 0 := by
          have hsum :=
            congrArg
              (fun u : ℂ ↦ u + principalFactor w)
              hEq
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using hsum
        exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
      have hzero_branch : exercise8_simple_sqrt_branch k (w : ℂ) = 0 := by
        exact hwAgree.trans hzero_principal
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
    let branchI : ℂ := exercise8_simple_sqrt_branch k Complex.I
    let factorI : ℂ :=
      Complex.sqrt ((1 : ℂ) - (Complex.I : ℂ) ^ (2 : ℕ)) *
        Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (Complex.I : ℂ) ^ (2 : ℕ))
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
    have hradI_nonneg : 0 ≤ (2 : ℝ) * (1 + (k : ℝ) ^ (2 : ℕ)) := by
      positivity
    have hbranchI_eq :
        branchI = ((((Real.sqrt ((2 : ℝ) * (1 + (k : ℝ) ^ (2 : ℕ)))) : ℝ)) : ℂ) := by
      rw [show branchI = exercise8_simple_sqrt_branch k Complex.I by rfl]
      rw [exercise8_simple_sqrt_branch_eq_principalSqrt_at_I, hradI_eq, Complex.sqrt_of_nonneg]
      · rfl
      · exact_mod_cast hradI_nonneg
    have hbranchI_re_pos : 0 < branchI.re := by
      have hsqrt_pos : 0 < Real.sqrt ((2 : ℝ) * (1 + (k : ℝ) ^ (2 : ℕ))) := by
        apply Real.sqrt_pos.2
        positivity
      rw [hbranchI_eq]
      simpa using hsqrt_pos
    have hfactorI_eq :
        factorI = ((((Real.sqrt 2 * Real.sqrt (1 + (k : ℝ) ^ (2 : ℕ))) : ℝ)) : ℂ) := by
      dsimp [factorI]
      have hsqrt_two : Complex.sqrt ((1 : ℂ) - (Complex.I : ℂ) ^ (2 : ℕ)) = ((Real.sqrt 2 : ℝ) : ℂ) := by
        have htwo_nonneg : 0 ≤ (2 : ℝ) := by positivity
        rw [show ((1 : ℂ) - (Complex.I : ℂ) ^ (2 : ℕ)) = (((2 : ℝ) : ℝ) : ℂ) by norm_num]
        rw [Complex.sqrt_of_nonneg (by exact_mod_cast htwo_nonneg)]
        rfl
      have hsqrt_ksq :
          Complex.sqrt ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (Complex.I : ℂ) ^ (2 : ℕ)) =
            ((Real.sqrt (1 + (k : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
        have hksq_nonneg : 0 ≤ 1 + (k : ℝ) ^ (2 : ℕ) := by positivity
        rw [show ((1 : ℂ) - ((k : ℂ) ^ (2 : ℕ)) * (Complex.I : ℂ) ^ (2 : ℕ)) =
            (((1 + (k : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) by
              simp]
        rw [Complex.sqrt_of_nonneg (by exact_mod_cast hksq_nonneg)]
        rfl
      rw [hsqrt_two, hsqrt_ksq]
      simp
    have hfactorI_re_pos : 0 < (principalFactor UpperHalfPlane.I).re := by
      have hpos_two : 0 < Real.sqrt 2 := by
        have : (0 : ℝ) < 2 := by norm_num
        exact Real.sqrt_pos.2 this
      have hpos_ksq : 0 < Real.sqrt (1 + (k : ℝ) ^ (2 : ℕ)) := by
        apply Real.sqrt_pos.2
        positivity
      have hpos_prod : 0 < Real.sqrt 2 * Real.sqrt (1 + (k : ℝ) ^ (2 : ℕ)) := by
        exact mul_pos hpos_two hpos_ksq
      have hprincipalI_eq : principalFactor UpperHalfPlane.I = factorI := by
        simp [principalFactor, factorI]
      rw [hprincipalI_eq, hfactorI_eq]
      simpa using hpos_prod
    have hI_cover : (UpperHalfPlane.I : UpperHalfPlane) ∈ agreeSet ∪ flipSet := by
      simpa [hcover]
    have hI_not_flip : (UpperHalfPlane.I : UpperHalfPlane) ∉ flipSet := by
      intro hflip
      have hre_eq : branchI.re = -(principalFactor UpperHalfPlane.I).re := by
        simpa [flipSet, originalBranch, branchI] using congrArg Complex.re hflip
      nlinarith
    rcases hI_cover with hI_agree | hI_flip
    · exact ⟨UpperHalfPlane.I, hI_agree⟩
    · exact False.elim (hI_not_flip hI_flip)
  have hagree_univ : agreeSet = Set.univ := hagree_clopen.eq_univ hagree_nonempty
  have hz_mem : (⟨z, hz⟩ : UpperHalfPlane) ∈ agreeSet := by
    simpa [hagree_univ]
  -- The interior anchor at `i` rules out the negative global sign, so the two owners agree
  -- everywhere on the connected upper half-plane.
  simpa [agreeSet, originalBranch, principalFactor] using hz_mem

/-- Helper for Cartan section26 0018_Exercise_8: after the vertical lift at height `Im w`, the
remaining scaled residual on the inner strip collapses to `0` because every scaled endpoint stays
inside the near-zero ball where the source integrand is bounded by `2`. -/
lemma exercise8_abel_integral_sub_verticalLift_sub_horizontal_tendsto_zero_on_innerStrip
    (k : Exercise8Modulus) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun w : ℂ ↦
        exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
          ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z)
      (nhdsWithin (x : ℂ) {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1})
      (nhds 0) := by
  let strip : Set ℂ := {w : ℂ | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1}
  rcases exercise8_integrand_bounded_near_zero k with ⟨R, hR_pos, hR_bound⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let δ : ℝ := min (R / 4) (min 1 (ε / 12))
  refine ⟨δ, ?_, ?_⟩
  · -- The metric radius is chosen to keep both scaled endpoints in the near-zero ball and to
    -- convert the final `O(Im w)` bound into the requested `ε`.
    dsimp [δ]
    refine lt_min ?_ ?_
    · positivity
    · refine lt_min ?_ ?_
      · norm_num
      · positivity
  · intro w hw hdist
    rcases hw with ⟨hwim, hwre0, hwre1⟩
    have hx_re : ((x : ℂ)).re = x := by simp
    have him_le : |w.im| ≤ dist w (x : ℂ) := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, hx_re] using
        (Complex.abs_im_le_norm (w - (x : ℂ)))
    have him_lt : |w.im| < δ := lt_of_le_of_lt him_le hdist
    have hwim_lt_δ : w.im < δ := by
      simpa [abs_of_nonneg hwim.le] using him_lt
    have hwim_lt_Rquarter : w.im < R / 4 := by
      exact lt_of_lt_of_le hwim_lt_δ (by dsimp [δ]; exact min_le_left _ _)
    have hwim_lt_one : w.im < 1 := by
      exact lt_of_lt_of_le hwim_lt_δ (by dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_left _ _))
    have hwim_lt_eps : w.im < ε / 12 := by
      exact lt_of_lt_of_le hwim_lt_δ (by dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_right _ _))
    have hnorm_w_le_two : ‖w‖ ≤ 2 := by
      -- On the inner strip and inside the `δ ≤ 1` ball above the real axis, both coordinates are
      -- bounded by `1`, so the ambient norm is at most `2`.
      have hreim : (((w.re : ℂ) + (w.im : ℂ) * Complex.I) : ℂ) = w := by
        simpa using Complex.re_add_im w
      calc
        ‖w‖ = ‖((w.re : ℂ) + (w.im : ℂ) * Complex.I)‖ := by
          simpa [hreim]
        _ ≤ ‖(w.re : ℂ)‖ + ‖(w.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |w.re| + |w.im| := by simp
        _ = w.re + w.im := by rw [abs_of_nonneg hwre0, abs_of_nonneg hwim.le]
        _ ≤ 2 := by linarith
    have hscaled_norm_le :
        ‖(w.im : ℂ) * w‖ ≤ 2 * w.im := by
      calc
        ‖(w.im : ℂ) * w‖ = w.im * ‖w‖ := by
          simpa [abs_of_nonneg hwim.le] using norm_mul (w.im : ℂ) w
        _ ≤ w.im * 2 := by
          gcongr
        _ = 2 * w.im := by ring
    have hscaled_small : ‖(w.im : ℂ) * w‖ < R := by
      calc
        ‖(w.im : ℂ) * w‖ ≤ 2 * w.im := hscaled_norm_le
        _ < 2 * (R / 4) := by
          gcongr
        _ < R := by
          nlinarith
    have hvertical_norm_le :
        ‖(((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ ≤ w.im := by
      have hvertical_eq :
          ‖(((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ = w.im * w.im := by
        have hsq_nonneg : 0 ≤ w.im * w.im := by positivity
        simpa [abs_of_nonneg hsq_nonneg] using
          (norm_mul (((w.im * w.im : ℝ) : ℂ)) Complex.I)
      rw [hvertical_eq]
      nlinarith [hwim, hwim_lt_one]
    have hvertical_small : ‖(((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ < R := by
      calc
        ‖(((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ ≤ w.im := hvertical_norm_le
        _ < R / 4 := hwim_lt_Rquarter
        _ < R := by nlinarith
    have hscaled_im : 0 < (((w.im : ℂ) * w).im) := by
      simpa [Complex.mul_im, mul_comm] using mul_pos hwim hwim
    have hvertical_im : 0 < ((((w.im * w.im : ℝ) : ℂ) * Complex.I).im) := by
      simpa using mul_pos hwim hwim
    have hscaled_coe :
        (((UpperHalfPlane.ofComplex ((w.im : ℂ) * w) : UpperHalfPlane) : ℂ)) =
          (w.im : ℂ) * w := by
      simpa using
        congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
          (UpperHalfPlane.ofComplex_apply
            (⟨(w.im : ℂ) * w, hscaled_im⟩ : UpperHalfPlane))
    have hvertical_coe :
        (((UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) :
            UpperHalfPlane) : ℂ)) =
          (((w.im * w.im : ℝ) : ℂ) * Complex.I) := by
      simpa using
        congrArg (fun u : UpperHalfPlane ↦ (u : ℂ))
          (UpperHalfPlane.ofComplex_apply
            (⟨(((w.im * w.im : ℝ) : ℂ) * Complex.I), hvertical_im⟩ : UpperHalfPlane))
    have hscaled_small_ofComplex :
        ‖(((UpperHalfPlane.ofComplex ((w.im : ℂ) * w) : UpperHalfPlane) : ℂ))‖ < R := by
      rw [hscaled_coe]
      exact hscaled_small
    have hvertical_small_ofComplex :
        ‖(((UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) :
            UpperHalfPlane) : ℂ))‖ < R := by
      rw [hvertical_coe]
      exact hvertical_small
    let scaledLift : UpperHalfPlane := UpperHalfPlane.ofComplex ((w.im : ℂ) * w)
    let verticalLift : UpperHalfPlane :=
      UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I))
    have hscaledLift_coe : ((scaledLift : UpperHalfPlane) : ℂ) = (w.im : ℂ) * w := by
      simpa [scaledLift] using hscaled_coe
    have hverticalLift_coe :
        ((verticalLift : UpperHalfPlane) : ℂ) = (((w.im * w.im : ℝ) : ℂ) * Complex.I) := by
      simpa [verticalLift] using hvertical_coe
    have habel_scaled :
        ‖exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * w))‖ ≤
          2 * ‖(w.im : ℂ) * w‖ := by
      simpa [hscaled_coe] using
        exercise8_abel_integral_norm_le_two_mul_norm_of_small k hR_bound
          (UpperHalfPlane.ofComplex ((w.im : ℂ) * w))
          hscaled_small_ofComplex
    have habel_vertical :
        ‖exercise8_abel_integral k
            (UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I)))‖ ≤
          2 * ‖(((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ := by
      have habel_vertical_raw :=
        exercise8_abel_integral_norm_le_two_mul_norm_of_small k hR_bound
          verticalLift
          hvertical_small_ofComplex
      calc
        ‖exercise8_abel_integral k
            (UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I)))‖ =
            ‖exercise8_abel_integral k verticalLift‖ := by
              simp [verticalLift]
        _ ≤ 2 * ‖((verticalLift : UpperHalfPlane) : ℂ)‖ := habel_vertical_raw
        _ = 2 * ‖(((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ := by
              rw [hverticalLift_coe]
    have hsegment :
        ‖∫ᶜ z in Path.segment ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) ((w.im : ℂ) * w),
            (exercise8_integrand k dz) z‖ ≤
          2 * ‖(w.im : ℂ) * w - (((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ := by
      have hsegment_raw :=
        exercise8_segment_integral_norm_le_two_mul_norm_sub_of_small k hR_bound
          verticalLift
          scaledLift
          hvertical_small_ofComplex
          hscaled_small_ofComplex
      calc
        ‖∫ᶜ z in Path.segment ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) ((w.im : ℂ) * w),
            (exercise8_integrand k dz) z‖ =
            ‖∫ᶜ z in Path.segment ((verticalLift : UpperHalfPlane) : ℂ)
                ((scaledLift : UpperHalfPlane) : ℂ), (exercise8_integrand k dz) z‖ := by
              rw [hverticalLift_coe, hscaledLift_coe]
        _ ≤ 2 * ‖((scaledLift : UpperHalfPlane) : ℂ) - ((verticalLift : UpperHalfPlane) : ℂ)‖ :=
              hsegment_raw
        _ = 2 * ‖(w.im : ℂ) * w - (((w.im * w.im : ℝ) : ℂ) * Complex.I)‖ := by
              rw [hverticalLift_coe, hscaledLift_coe]
    have hsegment_small :
        ‖∫ᶜ z in Path.segment ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) ((w.im : ℂ) * w),
            (exercise8_integrand k dz) z‖ ≤
          6 * w.im := by
      nlinarith [hsegment, norm_sub_le ((w.im : ℂ) * w) ((((w.im * w.im : ℝ) : ℂ) * Complex.I)),
        hscaled_norm_le, hvertical_norm_le]
    have hrewrite :
        exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z =
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * w)) -
            exercise8_abel_integral k
              (UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I))) -
            ∫ᶜ z in Path.segment ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) ((w.im : ℂ) * w),
              (exercise8_integrand k dz) z := by
      -- Route correction: specialize the exact scaled-residual identity at `r = Im w` so the
      -- only remaining work is the near-zero norm estimate.
      let u : UpperHalfPlane := UpperHalfPlane.ofComplex w
      have hu_coe : ((u : UpperHalfPlane) : ℂ) = w := by
        simpa [u] using
          congrArg (fun z : UpperHalfPlane ↦ (z : ℂ))
            (UpperHalfPlane.ofComplex_apply_of_im_pos hwim)
      have hu_im : ((u : UpperHalfPlane) : ℂ).im = w.im := by
        rw [hu_coe]
      have hu_im' : u.im = w.im := by
        simpa using hu_im
      have hrewrite_raw :=
        exercise8_abel_integral_sub_verticalLift_sub_horizontal_eq_scaledResidual
          k u (r := w.im) hwim hwim_lt_one.le
      have hrewrite_raw' := hrewrite_raw
      simp [hu_im, pow_two, mul_assoc, mul_left_comm, mul_comm] at hrewrite_raw'
      rw [hu_im'] at hrewrite_raw'
      calc
        exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z =
          exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) (u : ℂ),
              (exercise8_integrand k dz) z := by
                rw [hu_coe]
        _ = exercise8_abel_integral k u -
              exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
              ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) (u : ℂ),
                (exercise8_integrand k dz) z := by
                rfl
        _ = exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * (u : ℂ))) -
              exercise8_abel_integral k
                (UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I))) -
              ∫ᶜ z in Path.segment ((((w.im * w.im : ℝ) : ℂ) * Complex.I))
                  ((w.im : ℂ) * (u : ℂ)),
                (exercise8_integrand k dz) z := by
                simpa [mul_comm] using hrewrite_raw'
        _ =
          exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * w)) -
            exercise8_abel_integral k
              (UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I))) -
            ∫ᶜ z in Path.segment ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) ((w.im : ℂ) * w),
              (exercise8_integrand k dz) z := by
                rw [hu_coe]
    let a :=
      exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * w))
    let b :=
      exercise8_abel_integral k
        (UpperHalfPlane.ofComplex ((((w.im * w.im : ℝ) : ℂ) * Complex.I)))
    let c :=
      ∫ᶜ z in Path.segment ((((w.im * w.im : ℝ) : ℂ) * Complex.I)) ((w.im : ℂ) * w),
        (exercise8_integrand k dz) z
    have htriangle : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      -- The scaled residual is bounded by summing the norms of its three near-zero pieces.
      calc
        ‖a - b - c‖ = ‖a + (-b + -c)‖ := by
          simp [sub_eq_add_neg, add_assoc]
        _ ≤ ‖a‖ + ‖-b + -c‖ := norm_add_le _ _
        _ ≤ ‖a‖ + (‖-b‖ + ‖-c‖) := by
          gcongr
          exact norm_add_le _ _
        _ = ‖a‖ + ‖b‖ + ‖c‖ := by
          simp [add_assoc]
    have hmain :
        ‖exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z‖ ≤
          12 * w.im := by
      -- The exact residual identity plus the three near-zero estimates produce the final
      -- `O(Im w)` bound on the inner strip.
      rw [hrewrite]
      dsimp [a, b, c] at htriangle
      nlinarith [htriangle, habel_scaled, habel_vertical, hsegment_small,
        hscaled_norm_le, hvertical_norm_le]
    have hmain_lt :
        ‖exercise8_abel_integral k (UpperHalfPlane.ofComplex w) -
            exercise8_abel_integral k (UpperHalfPlane.ofComplex ((w.im : ℂ) * Complex.I)) -
            ∫ᶜ z in Path.segment ((w.im : ℂ) * Complex.I) w, (exercise8_integrand k dz) z‖ <
          ε := by
      have hεbound : 12 * w.im < ε := by
        nlinarith
      exact lt_of_le_of_lt hmain hεbound
    simpa [dist_eq_norm, strip] using hmain_lt

/-- Helper for Cartan section26 0018_Exercise_8: a horizontal segment at height `y` rewrites
directly as the interval integral on `a..b`, without keeping the affine `0..1` parameter in later
transport lemmas. -/
lemma exercise8_horizontal_segment_eq_directIntervalIntegral
    (k : Exercise8Modulus) (a b y : ℝ) :
    ∫ᶜ z in Path.segment ((a : ℂ) + (y : ℂ) * Complex.I)
        ((b : ℂ) + (y : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ t in a..b, exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I) := by
  -- Route correction: normalize the horizontal source segment once to the exact `a..b` interval
  -- form, so later boundary-transport lemmas no longer carry the auxiliary affine parameter.
  by_cases hab : a = b
  · -- When the endpoints coincide, both the curve integral and the interval integral vanish.
    subst hab
    rw [exercise8_horizontal_segment_eq_intervalIntegral]
    simp
  · -- Otherwise the affine change of variables from `0..1` to `a..b` cancels the Jacobian
    -- factor exactly.
    rw [exercise8_horizontal_segment_eq_intervalIntegral]
    have hparam :
        (fun t : ℝ ↦
          exercise8_integrand k ((((a + t * (b - a)) : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
          fun t : ℝ ↦
            exercise8_integrand k ((((a + (b - a) * t) : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
      funext t
      ring_nf
    rw [hparam]
    rw [intervalIntegral.integral_comp_add_mul
      (a := (0 : ℝ)) (b := 1) (c := b - a) (d := a)
      (fun t : ℝ ↦ exercise8_integrand k ((t : ℂ) + (y : ℂ) * Complex.I))
      (sub_ne_zero.mpr (Ne.symm hab))]
    rw [show
      ((b - a)⁻¹ •
          ∫ x in a + (b - a) * 0..a + (b - a) * 1,
            exercise8_integrand k ((x : ℂ) + (y : ℂ) * Complex.I) : ℂ) =
        ((((b - a)⁻¹ : ℝ) : ℂ) *
            ∫ x in a + (b - a) * 0..a + (b - a) * 1,
              exercise8_integrand k ((x : ℂ) + (y : ℂ) * Complex.I)) by
      rfl]
    have hmul : (((b - a : ℝ) : ℂ) * (((b - a)⁻¹ : ℝ) : ℂ)) = 1 := by
      exact_mod_cast mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm hab))
    calc
      ((((b - a)⁻¹ : ℝ) : ℂ) *
          ∫ x in a + (b - a) * 0..a + (b - a) * 1,
            exercise8_integrand k ((x : ℂ) + (y : ℂ) * Complex.I)) *
          ((b - a : ℝ) : ℂ) =
        ((((b - a : ℝ) : ℂ) * (((b - a)⁻¹ : ℝ) : ℂ)) *
            ∫ x in a + (b - a) * 0..a + (b - a) * 1,
              exercise8_integrand k ((x : ℂ) + (y : ℂ) * Complex.I)) := by
          ring
      _ =
        ∫ x in a + (b - a) * 0..a + (b - a) * 1,
          exercise8_integrand k ((x : ℂ) + (y : ℂ) * Complex.I) := by
            rw [hmul, one_mul]
      _ = ∫ x in a..b, exercise8_integrand k ((x : ℂ) + (y : ℂ) * Complex.I) := by
            simp

/-- Helper for Cartan section26 0018_Exercise_8: at positive height, horizontal Exercise 8
segments split additively at a real cutoff because they lie in the convex upper half-plane. -/
lemma exercise8_horizontal_segment_add
    (k : Exercise8Modulus) (a b c y : ℝ) (hy : 0 < y) :
    (∫ᶜ z in Path.segment ((a : ℂ) + (y : ℂ) * Complex.I)
          ((b : ℂ) + (y : ℂ) * Complex.I), (exercise8_integrand k dz) z) +
        ∫ᶜ z in Path.segment ((b : ℂ) + (y : ℂ) * Complex.I)
          ((c : ℂ) + (y : ℂ) * Complex.I), (exercise8_integrand k dz) z =
      ∫ᶜ z in Path.segment ((a : ℂ) + (y : ℂ) * Complex.I)
        ((c : ℂ) + (y : ℂ) * Complex.I), (exercise8_integrand k dz) z := by
  let za : UpperHalfPlane := ⟨((a : ℂ) + (y : ℂ) * Complex.I), by simpa using hy⟩
  let zb : UpperHalfPlane := ⟨((b : ℂ) + (y : ℂ) * Complex.I), by simpa using hy⟩
  let zc : UpperHalfPlane := ⟨((c : ℂ) + (y : ℂ) * Complex.I), by simpa using hy⟩
  -- Every cutoff point stays in the strict upper half-plane, so the already-proved segment
  -- additivity theorem applies verbatim to the three horizontal subsegments.
  simpa [za, zb, zc] using exercise8_segment_integral_add k za zb zc

/-- Helper for Cartan section26 0018_Exercise_8: on the positive right edge, the factor
`1 - z^2` of the radicand has norm bounded below by its real-axis value `t^2 - 1`. -/
lemma exercise8_rightFactor_norm_lower_on_right
    {t y : ℝ} (ht : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ))) (hy : 0 < y) :
    t ^ (2 : ℕ) - 1 ≤
      ‖(1 : ℂ) - (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ))‖ := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hfactor_nonneg : 0 ≤ t ^ (2 : ℕ) - 1 := by
    nlinarith [ht.1]
  have hsq :
      (t ^ (2 : ℕ) - 1) ^ (2 : ℕ) ≤
        Complex.normSq ((1 : ℂ) - (z ^ (2 : ℕ))) := by
    -- Expanding the norm square shows that the positive `y`-terms only increase the boundary
    -- value `(t^2 - 1)^2`.
    rw [show
        Complex.normSq ((1 : ℂ) - (z ^ (2 : ℕ))) =
          (1 - t ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ) +
            (2 * t * y) ^ (2 : ℕ) by
      simp [z, Complex.normSq_apply, pow_two]
      ring_nf]
    nlinarith
  have hnorm :
      ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ ^ (2 : ℕ) =
        Complex.normSq ((1 : ℂ) - (z ^ (2 : ℕ))) := by
    simpa using Complex.sq_norm ((1 : ℂ) - (z ^ (2 : ℕ)))
  -- Compare the squared lower bound with the squared norm, then return to norms.
  nlinarith [hfactor_nonneg, norm_nonneg ((1 : ℂ) - (z ^ (2 : ℕ))), hsq, hnorm]

/-- Helper for Cartan section26 0018_Exercise_8: on the positive right edge, the factor
`1 - k^2 z^2` of the radicand has norm bounded below by its real-axis value
`1 - k^2 t^2`. -/
lemma exercise8_modulusFactor_norm_lower_on_right
    (k : Exercise8Modulus) {t y : ℝ} (ht : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ))) (hy : 0 < y) :
    1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) ≤
      ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (2 : ℕ)))‖ := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hfactor_nonneg : 0 ≤ 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
    have hkt_lt : (k : ℝ) * t < (k : ℝ) * (1 / (k : ℝ)) := by
      exact mul_lt_mul_of_pos_left ht.2 hk_pos
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    have hkt_lt_one : (k : ℝ) * t < 1 := by
      rw [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp [hk_ne]] at hkt_lt
      exact hkt_lt
    have hkt_nonneg : 0 ≤ (k : ℝ) * t := by
      nlinarith [hk_pos, ht.1]
    have hsq : ((k : ℝ) * t) ^ (2 : ℕ) < 1 := by
      nlinarith [hkt_lt_one, hkt_nonneg]
    have hsq' : (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) < 1 := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    linarith
  have hsq :
      (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        Complex.normSq ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))) := by
    -- The same explicit norm expansion works for the `1 - k^2 z^2` factor.
    rw [show
        Complex.normSq ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))) =
          (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) +
              (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ)) ^ (2 : ℕ) +
            (2 * (k : ℝ) ^ (2 : ℕ) * t * y) ^ (2 : ℕ) by
      simp [z, Complex.normSq_apply, pow_two]
      ring_nf]
    have hbase :
        (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ^ (2 : ℕ) ≤
          (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) +
              (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ)) ^ (2 : ℕ) := by
      have hy_term_nonneg : 0 ≤ (k : ℝ) ^ (2 : ℕ) * y ^ (2 : ℕ) := by
        positivity
      nlinarith
    have htail_nonneg : 0 ≤ (2 * (k : ℝ) ^ (2 : ℕ) * t * y) ^ (2 : ℕ) := by
      positivity
    exact le_trans hbase (by nlinarith)
  have hnorm :
      ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ ^ (2 : ℕ) =
        Complex.normSq ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))) := by
    simpa using Complex.sq_norm ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ))))
  -- As on the first factor, the squared inequality already implies the desired norm bound.
  nlinarith [hfactor_nonneg,
    norm_nonneg ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))), hsq, hnorm]

/-- Helper for Cartan section26 0018_Exercise_8: on the positive right edge, the complex
integrand is dominated by the imaginary-period kernel. -/
lemma exercise8_integrand_norm_le_imaginaryKernel_on_right
    (k : Exercise8Modulus) {t y : ℝ} (ht : t ∈ Ioo (1 : ℝ) (1 / (k : ℝ))) (hy : 0 < y) :
    ‖exercise8_integrand k (((t : ℂ) + (y : ℂ) * Complex.I))‖ ≤ exercise8_imaginary_kernel k t := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hz : 0 < z.im := by
    simpa [z] using hy
  have hfactor1_pos : 0 < t ^ (2 : ℕ) - 1 := by
    nlinarith [ht.1]
  have hfactor2_pos : 0 < 1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    have hk_pos : 0 < (k : ℝ) := Exercise8Modulus.pos k
    have hkt_lt : (k : ℝ) * t < (k : ℝ) * (1 / (k : ℝ)) := by
      exact mul_lt_mul_of_pos_left ht.2 hk_pos
    have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
    have hkt_lt_one : (k : ℝ) * t < 1 := by
      rw [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp [hk_ne]] at hkt_lt
      exact hkt_lt
    have hkt_nonneg : 0 ≤ (k : ℝ) * t := by
      nlinarith [hk_pos, ht.1]
    have hsq : ((k : ℝ) * t) ^ (2 : ℕ) < 1 := by
      nlinarith [hkt_lt_one, hkt_nonneg]
    have hsq' : (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) < 1 := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    linarith
  have hfactor1 :
      t ^ (2 : ℕ) - 1 ≤ ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ :=
    exercise8_rightFactor_norm_lower_on_right ht hy
  have hfactor2 :
      1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) ≤
        ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ :=
    exercise8_modulusFactor_norm_lower_on_right k ht hy
  have hmul :
      (t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤
        ‖exercise8_radicand k z‖ := by
    have hmul_aux :
        (t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤
          ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ *
            ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ := by
      nlinarith [hfactor1, hfactor2,
        norm_nonneg ((1 : ℂ) - (z ^ (2 : ℕ))),
        norm_nonneg ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ))))]
    calc
      (t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤
          ‖(1 : ℂ) - (z ^ (2 : ℕ))‖ *
            ‖(1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ)))‖ := hmul_aux
      _ = ‖((1 : ℂ) - (z ^ (2 : ℕ))) *
            ((1 : ℂ) - (((k : ℂ) ^ (2 : ℕ)) * (z ^ (2 : ℕ))))‖ := by
            rw [norm_mul]
      _ = ‖exercise8_radicand k z‖ := by
            simp [exercise8_radicand, z, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hbranch_sq :
      ‖exercise8_simple_sqrt_branch k z‖ ^ (2 : ℕ) = ‖exercise8_radicand k z‖ := by
    calc
      ‖exercise8_simple_sqrt_branch k z‖ ^ (2 : ℕ) =
          ‖exercise8_simple_sqrt_branch k z ^ (2 : ℕ)‖ := by
            simp [sq]
      _ = ‖exercise8_radicand k z‖ := by
            rw [exercise8_simple_sqrt_branch_sq_eq_on_upper hz]
  have hsqrt :
      Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) ≤
        ‖exercise8_simple_sqrt_branch k z‖ := by
    have hprod_nonneg :
        0 ≤ (t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
      positivity
    nlinarith [hmul, hbranch_sq, hprod_nonneg,
      norm_nonneg (exercise8_simple_sqrt_branch k z), Real.sq_sqrt hprod_nonneg]
  have hbranch_pos : 0 < ‖exercise8_simple_sqrt_branch k z‖ := by
    exact norm_pos_iff.mpr (exercise8_simple_sqrt_branch_ne_zero_on_upper hz)
  have hsqrt_pos :
      0 < Real.sqrt ((t ^ (2 : ℕ) - 1) * (1 - (k : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ))) := by
    apply Real.sqrt_pos.2
    positivity
  -- Invert the lower bound on the branch norm to recover the right-edge majorant.
  rw [exercise8_integrand, exercise8_imaginary_kernel]
  simpa [z] using (inv_le_inv₀ hbranch_pos hsqrt_pos).2 hsqrt
