import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».ShiftedLogResidueData

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the literal rational evaluation
`rationalEval P Q` is meromorphic on the whole complex plane, so the global meromorphic normal
form `toMeromorphicNFOn _ Set.univ` can be used to repair removable roots on the positive real
axis. -/
lemma rationalEval_meromorphicOn_univ
    (P Q : Polynomial ℂ) :
    MeromorphicOn (rationalEval P Q) Set.univ := by
  have hPmer_univ : MeromorphicOn (fun w : ℂ ↦ P.eval w) Set.univ := by
    -- Polynomial evaluation is entire, hence meromorphic, on the whole plane.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) P).meromorphicOn
  have hQmer_univ : MeromorphicOn (fun w : ℂ ↦ Q.eval w) Set.univ := by
    -- The denominator polynomial enjoys the same entire-function meromorphicity.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) Q).meromorphicOn
  -- Meromorphicity is stable under pointwise division.
  simpa [rationalEval] using hPmer_univ.div hQmer_univ

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: away from genuine poles, the global
meromorphic normal form of `rationalEval P Q` is holomorphic and therefore differentiable. -/
lemma rationalEval_univNormalForm_differentiableAt_of_not_pole
    (P Q : Polynomial ℂ) {z : ℂ}
    (hz : ¬ meromorphicOrderAt (rationalEval P Q) z < 0) :
    DifferentiableAt ℂ (toMeromorphicNFOn (rationalEval P Q) Set.univ) z := by
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f Set.univ := rationalEval_meromorphicOn_univ P Q
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- Outside the pole locus, the local meromorphic order is nonnegative.
    exact le_of_not_gt hz
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f Set.univ) z := by
    -- Passing to normal form preserves the local meromorphic order on `Set.univ`.
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hmeromorphic (by simp)]
    exact horder_nonneg_f
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f Set.univ) z :=
    (meromorphicNFOn_toMeromorphicNFOn f Set.univ) (by simp)
  -- Nonnegative order at the normal-form representative upgrades to analyticity.
  exact (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).differentiableAt

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: whenever the denominator does not
vanish, the global meromorphic normal form agrees pointwise with the literal quotient. This is the
exact bridge used on compact positive-real intervals away from removable denominator roots. -/
lemma rationalEval_univNormalForm_eq_of_denominator_ne_zero
    (P Q : Polynomial ℂ) {z : ℂ} (hQz : Q.eval z ≠ 0) :
    toMeromorphicNFOn (rationalEval P Q) Set.univ z = rationalEval P Q z := by
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f Set.univ := rationalEval_meromorphicOn_univ P Q
  have hrat : AnalyticAt ℂ f z := by
    -- Off the denominator roots, the quotient is an honest holomorphic function.
    have hPanalytic : AnalyticAt ℂ (fun w : ℂ ↦ P.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) P z (by simp))
    have hQanalytic : AnalyticAt ℂ (fun w : ℂ ↦ Q.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) Q z (by simp))
    simpa [f, rationalEval] using hPanalytic.div hQanalytic hQz
  calc
    toMeromorphicNFOn f Set.univ z = toMeromorphicNFAt f z z := by
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmeromorphic (by simp)]
    _ = f z := by
      exact congrFun (toMeromorphicNFAt_eq_self.2 hrat.meromorphicNFAt) z

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: on any compact interval contained in
`[0, ∞)`, the literal real-axis rational kernel is uniformly bounded because the global
meromorphic normal form is continuous there and the only possible discrepancies occur at
denominator roots, where Lean's literal quotient already takes the value `0`. -/
lemma rationalEval_norm_le_on_nonneg_Icc
    (P Q : Polynomial ℂ) {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∃ M : ℝ,
      ∀ x ∈ Set.Icc a b, ‖rationalEval P Q (x : ℂ)‖ ≤ M := by
  let g : ℝ → ℂ := fun x ↦ toMeromorphicNFOn (rationalEval P Q) Set.univ (x : ℂ)
  have hcont : ContinuousOn g (Set.Icc a b) := by
    intro x hx
    -- Every nonnegative real point is a non-pole, so the global normal form is continuous there.
    have hcontComplex :
        ContinuousAt (fun z : ℂ ↦ toMeromorphicNFOn (rationalEval P Q) Set.univ z) (x : ℂ) := by
      exact
        (rationalEval_univNormalForm_differentiableAt_of_not_pole
          P Q (z := (x : ℂ)) (hcut' x (le_trans ha hx.1))).continuousAt
    have hcontReal : ContinuousAt g x := by
      simpa [g] using
        hcontComplex.comp
          (Complex.continuous_ofReal.continuousAt :
            ContinuousAt (fun y : ℝ ↦ (y : ℂ)) x)
    exact hcontReal.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn
    (f := g) hcont
  refine ⟨max M 0, ?_⟩
  intro x hx
  by_cases hQx : Q.eval (x : ℂ) = 0
  · -- At denominator roots, the literal quotient is `0`, so the compact bound is automatic.
    simp [rationalEval, hQx]
  · -- Away from denominator roots, the global normal form equals the literal rational function.
    have hEq :
        toMeromorphicNFOn (rationalEval P Q) Set.univ (x : ℂ) = rationalEval P Q (x : ℂ) :=
      rationalEval_univNormalForm_eq_of_denominator_ne_zero P Q hQx
    exact le_trans (by simpa [g, hEq] using hM x hx) (le_max_left M 0)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the positive-real rational kernel is
integrable on `(0, ∞)` under the degree-gap and no-pole-on-the-cut hypotheses. Near `0`, the
global meromorphic normal form gives a compact bound; on the tail, the degree gap gives the
standard `x⁻²` decay. -/
lemma rationalEval_integrableOn_Ioi
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    IntegrableOn (fun x : ℝ ↦ rationalEval P Q (x : ℂ)) (Set.Ioi (0 : ℝ)) volume := by
  let f : ℝ → ℂ := fun x ↦ rationalEval P Q (x : ℂ)
  have hf_meas : Measurable f := by
    -- The literal quotient is a measurable algebraic expression in the real variable.
    fun_prop
  obtain ⟨M₀, hM₀⟩ := rationalEval_norm_le_on_nonneg_Icc P Q
    (a := 0) (b := 1) le_rfl zero_le_one hcut'
  have hlowDom :
      IntegrableOn (fun _ : ℝ ↦ M₀) (Set.Ioc (0 : ℝ) 1) volume := by
    exact MeasureTheory.integrableOn_const
      (μ := volume) (s := Set.Ioc (0 : ℝ) 1) (C := M₀) (hs := by simp)
  have hlow :
      IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume := by
    have hlowDom' : Integrable (fun _ : ℝ ↦ M₀) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      hlowDom
    refine Integrable.mono' hlowDom' hf_meas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hbound := hM₀ x hxIcc
    exact hbound
  obtain ⟨K, R₀, hKR, hdecay⟩ := rationalEval_decay_of_degree_gap_two P Q hdeg
  let S : ℝ := max 1 R₀
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨M₁, hM₁⟩ := rationalEval_norm_le_on_nonneg_Icc P Q
    (a := 1) (b := S) zero_le_one (le_max_left _ _) hcut'
  have hmidDom :
      IntegrableOn (fun _ : ℝ ↦ M₁) (Set.Ioc (1 : ℝ) S) volume := by
    exact MeasureTheory.integrableOn_const
      (μ := volume) (s := Set.Ioc (1 : ℝ) S) (C := M₁) (hs := by simp [S])
  have hmid :
      IntegrableOn f (Set.Ioc (1 : ℝ) S) volume := by
    have hmidDom' : Integrable (fun _ : ℝ ↦ M₁) (volume.restrict (Set.Ioc (1 : ℝ) S)) :=
      hmidDom
    refine Integrable.mono' hmidDom' hf_meas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hxIcc : x ∈ Set.Icc (1 : ℝ) S := ⟨hx.1.le, hx.2⟩
    have hbound := hM₁ x hxIcc
    exact hbound
  have hpow :
      IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℝ)) (Set.Ioi S) volume := by
    simpa using
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := S) (by norm_num) hSpos)
  have hpowZ :
      IntegrableOn (fun x : ℝ ↦ x ^ (-2 : ℤ)) (Set.Ioi S) volume := by
    simpa using hpow
  have htailReal :
      IntegrableOn (fun x : ℝ ↦ K * x ^ (-2 : ℤ)) (Set.Ioi S) volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpowZ.const_mul K
  have htail :
      IntegrableOn f (Set.Ioi S) volume := by
    have htailDom' :
        Integrable (fun x : ℝ ↦ K * x ^ (-2 : ℤ)) (volume.restrict (Set.Ioi S)) :=
      htailReal
    refine Integrable.mono' htailDom' hf_meas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hxS : S < x := hx
    have hxpos : 0 < x := lt_trans hSpos hxS
    have hR₀x : R₀ ≤ x := le_trans (le_max_right _ _) hxS.le
    have hbound :
        ‖f x‖ ≤ K / x ^ (2 : ℕ) := by
      simpa [f, Complex.norm_real, abs_of_pos hxpos] using
        hdecay (x : ℂ) (by simpa [Complex.norm_real, abs_of_pos hxpos] using hR₀x)
    have hxzpow :
        K / x ^ (2 : ℕ) = K * x ^ (-2 : ℤ) := by
      rw [div_eq_mul_inv, zpow_neg]
      rfl
    have hK_nonneg : 0 ≤ K := (lt_min_iff.mp hKR).1.le
    have htail_nonneg : 0 ≤ K * x ^ (-2 : ℤ) := by
      have hxpow_nonneg : 0 ≤ x ^ (-2 : ℤ) := zpow_nonneg hxpos.le (-2)
      positivity
    simpa [f, hxzpow, Complex.norm_real, abs_of_nonneg htail_nonneg]
      using hbound
  have hsplit :
      Set.Ioc (0 : ℝ) 1 ∪ (Set.Ioc (1 : ℝ) S ∪ Set.Ioi S) = Set.Ioi (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · rcases hx with hx | hx
        · exact lt_trans zero_lt_one hx.1
        · exact lt_trans hSpos hx
    · intro hx
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx, hx1⟩
      · have hxgt1 : 1 < x := lt_of_not_ge hx1
        by_cases hxS : x ≤ S
        · exact Or.inr (Or.inl ⟨hxgt1, hxS⟩)
        · exact Or.inr (Or.inr (lt_of_not_ge hxS))
  -- Split `(0, ∞)` into the bounded low interval, the bounded middle interval up to `S`, and the
  -- decaying tail beyond `S`.
  rw [← hsplit]
  exact hlow.union (hmid.union htail)

/-- Helper for Cartan section12 0012_Remark_III_6_extra_7: the symmetric truncations
`(1 / R)..R` of the positive-real rational kernel converge to the improper integral on `(0, ∞)`.
This isolates the real-variable convergence from the remaining contour normalization. -/
lemma rationalEval_intervalIntegral_tendsto_integral_Ioi
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦ ∫ x in (1 / R)..R, rationalEval P Q (x : ℂ))
      atTop
      (nhds (∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
  let f : ℝ → ℂ := fun x ↦ rationalEval P Q (x : ℂ)
  have hfi : IntegrableOn f (Set.Ioi (0 : ℝ)) volume :=
    rationalEval_integrableOn_Ioi P Q hdeg hcut'
  have hLower :
      Tendsto (fun R : ℝ ↦ 1 / R) atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_inv_atTop_zero
  let φ : ℝ → Set ℝ := fun R ↦ Set.Ioi (1 / R) ∩ Set.Iic R
  have hcover :
      MeasureTheory.AECover (volume.restrict <| Set.Ioi (0 : ℝ)) atTop φ :=
    (MeasureTheory.aecover_Ioi_of_Ioi
      (μ := volume) (l := atTop) (A := (0 : ℝ))
      (a := fun R : ℝ ↦ 1 / R) hLower).inter
      (MeasureTheory.aecover_Iic
        (μ := volume.restrict <| Set.Ioi (0 : ℝ))
        (l := atTop) (b := fun R : ℝ ↦ R) tendsto_id)
  have hlimit :
      Tendsto
        (fun R : ℝ ↦ ∫ x in φ R, f x ∂(volume.restrict <| Set.Ioi (0 : ℝ)))
        atTop
        (nhds (∫ x in Set.Ioi (0 : ℝ), f x ∂volume)) := by
    simpa [f] using
      (hcover.integral_tendsto_of_countably_generated
        (show Integrable f (volume.restrict <| Set.Ioi (0 : ℝ)) from hfi))
  have hevent :
      ∀ᶠ R : ℝ in atTop,
        (∫ x in φ R, f x ∂(volume.restrict <| Set.Ioi (0 : ℝ))) =
          ∫ x in (1 / R)..R, f x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with R hR
    have hRpos : 0 < R := lt_trans zero_lt_one hR
    have hsubset : Set.Ioc (1 / R) R ⊆ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact lt_trans (one_div_pos.mpr hRpos) hx.1
    have hle : 1 / R ≤ R := by
      field_simp [hRpos.ne']
      nlinarith
    have hinter :
        Set.Ioc (1 / R) R ∩ Set.Ioi (0 : ℝ) = Set.Ioc (1 / R) R := by
      ext x
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, hsubset hx⟩
    rw [show φ R = Set.Ioc (1 / R) R by rfl]
    rw [Measure.restrict_restrict measurableSet_Ioc, hinter]
    simpa [f] using (intervalIntegral.integral_of_le hle (f := f) (μ := volume)).symm
  -- The restricted-measure truncations already cover `(0, ∞)`, so the interval formulation
  -- inherits the same limit.
  exact Tendsto.congr' hevent hlimit
