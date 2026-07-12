import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2».LocalResidueExcision

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: the rational function whose real-axis integral is evaluated by
the keyhole contour argument. -/
abbrev rationalEval (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ P.eval z / Q.eval z

/-- Helper for Remark III.6-extra-7: the shifted-log integrand whose residues appear in the final
formula. -/
abbrev shiftedLogRationalEval (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ rationalEval P Q z * Complex.log (-z)

/-- Helper for Remark III.6-extra-7: the shifted slit-plane domain on which the branch
`z ↦ Complex.log (-z)` is holomorphic. -/
abbrev shiftedLogDomain : Set ℂ :=
  {z : ℂ | -z ∈ Complex.slitPlane}

/-- Helper for Remark III.6-extra-7: the meromorphic normal-form replacement of the rational
factor on the shifted slit domain, multiplied by the shifted logarithm branch. -/
abbrev shiftedLogRationalNormalForm (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z * Complex.log (-z)

/-- Helper for Remark III.6-extra-7: the source branch of `R(z) log z` on the positive-axis
keyhole. It is represented on `shiftedLogDomain` by `log (-z) + π i`, whose boundary values are
`log x` on the upper lip and `log x + 2π i` on the lower lip. -/
abbrev sourceLogRationalEval (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦ rationalEval P Q z * (Complex.log (-z) + Real.pi * Complex.I)

/-- Helper for Remark III.6-extra-7: the source-branch normal form for `R(z) log z`, obtained by
replacing only the rational factor by its meromorphic normal form on the source branch domain. -/
abbrev sourceLogRationalNormalForm (P Q : Polynomial ℂ) : ℂ → ℂ :=
  fun z ↦
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z *
      (Complex.log (-z) + Real.pi * Complex.I)

/-- Helper for Remark III.6-extra-7: the finite pole set hypothesis rewritten through the local
abbreviation `rationalEval`. -/
lemma rationalEval_pole_iff_mem
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles :
      ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s) :
    ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s := by
  -- This is only a notational repackaging of the pole data from the theorem statement.
  intro z
  simpa [rationalEval] using hpoles z

/-- Helper for Remark III.6-extra-7: the positive real axis is free of poles for the locally named
rational integrand. -/
lemma rationalEval_not_pole_of_nonneg_real
    (P Q : Polynomial ℂ)
    (hcut :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) (x : ℂ) < 0) :
    ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0 := by
  -- The no-pole-on-the-cut hypothesis is unchanged after introducing `rationalEval`.
  intro x hx
  simpa [rationalEval] using hcut x hx

/-- Helper for Remark III.6-extra-7: on the lower side of the shifted branch cut, `log (-z)`
approaches `log x - π i` at a positive real point `x`. -/
lemma tendsto_shiftedLog_boundary_from_below {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto Complex.log (nhdsWithin (-(x : ℂ)) {z : ℂ | z.im < 0})
      (nhds ((Real.log x : ℂ) - Real.pi * Complex.I)) := by
  -- This is the standard one-sided boundary value of `Complex.log` on the negative real axis.
  simpa [Complex.norm_real, abs_of_pos hx, sub_eq_add_neg] using
    (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (z := -(x : ℂ)) (by simpa using neg_lt_zero.mpr hx) (by simp))

/-- Helper for Remark III.6-extra-7: on the upper side of the shifted branch cut, `log (-z)`
approaches `log x + π i` at a positive real point `x`. -/
lemma tendsto_shiftedLog_boundary_from_above {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto Complex.log (nhdsWithin (-(x : ℂ)) {z : ℂ | 0 ≤ z.im})
      (nhds ((Real.log x : ℂ) + Real.pi * Complex.I)) := by
  -- This is the companion one-sided boundary value on the other side of the slit.
  simpa [Complex.norm_real, abs_of_pos hx] using
    (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := -(x : ℂ)) (by simpa using neg_lt_zero.mpr hx) (by simp))

/-- Helper for Remark III.6-extra-7: the shifted slit-plane domain is open because it is the
preimage of `Complex.slitPlane` under negation. -/
lemma isOpen_shiftedLogDomain :
    IsOpen shiftedLogDomain := by
  -- Rewrite the shifted branch domain as a preimage so the openness of `Complex.slitPlane`
  -- transfers directly.
  simpa [shiftedLogDomain] using Complex.isOpen_slitPlane.preimage continuous_neg

/-- Helper for Remark III.6-extra-7: every pole recorded by the finite pole set `s` already lies
in the shifted logarithm domain, because the no-pole-on-`[0, ∞)` hypothesis excludes poles on the
shifted branch cut. -/
lemma mem_shiftedLogDomain_of_mem_pole_finset
    {f : ℂ → ℂ} {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ↔ z ∈ s)
    (hcut : ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt f (x : ℂ) < 0)
    {z : ℂ} (hz : z ∈ s) :
    z ∈ shiftedLogDomain := by
  change -z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hz_im : z.im = 0
  · -- On the real axis, the cut hypothesis forces the pole to lie strictly on the negative side.
    have hz_not_nonneg : ¬ 0 ≤ z.re := by
      intro hz_re_nonneg
      have hpole : meromorphicOrderAt f z < 0 := (hpoles z).2 hz
      have hnot_pole : ¬ meromorphicOrderAt f ((z.re : ℂ)) < 0 := hcut z.re hz_re_nonneg
      have hz_eq : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [hz_im]
      have hpole_real : meromorphicOrderAt f ((z.re : ℂ)) < 0 := by
        rwa [hz_eq] at hpole
      exact hnot_pole hpole_real
    left
    simpa using neg_pos.mpr (lt_of_not_ge hz_not_nonneg)
  · -- Off the real axis, the shifted branch is already regular.
    right
    simpa using hz_im

/-- Helper for Remark III.6-extra-7: the whole pole finset lies in the shifted logarithm domain. -/
lemma pole_finset_subset_shiftedLogDomain
    {f : ℂ → ℂ} {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ↔ z ∈ s)
    (hcut : ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt f (x : ℂ) < 0) :
    (↑s : Set ℂ) ⊆ shiftedLogDomain := by
  intro z hz
  -- Apply the pointwise cut-avoidance lemma pole-by-pole.
  exact mem_shiftedLogDomain_of_mem_pole_finset hpoles hcut hz

/-- Helper for Remark III.6-extra-7: the rational function `P / Q` is meromorphic on the shifted
slit domain because polynomial evaluations are entire and meromorphicity is stable under
division. -/
lemma rationalEval_meromorphicOn_shiftedLogDomain
    (P Q : Polynomial ℂ) :
    MeromorphicOn (rationalEval P Q) shiftedLogDomain := by
  have hPmer_univ : MeromorphicOn (fun w : ℂ ↦ P.eval w) Set.univ := by
    -- Polynomial evaluation is entire, hence meromorphic, on the whole plane.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) P).meromorphicOn
  have hQmer_univ : MeromorphicOn (fun w : ℂ ↦ Q.eval w) Set.univ := by
    -- The same entire-function bridge applies to the denominator polynomial.
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) Q).meromorphicOn
  have hrat_univ : MeromorphicOn (rationalEval P Q) Set.univ := by
    -- Meromorphicity is stable under pointwise division.
    simpa [rationalEval] using hPmer_univ.div hQmer_univ
  -- Restrict the global meromorphic statement to the shifted slit domain.
  exact hrat_univ.mono_set (by intro z hz; simp)

/-- Helper for Remark III.6-extra-7: replacing the rational factor by its meromorphic normal form
does not change the local trailing coefficient of the shifted-log integrand at points of the
shifted slit domain. -/
lemma meromorphicTrailingCoeffAt_shiftedLogRationalNormalForm_eq
    (P Q : Polynomial ℂ) {z : ℂ} (hz : z ∈ shiftedLogDomain) :
    meromorphicTrailingCoeffAt (shiftedLogRationalNormalForm P Q) z =
      meromorphicTrailingCoeffAt (shiftedLogRationalEval P Q) z := by
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  apply meromorphicTrailingCoeffAt_congr_nhdsNE
  have hEqNF := hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  -- Multiplying by the same shifted logarithm preserves punctured-neighborhood equality.
  filter_upwards [hEqNF] with w hw
  rw [shiftedLogRationalNormalForm, shiftedLogRationalEval, hw]

/-- Helper for Remark III.6-extra-7: one isolated source-side local residue circle for the literal
shifted logarithmic integrand transfers unchanged to the shifted meromorphic normal form, because
the two integrands differ only on a codiscrete subset of the admissible circle. The isolation is
part of the input so the source residue really is the residue at the listed pole, not the integral
around a larger circle containing additional poles. -/
lemma shiftedLogRationalNormalForm_localResidueCircle_at
    (P Q : Polynomial ℂ) {s : Finset ℂ} {z residue_z : ℂ}
    (hres :
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
        (shiftedLogRationalEval P Q)
        z
        residue_z) :
    LocalResidueCircle
      shiftedLogDomain
      shiftedLogDomain
      (shiftedLogRationalNormalForm P Q)
      z
      residue_z := by
  let U : Set ℂ := shiftedLogDomain
  have hmeromorphic : MeromorphicOn (rationalEval P Q) U :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  rcases hres with ⟨R, hR, hRK, hRD, havoid, hdiff, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, ?_⟩
  let _ := havoid
  let _ := hdiff
  have hsphere_subset : Metric.sphere z |R| ⊆ U := by
    -- The owner closed ball from the source residue circle already contains the boundary sphere.
    intro w hw
    have hw_le : dist w z ≤ R := by
      have hw_eq : dist w z = |R| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      rw [abs_of_pos hR] at hw_eq
      exact le_of_eq hw_eq
    exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
  have hEq :
      shiftedLogRationalNormalForm P Q =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
        shiftedLogRationalEval P Q := by
    have hEqNF :
        (fun w ↦ toMeromorphicNFOn (rationalEval P Q) U w)
          =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
        rationalEval P Q := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono hsphere_subset)
    -- Multiply the codiscrete equality for the rational factor by the common shifted logarithm.
    filter_upwards [hEqNF] with w hw
    rw [shiftedLogRationalNormalForm, shiftedLogRationalEval, hw]
  -- The circle integral does not see codiscrete modifications of the integrand.
  calc
    (∮ w in C(z, R), shiftedLogRationalNormalForm P Q w) =
        ∮ w in C(z, R), shiftedLogRationalEval P Q w := by
          exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
    _ = (2 * Real.pi * Complex.I : ℂ) * residue_z := hcircleR

/-- Helper for Remark III.6-extra-7: the full finite family of isolated source-side local residue
circles transfers pointwise to the shifted meromorphic normal form. -/
lemma shiftedLogRationalNormalForm_localResidueCircle
    (P Q : Polynomial ℂ) {s : Finset ℂ} (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (shiftedLogRationalEval P Q)
          z
          (residue z)) :
    ∀ z ∈ s,
      LocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        (shiftedLogRationalNormalForm P Q)
        z
        (residue z) := by
  intro z hz
  -- Reduce the family statement to the pointwise codiscrete-transfer lemma.
  exact shiftedLogRationalNormalForm_localResidueCircle_at P Q (hresidue z hz)

/-- Helper for Remark III.6-extra-7: at any point of the shifted slit domain away from the pole
finset `s`, the shifted logarithmic meromorphic normal form is differentiable on the punctured
domain `shiftedLogDomain \ s`. This isolates the pointwise holomorphy input needed by the
isolated-residue transfer before the later global `DifferentiableOn` packaging. -/
lemma shiftedLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s)
    {z : ℂ} (hz : z ∈ shiftedLogDomain \ (↑s : Set ℂ)) :
    DifferentiableWithinAt ℂ
      (shiftedLogRationalNormalForm P Q)
      (shiftedLogDomain \ (↑s : Set ℂ))
      z := by
  let f : ℂ → ℂ := rationalEval P Q
  let _ := hQ
  have hmeromorphic : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- Outside the pole finset, the local meromorphic order cannot be negative.
    by_contra hneg
    exact hz.2 ((hpoles' z).1 (lt_of_not_ge hneg))
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f shiftedLogDomain) z := by
    -- Passing to normal form preserves the local meromorphic order on the domain.
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := shiftedLogDomain) hmeromorphic hz.1]
    exact horder_nonneg_f
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f shiftedLogDomain) z :=
    (meromorphicNFOn_toMeromorphicNFOn f shiftedLogDomain) hz.1
  have hnf_diff : DifferentiableAt ℂ (fun w ↦ toMeromorphicNFOn f shiftedLogDomain w) z := by
    -- The normal-form factor is analytic, hence differentiable, at every non-pole point.
    exact
      (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).differentiableAt
  have hlog_diff : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.log (-w)) z := by
    -- The shifted branch of the logarithm is holomorphic on `shiftedLogDomain`.
    simpa using (differentiableAt_id.neg.clog hz.1)
  -- Multiply the two holomorphic factors to recover the corrected integrand.
  simpa [shiftedLogRationalNormalForm, f] using
    (hnf_diff.mul hlog_diff).differentiableWithinAt

/-- Helper for Remark III.6-extra-7: one isolated source-side local residue circle for the literal
shifted logarithmic integrand stays isolated after replacing the rational factor by its
meromorphic normal form. The owner and separation data are unchanged; only the circle integral
uses the codiscrete normal-form comparison. -/
lemma shiftedLogRationalNormalForm_isolatedLocalResidueCircle_at
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ w : ℂ, meromorphicOrderAt (rationalEval P Q) w < 0 ↔ w ∈ s)
    {z residue_z : ℂ}
    (hres :
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
        (shiftedLogRationalEval P Q)
        z
        residue_z) :
    IsolatedLocalResidueCircle
      shiftedLogDomain
      shiftedLogDomain
      s
      (shiftedLogRationalNormalForm P Q)
      z
      residue_z := by
  let U : Set ℂ := shiftedLogDomain
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f U :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  rcases hres with ⟨R, hR, hRK, hRD, havoid, hdiff, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, havoid, ?_, ?_⟩
  · have hNFdiff :
        DifferentiableOn ℂ (shiftedLogRationalNormalForm P Q) (U \ (↑s : Set ℂ)) :=
      fun w hw ↦
        shiftedLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
          P Q hQ hpoles' hw
    -- Rebuild the punctured-ball holomorphy field by showing the source punctured ball avoids
    -- every pole in `s` except the center `z`, which has already been removed.
    refine hNFdiff.mono ?_
    intro w hw
    refine ⟨hRD ?_, ?_⟩
    · rw [Metric.mem_closedBall]
      exact le_of_lt <| by simpa [Metric.mem_ball] using hw.1
    · intro hwS
      have hwne : w ≠ z := by
        simpa using hw.2
      have hwBall : w ∈ Metric.closedBall z R := by
        rw [Metric.mem_closedBall]
        exact le_of_lt <| by simpa [Metric.mem_ball] using hw.1
      exact havoid w hwS hwne hwBall
  · have hsphere_subset : Metric.sphere z |R| ⊆ U := by
      -- The owner closed ball from the source residue circle already contains the boundary sphere.
      intro w hw
      have hw_le : dist w z ≤ R := by
        have hw_eq : dist w z = |R| := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hw
        rw [abs_of_pos hR] at hw_eq
        exact le_of_eq hw_eq
      exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
    have hEq :
        shiftedLogRationalNormalForm P Q =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
          shiftedLogRationalEval P Q := by
      have hEqNF :
          (fun w ↦ toMeromorphicNFOn f U w)
            =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
          f := by
        exact
          (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).symm.filter_mono
            (Filter.codiscreteWithin_mono hsphere_subset)
      -- Multiply the codiscrete equality for the rational factor by the common shifted logarithm.
      filter_upwards [hEqNF] with w hw
      rw [shiftedLogRationalNormalForm, shiftedLogRationalEval, hw]
    -- The same codiscrete comparison transfers the exact residue-circle integral.
    calc
      (∮ w in C(z, R), shiftedLogRationalNormalForm P Q w) =
          ∮ w in C(z, R), shiftedLogRationalEval P Q w := by
            exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
      _ = (2 * Real.pi * Complex.I : ℂ) * residue_z := hcircleR

/-- Helper for Remark III.6-extra-7: the full finite family of isolated source-side local residue
circles transfers pointwise to the shifted meromorphic normal form without changing the owner or
the finite singular set. -/
lemma shiftedLogRationalNormalForm_isolatedLocalResidueCircle
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ w : ℂ, meromorphicOrderAt (rationalEval P Q) w < 0 ↔ w ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (shiftedLogRationalEval P Q)
          z
          (residue z)) :
    ∀ z ∈ s,
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
        (shiftedLogRationalNormalForm P Q)
        z
        (residue z) := by
  intro z hz
  -- Reduce the family statement to the pointwise isolated transfer lemma with the global pole API.
  exact
    shiftedLogRationalNormalForm_isolatedLocalResidueCircle_at
      P Q hQ hpoles' (hresidue z hz)

/-- Helper for Remark III.6-extra-7: away from the denominator roots, the rational factor and the
shifted logarithm are both holomorphic on the shifted slit plane, hence so is their product. -/
lemma shiftedLogRationalEval_differentiableOn_shiftedLogDomain_off_roots
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    DifferentiableOn ℂ (shiftedLogRationalEval P Q)
      (shiftedLogDomain \ (↑(Q.roots.toFinset) : Set ℂ)) := by
  intro z hz
  -- Excluding denominator roots gives a genuine quotient-holomorphy statement for
  -- `P.eval / Q.eval`.
  have hQeval : Q.eval z ≠ 0 := by
    intro hzero
    exact hz.2 (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hzero))
  have hrat : DifferentiableAt ℂ (rationalEval P Q) z := by
    simpa [rationalEval] using (P.differentiableAt.div Q.differentiableAt hQeval)
  have hlog : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.log (-w)) z := by
    -- The shifted branch is just `Complex.log` composed with negation.
    simpa using (differentiableAt_id.neg.clog hz.1)
  exact (hrat.mul hlog).differentiableWithinAt

/-- Helper for Remark III.6-extra-7: removing the pole set `s` in addition to the denominator roots
only shrinks the holomorphy domain, so the shifted-log rational integrand remains differentiable on
that smaller set. -/
lemma shiftedLogRationalEval_differentiableOn_shiftedLogDomain_off_poles_and_roots
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (s : Finset ℂ) :
    DifferentiableOn ℂ (shiftedLogRationalEval P Q)
      (shiftedLogDomain \ (↑(s ∪ Q.roots.toFinset) : Set ℂ)) := by
  have hbase :
      DifferentiableOn ℂ (shiftedLogRationalEval P Q)
        (shiftedLogDomain \ (↑(Q.roots.toFinset) : Set ℂ)) :=
    shiftedLogRationalEval_differentiableOn_shiftedLogDomain_off_roots P Q hQ
  -- The residue theorem later works on the smaller excision set `s ∪ Q.roots.toFinset`.
  refine hbase.mono ?_
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro hzroot
  exact hz.2 (Finset.mem_union.mpr (Or.inr hzroot))

/-- Helper for Remark III.6-extra-7: after replacing the raw rational factor by its meromorphic
normal form on the shifted slit domain, the shifted-log integrand is holomorphic away from the
pole finset `s`. This is the source-faithful correction for removable denominator roots. -/
lemma shiftedLogRationalNF_differentiableOn_shiftedLogDomain_off_poles
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {s : Finset ℂ}
    (hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s) :
    DifferentiableOn ℂ
      (shiftedLogRationalNormalForm P Q)
      (shiftedLogDomain \ (↑s : Set ℂ)) := by
  intro z hz
  -- Package the earlier pointwise holomorphy bridge as the requested `DifferentiableOn` fact.
  exact
    shiftedLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
      P Q hQ hpoles' hz

/-- Helper for Remark III.6-extra-7: the degree-gap hypothesis already rules out the zero
denominator polynomial. -/
lemma denominator_ne_zero_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    Q ≠ 0 := by
  -- If `Q = 0`, then `Q.natDegree = 0`, contradicting `P.natDegree + 2 ≤ Q.natDegree`.
  intro hQ
  subst hQ
  simp at hdeg

/-- Helper for Remark III.6-extra-7: multiplying the denominator by `X^2` keeps it nonzero, which
is the algebraic input for the later asymptotic comparison. -/
lemma denominator_mul_X_sq_ne_zero_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    Q * Polynomial.X ^ 2 ≠ 0 := by
  -- The degree-gap step first produces `Q ≠ 0`; the polynomial `X^2` is nonzero as well.
  exact mul_ne_zero
    (denominator_ne_zero_of_degree_gap_two P Q hdeg)
    (pow_ne_zero 2 Polynomial.X_ne_zero)

/-- Helper for Remark III.6-extra-7: multiplying the numerator by `X^2` matches the source outer-
arc quantity `z^2 * (P(z) / Q(z))`, and the degree-gap hypothesis says that this corrected
numerator has degree at most the denominator degree. -/
lemma numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (P * Polynomial.X ^ 2).natDegree ≤ Q.natDegree := by
  by_cases hP : P = 0
  · -- If the numerator is zero, the corrected numerator is zero as well, so the bound is trivial.
    subst hP
    simp
  · -- Otherwise `natDegree_mul_X_pow` turns the claim into the given arithmetic degree gap.
    simpa [Polynomial.natDegree_mul_X_pow (n := 2) hP] using hdeg

/-- Helper for Remark III.6-extra-7: the corrected cobounded polynomial comparison is between
`(P * X^2).eval` and `Q.eval`, because this is the algebraic form of bounding `z^2 * R(z)` on the
outer circle. -/
lemma numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (fun z ↦ (P * Polynomial.X ^ 2).eval z) =O[cobounded ℂ] Q.eval := by
  by_cases hP : P = 0
  · -- The zero numerator is bounded by everything, so the Big-O statement is immediate.
    simpa [hP] using Asymptotics.isBigO_zero Q.eval (cobounded ℂ)
  · -- Convert the corrected nat-degree comparison into the degree inequality required by mathlib.
    have hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
    have hdeg' : (P * Polynomial.X ^ 2).degree ≤ Q.degree := by
      rw [Polynomial.degree_eq_natDegree (mul_ne_zero hP (pow_ne_zero 2 Polynomial.X_ne_zero)),
        Polynomial.degree_eq_natDegree hQ]
      exact_mod_cast numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two P Q hdeg
    simpa using
      (Polynomial.isBigO_cobounded_of_degree_le
        (P := P * Polynomial.X ^ 2) (Q := Q) hdeg')

/-- Helper for Remark III.6-extra-7: a bound of the form `‖a‖ ≤ K * ‖b‖` gives the corresponding
uniform estimate `‖a / b‖ ≤ K`. -/
lemma norm_div_le_of_norm_le_mul {a b : ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hab : ‖a‖ ≤ K * ‖b‖) :
    ‖a / b‖ ≤ K := by
  by_cases hb : b = 0
  · -- If the denominator vanishes, complex division is defined as `0`, so only `0 ≤ K` remains.
    subst hb
    simpa using hK
  · -- Otherwise divide the norm inequality by the positive scalar `‖b‖`.
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hb)).2 <| by simpa [mul_comm] using hab

/-- Helper for Remark III.6-extra-7: the corrected rational quantity `z^2 * R(z)` stays uniformly
bounded outside a sufficiently large disk when `deg Q ≥ deg P + 2`. -/
lemma rationalEval_mul_sq_eventually_bounded
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖(z ^ 2 : ℂ) * rationalEval P Q z‖ ≤ K := by
  obtain ⟨K, hKpos, hKbound⟩ :=
    Asymptotics.isBigO_iff'.mp
      (numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two P Q hdeg)
  have hbounded :
      ∀ᶠ z in cobounded ℂ, ‖(z ^ 2 : ℂ) * rationalEval P Q z‖ ≤ K := by
    -- Route correction: bound the source-faithful object `z^2 * R(z)` directly, rather than a
    -- later outer-arc specialization.
    filter_upwards [hKbound] with z hz
    have hquot :
        ‖((P * Polynomial.X ^ 2).eval z) / Q.eval z‖ ≤ K :=
      norm_div_le_of_norm_le_mul hKpos.le hz
    have hnorm :
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) ≤ K := by
      calc
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖)
            = ‖P.eval z‖ * ‖z‖ ^ (2 : ℕ) / ‖Q.eval z‖ := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring_nf
        _ ≤ K := by
              simpa [rationalEval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
                norm_div, norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using hquot
    calc
      ‖(z ^ 2 : ℂ) * rationalEval P Q z‖
          = ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) := by
              rw [rationalEval, norm_mul, norm_div, norm_pow]
      _ ≤ K := hnorm
  rcases Filter.hasBasis_cobounded_norm.eventually_iff.mp hbounded with ⟨R₀, -, hR₀⟩
  refine ⟨K, max R₀ 1, ?_, ?_⟩
  · -- Enlarge the eventual radius so the final decay estimate stays away from `0`.
    refine lt_min hKpos ?_
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro z hz
    -- Any point outside the larger radius still lies in the original eventual region.
    exact hR₀ <| by
      simpa using (le_trans (le_max_left _ _) hz)

/-- Helper for Remark III.6-extra-7: once `‖z‖` is bounded away from `0`, a bound on
`‖z^2 * R(z)‖` converts into the expected `‖R(z)‖ ≤ K / ‖z‖^2` decay. -/
lemma decay_of_mul_sq_bound {R K : ℝ} {z w : ℂ}
    (hR : 0 < R) (hz : R ≤ ‖z‖) (hbound : ‖(z ^ 2 : ℂ) * w‖ ≤ K) :
    ‖w‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR hz
  have hzsqpos : 0 < ‖z‖ ^ (2 : ℕ) := by
    exact pow_pos hzpos 2
  -- Rewrite the corrected norm as `‖w‖ * ‖z‖^2` and divide by the positive square norm.
  refine (le_div_iff₀ hzsqpos).2 ?_
  calc
    ‖w‖ * ‖z‖ ^ (2 : ℕ) = ‖(z ^ 2 : ℂ) * w‖ := by
      rw [norm_mul, norm_pow, mul_comm]
    _ ≤ K := hbound

/-- Helper for Remark III.6-extra-7: the degree-gap hypothesis gives the standard quadratic decay
estimate `‖R(z)‖ = O(‖z‖⁻²)` for the rational function `R(z) = P(z) / Q(z)`. -/
lemma rationalEval_decay_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖rationalEval P Q z‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  obtain ⟨K, R, hKR, hbounded⟩ := rationalEval_mul_sq_eventually_bounded P Q hdeg
  refine ⟨K, R, hKR, ?_⟩
  intro z hz
  have hR : 0 < R := (lt_min_iff.mp hKR).2
  -- First bound `z^2 * R(z)` uniformly, then divide by `‖z‖^2`.
  exact decay_of_mul_sq_bound hR hz (hbounded z hz)

/-- Helper for Remark III.6-extra-7: the degree gap is exactly the strict inequality needed to
compare `P` with `Q * X^2` in the cobounded polynomial asymptotics route. -/
lemma natDegree_lt_denominator_mul_X_sq_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    P.natDegree < (Q * Polynomial.X ^ 2).natDegree := by
  -- Rewrite the target degree through `natDegree_mul_X_pow` and discharge the arithmetic gap.
  have hQne : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  have hlt : P.natDegree < Q.natDegree + 2 := by
    omega
  simpa [Polynomial.natDegree_mul_X_pow (n := 2) hQne] using hlt
