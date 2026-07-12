import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».ShiftedLogResidueData
import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisRealIntegral
import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisResidueLocalization
import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisShiftedLogContour

open Filter MeasureTheory Bornology
open scoped BigOperators Topology unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: away from the pole finset, the source-faithful adjusted
branch normal form `R(z) * (log (-z) + π i)` is holomorphic on the shifted slit plane. -/
lemma sourceLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s)
    {z : ℂ} (hz : z ∈ shiftedLogDomain \ (↑s : Set ℂ)) :
    DifferentiableWithinAt ℂ
      (sourceLogRationalNormalForm P Q)
      (shiftedLogDomain \ (↑s : Set ℂ))
      z := by
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- Outside the pole finset, the rational factor cannot have negative meromorphic order.
    by_contra hneg
    exact hz.2 ((hpoles' z).1 (lt_of_not_ge hneg))
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f shiftedLogDomain) z := by
    -- Passing to meromorphic normal form preserves the local order on the domain.
    rw [meromorphicOrderAt_toMeromorphicNFOn hmeromorphic hz.1]
    exact horder_nonneg_f
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f shiftedLogDomain) z :=
    (meromorphicNFOn_toMeromorphicNFOn f shiftedLogDomain) hz.1
  have hnf_diff : DifferentiableAt ℂ (fun w ↦ toMeromorphicNFOn f shiftedLogDomain w) z := by
    -- The normal-form rational factor is analytic at every non-pole point.
    exact
      (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).differentiableAt
  have hlog_diff :
      DifferentiableAt ℂ (fun w : ℂ ↦ Complex.log (-w) + Real.pi * Complex.I) z := by
    -- The adjusted logarithm is just the shifted branch plus a constant.
    exact (differentiableAt_id.neg.clog hz.1).add_const (Real.pi * Complex.I)
  -- Multiply the holomorphic rational factor and adjusted logarithmic branch.
  simpa [sourceLogRationalNormalForm, f] using
    (hnf_diff.mul hlog_diff).differentiableWithinAt

/-- Helper for Remark III.6-extra-7: the source-branch normal form is holomorphic away from the
finite pole set, so it can be used in the large-keyhole residue theorem. -/
lemma sourceLogRationalNF_differentiableOn_shiftedLogDomain_off_poles
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s) :
    DifferentiableOn ℂ
      (sourceLogRationalNormalForm P Q)
      (shiftedLogDomain \ (↑s : Set ℂ)) := by
  intro z hz
  -- Package the pointwise holomorphy statement as the required `DifferentiableOn` field.
  exact
    sourceLogRationalNF_differentiableWithinAt_shiftedLogDomain_off_poles
      P Q hpoles' hz

/-- Helper for Remark III.6-extra-7: after replacing the rational quotient by its meromorphic
normal form on `shiftedLogDomain`, the bare rational factor is already holomorphic away from the
finite pole set. This isolates the non-logarithmic correction term used in the contour split. -/
lemma rationalNormalForm_differentiableOn_shiftedLogDomain_off_poles
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s) :
    DifferentiableOn ℂ
      (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain)
      (shiftedLogDomain \ (↑s : Set ℂ)) := by
  intro z hz
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- Off the actual pole finset, the rational kernel has nonnegative local order.
    exact le_of_not_gt fun hneg ↦ hz.2 ((hpoles' z).1 hneg)
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f shiftedLogDomain) z := by
    -- Passing to the normal form preserves local order on the shifted slit plane.
    rw [meromorphicOrderAt_toMeromorphicNFOn hmeromorphic hz.1]
    exact horder_nonneg_f
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f shiftedLogDomain) z :=
    (meromorphicNFOn_toMeromorphicNFOn f shiftedLogDomain) hz.1
  -- Nonnegative order at the normal-form representative upgrades to holomorphy.
  have hdiff : DifferentiableAt ℂ (toMeromorphicNFOn f shiftedLogDomain) z :=
    (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).differentiableAt
  exact hdiff.differentiableWithinAt

/-- Helper for Remark III.6-extra-7: the isolated local residue circles for the literal source
branch transfer unchanged to the source-branch meromorphic normal form. -/
lemma sourceLogRationalNormalForm_isolatedLocalResidueCircle
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles' : ∀ w : ℂ, meromorphicOrderAt (rationalEval P Q) w < 0 ↔ w ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (sourceLogRationalEval P Q)
          z
          (residue z)) :
    ∀ z ∈ s,
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
        (sourceLogRationalNormalForm P Q)
        z
        (residue z) := by
  let U : Set ℂ := shiftedLogDomain
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f U :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  intro z hz
  rcases hresidue z hz with ⟨R, hR, hRK, hRD, hsep, hdiff, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, hsep, ?_, ?_⟩
  · have hNFdiff :
        DifferentiableOn ℂ (sourceLogRationalNormalForm P Q) (U \ (↑s : Set ℂ)) :=
      sourceLogRationalNF_differentiableOn_shiftedLogDomain_off_poles P Q hpoles'
    -- The same punctured ball used for the source branch still avoids every other listed pole.
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
      exact hsep w hwS hwne hwBall
  · have hsphere_subset : Metric.sphere z |R| ⊆ U := by
      -- The source residue-circle owner already places the boundary sphere inside the domain.
      intro w hw
      have hw_le : dist w z ≤ R := by
        have hw_eq : dist w z = |R| := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hw
        rw [abs_of_pos hR] at hw_eq
        exact le_of_eq hw_eq
      exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
    have hEq :
        sourceLogRationalNormalForm P Q =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
          sourceLogRationalEval P Q := by
      have hEqNF :
          (fun w ↦ toMeromorphicNFOn f U w)
            =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
          f := by
        exact
          (toMeromorphicNFOn_eqOn_codiscrete hmeromorphic).symm.filter_mono
            (Filter.codiscreteWithin_mono hsphere_subset)
      -- Only the rational factor is normalized, so the codiscrete comparison is multiplicative.
      filter_upwards [hEqNF] with w hw
      rw [sourceLogRationalNormalForm, sourceLogRationalEval, hw]
    -- The circle integral is unchanged after replacing the rational factor by its normal form.
    calc
      (∮ w in C(z, R), sourceLogRationalNormalForm P Q w) =
          ∮ w in C(z, R), sourceLogRationalEval P Q w := by
            exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
      _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR

/-- Helper for Remark III.6-extra-7: the isolated local residue circles for the literal rational
kernel transfer unchanged to the shifted-domain meromorphic normal form. This is the correction-
term bridge needed when the bare rational contour is handled by exact residue data rather than by
trailing coefficients. -/
lemma rationalNormalForm_isolatedLocalResidueCircle
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles' : ∀ w : ℂ, meromorphicOrderAt (rationalEval P Q) w < 0 ↔ w ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (rationalEval P Q)
          z
          (residue z)) :
    ∀ z ∈ s,
      IsolatedLocalResidueCircle
        shiftedLogDomain
        shiftedLogDomain
        s
        (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain)
        z
        (residue z) := by
  let U : Set ℂ := shiftedLogDomain
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f U :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  intro z hz
  rcases hresidue z hz with ⟨R, hR, hRK, hRD, hsep, hdiff, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, hsep, ?_, ?_⟩
  · have hNFdiff :
        DifferentiableOn ℂ (toMeromorphicNFOn f U) (U \ (↑s : Set ℂ)) :=
      rationalNormalForm_differentiableOn_shiftedLogDomain_off_poles P Q hpoles'
    -- The same punctured ball still avoids the rest of the finite pole family, so the normal form
    -- is holomorphic there as well.
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
      exact hsep w hwS hwne hwBall
  · have hsphere_subset : Metric.sphere z |R| ⊆ U := by
      -- The original residue circle already lives inside the shifted slit domain.
      intro w hw
      have hw_le : dist w z ≤ R := by
        have hw_eq : dist w z = |R| := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hw
        rw [abs_of_pos hR] at hw_eq
        exact le_of_eq hw_eq
      exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
    have hEq :
        (fun w ↦ toMeromorphicNFOn f U w)
          =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)] f := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono hsphere_subset)
    -- The circle integral does not change after replacing the rational kernel by its normal form
    -- on the same pole-free residue circle.
    calc
      (∮ w in C(z, R), toMeromorphicNFOn f U w) =
          ∮ w in C(z, R), f w := by
            exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
      _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR

/-- Helper for Remark III.6-extra-7: the source branch differs from the shifted branch only by the
constant correction term `π i` times the meromorphic normal-form rational factor. This is the
owner-level algebraic split needed before any contour comparison can separate the source branch
from the shifted branch. -/
lemma sourceLogRationalNormalForm_eq_shiftedLogRationalNormalForm_add_piMul
    (P Q : Polynomial ℂ) (z : ℂ) :
    sourceLogRationalNormalForm P Q z =
      shiftedLogRationalNormalForm P Q z +
        (Real.pi * Complex.I : ℂ) *
          toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z := by
  let a : ℂ := toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z
  -- Expand the source branch once and distribute the common meromorphic normal-form factor.
  change a * (Complex.log (-z) + Real.pi * Complex.I) =
      a * Complex.log (-z) + (Real.pi * Complex.I) * a
  rw [mul_add, mul_comm a (Real.pi * Complex.I)]

/-- Helper for Remark III.6-extra-7: whenever the shifted branch and the bare meromorphic
normal-form correction are curve-integrable on the same path, the source branch integral splits as
their sum. This is the algebraic contour identity used before any asymptotic estimates. -/
lemma sourceLog_curveIntegral_eq_shiftedLog_add_piCorrection
    {a b : ℂ} (γ : Path a b) (P Q : Polynomial ℂ)
    (hshifted :
      CurveIntegrable (fun z ↦ ((shiftedLogRationalNormalForm P Q) dz) z) γ)
    (hcorrection :
      CurveIntegrable
        (fun z ↦
          ((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)
        γ) :
    ∫ᶜ z in γ, (((sourceLogRationalNormalForm P Q) dz) z) =
      ∫ᶜ z in γ, (((shiftedLogRationalNormalForm P Q) dz) z) +
        (Real.pi * Complex.I : ℂ) *
          ∫ᶜ z in γ,
            ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)) := by
  let c : ℂ := Real.pi * Complex.I
  have hsourceCoeff :
      sourceLogRationalNormalForm P Q =
        fun z ↦
          shiftedLogRationalNormalForm P Q z +
            c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z := by
    funext z
    -- Rewrite the source coefficient once before feeding it into curve-integral linearity.
    simpa [c] using sourceLogRationalNormalForm_eq_shiftedLogRationalNormalForm_add_piMul P Q z
  have hsumForm :
      (fun z ↦
        (((fun z ↦
            shiftedLogRationalNormalForm P Q z +
              c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z) dz) z)) =
        fun z ↦
          (((shiftedLogRationalNormalForm P Q) dz) z) +
            (((fun w ↦ c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain w) dz) z) := by
    funext z
    apply ContinuousLinearMap.ext
    intro w
    simp [Complex.scalarOneForm_apply, add_mul]
    ring
  have hcorrectionForm :
      (fun z ↦
        (((fun w ↦ c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain w) dz) z)) =
        fun z ↦ c • ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)) := by
    funext z
    apply ContinuousLinearMap.ext
    intro w
    simp [Complex.scalarOneForm_apply, mul_assoc, smul_eq_mul]
    ring
  have hcorrectionMul :
      CurveIntegrable
        (fun z ↦
          (((fun w ↦ c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain w) dz) z))
        γ := by
    have hsmul :
        CurveIntegrable
          (fun z ↦ c • ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)))
          γ := by
      -- Scalar-multiplying the correction kernel preserves curve integrability.
      exact CurveIntegrable.smul (c := c) hcorrection
    rw [← hcorrectionForm] at hsmul
    exact hsmul
  have hsource :
      CurveIntegrable (fun z ↦ ((sourceLogRationalNormalForm P Q) dz) z) γ := by
    -- The source branch inherits curve integrability from the shifted branch plus correction split.
    rw [hsourceCoeff]
    rw [hsumForm]
    exact hshifted.add hcorrectionMul
  -- Use the pointwise one-form split and then apply the standard curve-integral linearity rules.
  calc
    ∫ᶜ z in γ, (((sourceLogRationalNormalForm P Q) dz) z) =
        ∫ᶜ z in γ,
          ((((fun z ↦
              shiftedLogRationalNormalForm P Q z +
                c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z) dz) z)) := by
          rw [hsourceCoeff]
    _ =
        ∫ᶜ z in γ, (((shiftedLogRationalNormalForm P Q) dz) z) +
          ∫ᶜ z in γ,
            (((fun w ↦ c * toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain w) dz) z) := by
          rw [hsumForm]
          exact curveIntegral_fun_add hshifted hcorrectionMul
    _ =
        ∫ᶜ z in γ, (((shiftedLogRationalNormalForm P Q) dz) z) +
          c * ∫ᶜ z in γ,
            ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)) := by
          rw [hcorrectionForm, curveIntegral_fun_smul]
          simp [c, smul_eq_mul]
    _ =
        ∫ᶜ z in γ, (((shiftedLogRationalNormalForm P Q) dz) z) +
          (Real.pi * Complex.I : ℂ) *
            ∫ᶜ z in γ,
              ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)) := by
          simp [c, smul_eq_mul]

/-- Helper for Remark III.6-extra-7: the explicit `π i` correction contour produced by the
source-to-shifted branch split. -/
abbrev positiveAxisPiCorrectionContourTerm
    (P Q : Polynomial ℂ) (R : ℝ) : ℂ :=
  (Real.pi * Complex.I : ℂ) *
    ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
      ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z))

/-- Helper for Remark III.6-extra-7: the actual poles of `rationalEval P Q` form the expected
finite subfamily of denominator roots. This gives a concrete finite pole owner for the later
whole-contour continuity arguments. -/
private noncomputable def rationalEvalPoleFinset (P Q : Polynomial ℂ) : Finset ℂ :=
  let roots : Finset ℂ := Q.roots.toFinset
  roots.filter fun z ↦ meromorphicOrderAt (rationalEval P Q) z < 0

/-- Helper for Remark III.6-extra-7: every genuine pole of the rational kernel lies among the
denominator roots. This turns the abstract pole set into a usable finite finset. -/
private lemma rationalEval_pole_mem_denominator_roots
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) {z : ℂ}
    (hz : meromorphicOrderAt (rationalEval P Q) z < 0) :
    z ∈ Q.roots.toFinset := by
  by_contra hzRoot
  have hQz : Q.eval z ≠ 0 := by
    intro hQz
    exact hzRoot (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hQz))
  have hrat : AnalyticAt ℂ (rationalEval P Q) z := by
    -- Off the denominator roots, the rational quotient is an honest holomorphic function.
    have hPanalytic : AnalyticAt ℂ (fun w : ℂ ↦ P.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial P z (by simp))
    have hQanalytic : AnalyticAt ℂ (fun w : ℂ ↦ Q.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial Q z (by simp))
    simpa [rationalEval] using hPanalytic.div hQanalytic hQz
  exact (not_lt_of_ge hrat.meromorphicOrderAt_nonneg) hz

/-- Helper for Remark III.6-extra-7: membership in the canonical pole finset is equivalent to
negative meromorphic order. This is the reusable bridge from local pole facts to the chosen
finite set. -/
private lemma rationalEval_pole_iff_mem_poleFinset
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ rationalEvalPoleFinset P Q := by
  intro z
  constructor
  · intro hz
    -- Record the pole in the filtered denominator-root finset.
    exact Finset.mem_filter.2 ⟨rationalEval_pole_mem_denominator_roots P Q hQ hz, hz⟩
  · intro hz
    -- The filter keeps exactly the negative-order points.
    exact (Finset.mem_filter.1 hz).2

/-- Helper for Remark III.6-extra-7: the canonical pole finset lies in the shifted logarithm
domain because the nonnegative real axis is pole-free. This lets the slit-domain geometry absorb
the pole data. -/
private lemma rationalEvalPoleFinset_subset_shiftedLogDomain
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    (↑(rationalEvalPoleFinset P Q) : Set ℂ) ⊆ shiftedLogDomain := by
  -- Reuse the general pole-on-the-cut exclusion once the pole finset is fixed.
  simpa [rationalEvalPoleFinset] using
    pole_finset_subset_shiftedLogDomain
      (rationalEval_pole_iff_mem_poleFinset P Q hQ) hcut'

/-- Helper for Remark III.6-extra-7: every actual pole of the rational kernel eventually lies
strictly inside the large positive-axis slit annulus. This is the frontier-avoidance package
needed before certifying contour integrability on the whole keyhole. -/
private lemma eventually_rationalEvalPoleFinset_subset_interior_positiveAxisWedgeAnnulus
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∀ᶠ R : ℝ in atTop,
      let ε := 1 / R
      1 < R ∧
        ∀ z ∈ rationalEvalPoleFinset P Q,
          z ∈ interior (positiveAxisWedgeAnnulus R ε) := by
  classical
  let s : Finset ℂ := rationalEvalPoleFinset P Q
  let hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  have hsDomain :
      (↑s : Set ℂ) ⊆ shiftedLogDomain :=
    rationalEvalPoleFinset_subset_shiftedLogDomain P Q hQ hcut'
  let radius : ℂ → ℝ := fun z ↦
    if hz : z ∈ s then
      let data := Metric.mem_nhds_iff.1 (isOpen_shiftedLogDomain.mem_nhds (hsDomain hz))
      data.choose / 2
    else 1
  have hradius_pos : ∀ z ∈ s, 0 < radius z := by
    intro z hz
    dsimp [radius]
    simp [hz]
    let data := Metric.mem_nhds_iff.1 (isOpen_shiftedLogDomain.mem_nhds (hsDomain hz))
    have hdata : 0 < data.choose := data.choose_spec.1
    linarith
  have hradius_D : ∀ z ∈ s, Metric.closedBall z (radius z) ⊆ shiftedLogDomain := by
    intro z hz
    dsimp [radius]
    simp [hz]
    let data := Metric.mem_nhds_iff.1 (isOpen_shiftedLogDomain.mem_nhds (hsDomain hz))
    have hdata : 0 < data.choose := data.choose_spec.1
    exact (Metric.closedBall_subset_ball (by linarith)).trans data.choose_spec.2
  have hEventuallyInterior :
      ∀ᶠ R : ℝ in atTop,
        ∀ z ∈ s,
          Metric.closedBall z (radius z) ⊆ interior (positiveAxisWedgeAnnulus R (1 / R)) := by
    rw [Filter.eventually_all_finset]
    intro z hz
    filter_upwards
      [eventually_closedBall_subset_interior_positiveAxisWedgeAnnulus
        z (hradius_pos z hz) (hradius_D z hz)]
      with R hR
    exact hR.2
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hEventuallyInterior] with R hRgt1 hInterior
  refine ⟨hRgt1, ?_⟩
  intro z hz
  exact hInterior z hz (Metric.mem_closedBall_self (hradius_pos z hz).le)

/-- Helper for Remark III.6-extra-7: once the keyhole boundary is far enough from every pole, the
source contour integral is exactly the shifted contour integral plus the explicit `π i`
correction contour. This is the only source-to-shifted bridge needed in the final limit
assembly. -/
lemma eventually_sourceLogKeyhole_curveIntegral_eq_shiftedLog_add_piCorrection
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∀ᶠ R : ℝ in atTop,
      ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((sourceLogRationalNormalForm P Q) dz) z) =
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((shiftedLogRationalNormalForm P Q) dz) z) +
        positiveAxisPiCorrectionContourTerm P Q R := by
  -- Route correction: use the branch-splitting identity directly on the whole keyhole, rather
  -- than inventing another source-only contour normalization.
  let s : Finset ℂ := rationalEvalPoleFinset P Q
  let hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  have hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s :=
    rationalEval_pole_iff_mem_poleFinset P Q hQ
  have hshiftedCont :
      ContinuousOn (shiftedLogRationalNormalForm P Q) (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- Away from the pole finset, the shifted normal form is holomorphic and hence continuous.
    exact
      (shiftedLogRationalNF_differentiableOn_shiftedLogDomain_off_poles P Q hQ hpoles').continuousOn
  have hcorrectionCont :
      ContinuousOn (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain)
        (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- The bare meromorphic normal form enjoys the same continuity away from the actual poles.
    exact
      (rationalNormalForm_differentiableOn_shiftedLogDomain_off_poles P Q hpoles').continuousOn
  have hshiftedFormCont :
      ContinuousOn (fun z ↦ ((shiftedLogRationalNormalForm P Q) dz) z)
        (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- Turn continuity of the scalar coefficient into continuity of the associated scalar `1`-form.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ))).prodMk hshiftedCont)
  have hcorrectionFormCont :
      ContinuousOn
        (fun z ↦ (((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z))
        (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- The same scalar-one-form conversion applies to the correction kernel.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ))).prodMk hcorrectionCont)
  filter_upwards
      [eventually_rationalEvalPoleFinset_subset_interior_positiveAxisWedgeAnnulus P Q hdeg hcut']
      with R hR
  rcases hR with ⟨hRgt1, hInterior⟩
  let ε : ℝ := 1 / R
  have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
  have hε : 0 < ε := by
    dsimp [ε]
    exact one_div_pos.mpr hRpos
  have hεR : ε < R := by
    dsimp [ε]
    exact (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
  have hfrontier :
      frontier (positiveAxisWedgeAnnulus R ε) = Set.range (positiveAxisKeyhole R ε) :=
    positiveAxisWedgeAnnulus_frontier_eq_range R ε hε hεR
  have hpathRange :
      Set.range (positiveAxisKeyhole R ε) ⊆ shiftedLogDomain \ (↑s : Set ℂ) := by
    intro z hz
    have hzFrontier : z ∈ frontier (positiveAxisWedgeAnnulus R ε) := by
      simpa [hfrontier] using hz
    have hzClosure : z ∈ closure (positiveAxisWedgeAnnulus R ε) :=
      frontier_subset_closure hzFrontier
    have hzWedge : z ∈ positiveAxisWedgeAnnulus R ε := by
      simpa [isClosed_positiveAxisWedgeAnnulus R ε |>.closure_eq] using hzClosure
    have hzNotPole : z ∉ (↑s : Set ℂ) := by
      intro hzPole
      have hzInterior : z ∈ interior (positiveAxisWedgeAnnulus R ε) := hInterior z hzPole
      have hzFrontier' := hzFrontier
      change z ∈ closure (positiveAxisWedgeAnnulus R ε) \ interior (positiveAxisWedgeAnnulus R ε)
        at hzFrontier'
      exact hzFrontier'.2 hzInterior
    exact ⟨positiveAxisWedgeAnnulus_subset_shiftedLogDomain hε hεR hzWedge, hzNotPole⟩
  let γ := (positiveAxisKeyhole R ε).toClosedPath.toPath
  have hγPiecewise : γ.IsPiecewiseDifferentiable := by
    -- The repaired keyhole path inherits the explicit piecewise differentiability package.
    simpa [γ, Path.toClosedPath] using positiveAxisKeyhole_isPiecewiseDifferentiable R ε
  have hγRange :
      Set.range γ ⊆ shiftedLogDomain \ (↑s : Set ℂ) := by
    simpa [γ, Path.toClosedPath] using hpathRange
  have hshifted :
      CurveIntegrable (fun z ↦ ((shiftedLogRationalNormalForm P Q) dz) z) γ := by
    -- Continuity on the pole-free frontier is enough for whole-keyhole curve integrability.
    have hshiftedReal :
        CurveIntegrable
          (Complex.realScalarOneForm (shiftedLogRationalNormalForm P Q))
          γ := by
      have hshiftedRealCont :
          ContinuousOn
            (Complex.realScalarOneForm (shiftedLogRationalNormalForm P Q))
            (shiftedLogDomain \ (↑s : Set ℂ)) := by
        rw [show Complex.realScalarOneForm (shiftedLogRationalNormalForm P Q) =
            fun z ↦ shiftedLogRationalNormalForm P Q z • (1 : ℂ →L[ℝ] ℂ) by
              funext z
              exact Complex.realScalarOneForm_eq_smul (shiftedLogRationalNormalForm P Q) z]
        exact hshiftedCont.smul
          (continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ)))
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hshiftedRealCont hγPiecewise hγRange
    simpa [Complex.realScalarOneForm] using hshiftedReal
  have hcorrection :
      CurveIntegrable
        (fun z ↦ (((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z))
        γ := by
    -- The same frontier argument certifies the bare correction form on the whole contour.
    have hcorrectionReal :
        CurveIntegrable
          (Complex.realScalarOneForm
            (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain))
          γ := by
      have hcorrectionRealCont :
          ContinuousOn
            (Complex.realScalarOneForm
              (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain))
            (shiftedLogDomain \ (↑s : Set ℂ)) := by
        rw [show Complex.realScalarOneForm
            (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) =
              fun z ↦
                toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z •
                  (1 : ℂ →L[ℝ] ℂ) by
              funext z
              exact
                Complex.realScalarOneForm_eq_smul
                  (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) z]
        exact hcorrectionCont.smul
          (continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ)))
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hcorrectionRealCont hγPiecewise hγRange
    simpa [Complex.realScalarOneForm] using hcorrectionReal
  -- Apply the already-proved source/shifted branch split once both contour integrability facts
  -- are available on the whole keyhole.
  simpa [γ, ε, positiveAxisPiCorrectionContourTerm] using
    sourceLog_curveIntegral_eq_shiftedLog_add_piCorrection γ P Q hshifted hcorrection

/-- Helper for Remark III.6-extra-7: the complementary keyhole angle
`π - positiveAxisKeyholeAngle R (1 / R)` tends to `π` as `R → ∞`. This is the common angle
normalization used when both slit-lip limits are rewritten as interval kernels. -/
lemma positiveAxisKeyholeComplementaryAngle_tendsto_pi :
    Tendsto
      (fun R : ℝ ↦ Real.pi - positiveAxisKeyholeAngle R (1 / R))
      atTop
      (nhds Real.pi) := by
  have hInv :
      Tendsto (fun R : ℝ ↦ R⁻¹) atTop (nhds (0 : ℝ)) := by
    -- The reciprocal radius shrinks to `0` along the large-keyhole limit.
    simpa using tendsto_inv_atTop_zero
  have hArg :
      Tendsto (fun R : ℝ ↦ ((1 / R) / R : ℝ)) atTop (nhds (0 : ℝ)) := by
    -- The keyhole opening angle is `arctan ((1 / R) / R)`, so its argument is quadratic in
    -- `R⁻¹` and therefore also tends to `0`.
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hInv.mul hInv
  have hAngle :
      Tendsto (fun R : ℝ ↦ positiveAxisKeyholeAngle R (1 / R)) atTop (nhds (0 : ℝ)) := by
    -- After unfolding the angle once, continuity of `arctan` finishes the normalization.
    have harctan :
        Tendsto (fun x : ℝ ↦ Real.arctan x) (nhds (0 : ℝ)) (nhds (Real.arctan 0)) :=
      Real.continuousAt_arctan.tendsto
    simpa [positiveAxisKeyholeAngle] using
      harctan.comp hArg
  -- Subtracting an angle that tends to `0` sends the complementary angle to `π`.
  simpa using Filter.Tendsto.const_sub Real.pi hAngle

/-- Helper for Remark III.6-extra-7: the repaired major-arc angular length is always bounded by
`2π`. This is the uniform geometric bound used in both circular-arc decay estimates. -/
lemma positiveAxisKeyhole_majorArc_angleLength_le_two_pi
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    |positiveAxisKeyholeLowerAngle R ε - positiveAxisKeyholeUpperAngle R ε| ≤ 2 * Real.pi := by
  have hθnonneg : 0 ≤ positiveAxisKeyholeAngle R ε :=
    (positiveAxisKeyhole_angle_bounds hε hεR).1.le
  rw [abs_of_nonneg (sub_nonneg.mpr (positiveAxisKeyhole_majorArc_angle_order hε hεR).1.le)]
  -- The repaired major arc runs from `θ` to `2π - θ`, so its angular length is `2π - 2θ`.
  dsimp [positiveAxisKeyholeLowerAngle, positiveAxisKeyholeUpperAngle]
  linarith [Real.pi_pos, hθnonneg]

/-- Helper for Remark III.6-extra-7: on `shiftedLogDomain`, the shifted and global meromorphic
normal forms of `rationalEval P Q` are the same local normal-form germ. This is the stable bridge
used when the slit-side kernel is transported to the global positive-axis normal form. -/
lemma rationalEval_shiftedNormalForm_eq_univNormalForm
    (P Q : Polynomial ℂ) {z : ℂ} (hz : z ∈ shiftedLogDomain) :
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z =
      toMeromorphicNFOn (rationalEval P Q) Set.univ z := by
  let f : ℂ → ℂ := rationalEval P Q
  have hshifted : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  have huniv : MeromorphicOn f Set.univ :=
    rationalEval_meromorphicOn_univ P Q
  -- Both normal forms are the same `toMeromorphicNFAt` germ once the point lies in
  -- `shiftedLogDomain`.
  calc
    toMeromorphicNFOn f shiftedLogDomain z = toMeromorphicNFAt f z z := by
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hshifted hz]
    _ = toMeromorphicNFOn f Set.univ z := by
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt huniv (by simp)]

/-- Helper for Remark III.6-extra-7: away from the denominator roots, the shifted-domain
meromorphic normal form agrees pointwise with the literal rational quotient. This is the exact
comparison used on the keyhole arcs once the radius is separated from the finite root set. -/
lemma rationalEval_shiftedNormalForm_eq_of_denominator_ne_zero
    (P Q : Polynomial ℂ) {z : ℂ} (hz : z ∈ shiftedLogDomain) (hQz : Q.eval z ≠ 0) :
    toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z = rationalEval P Q z := by
  let f : ℂ → ℂ := rationalEval P Q
  have hmeromorphic : MeromorphicOn f shiftedLogDomain :=
    rationalEval_meromorphicOn_shiftedLogDomain P Q
  have hrat : AnalyticAt ℂ f z := by
    -- Off the denominator roots, the rational quotient is an honest holomorphic function.
    have hPanalytic : AnalyticAt ℂ (fun w : ℂ ↦ P.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial P z (by simp))
    have hQanalytic : AnalyticAt ℂ (fun w : ℂ ↦ Q.eval w) z := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial Q z (by simp))
    simpa [f, rationalEval] using hPanalytic.div hQanalytic hQz
  calc
    toMeromorphicNFOn f shiftedLogDomain z = toMeromorphicNFAt f z z := by
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmeromorphic hz]
    _ = f z := by
      exact congrFun (toMeromorphicNFAt_eq_self.2 hrat.meromorphicNFAt) z

/-- Helper for Remark III.6-extra-7: every denominator root is contained in a fixed closed ball,
so sufficiently large circles avoid all denominator zeros. -/
lemma exists_large_radius_denominator_ne_zero
    (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ R > 0, ∀ z : ℂ, R ≤ ‖z‖ → Q.eval z ≠ 0 := by
  -- The finite root set is bounded, so one radius eventually dominates the norm of every root.
  obtain ⟨R, hRpos, hRbound⟩ :=
    (Q.roots.toFinset.finite_toSet.isBounded.exists_pos_norm_lt :
      ∃ R > 0, ∀ z ∈ (Q.roots.toFinset : Set ℂ), ‖z‖ < R)
  refine ⟨R, hRpos, ?_⟩
  intro z hz hQz
  have hzroot : z ∈ (Q.roots.toFinset : Set ℂ) := by
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hQz)
  -- A point outside the bounding ball cannot be one of the denominator roots.
  exact (not_lt_of_ge hz) (hRbound z hzroot)

/-- Helper for Remark III.6-extra-7: after discarding the origin itself, sufficiently small
circles avoid all denominator roots. This is the local punctured-neighborhood separation used
before comparing the shifted and global meromorphic normal forms near `0`. -/
lemma exists_small_radius_denominator_ne_zero
    (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ δ > 0, ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → Q.eval z ≠ 0 := by
  let bad : Set ℂ := (Q.roots.toFinset : Set ℂ) \ ({0} : Set ℂ)
  have hbadFinite : bad.Finite :=
    Q.roots.toFinset.finite_toSet.subset fun _ hz ↦ hz.1
  have hbadClosed : IsClosed bad := hbadFinite.isClosed
  have h0not : (0 : ℂ) ∉ bad := by
    simp [bad]
  have hnhds : badᶜ ∈ nhds (0 : ℂ) :=
    IsClosed.compl_mem_nhds hbadClosed h0not
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hδball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro z hz0 hzδ hQz
  have hzball : z ∈ Metric.ball 0 δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzδ
  have hznotbad : z ∉ bad := hδball hzball
  have hzroot : z ∈ (Q.roots.toFinset : Set ℂ) := by
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hQz)
  have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz0)
  -- Any sufficiently small nonzero root would lie in the forbidden finite set `bad`.
  exact hznotbad ⟨hzroot, by simpa [hz_ne]⟩

/-- Helper for Remark III.6-extra-7: the shifted-domain meromorphic normal form stays uniformly
bounded on a sufficiently small punctured neighborhood of `0`. The proof compares it with the
global meromorphic normal form, which is continuous at `0` because `0` is not a pole. -/
lemma exists_small_radius_bound_shiftedNormalForm
    (P Q : Polynomial ℂ)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧
      ∀ z : ℂ, z ∈ shiftedLogDomain → 0 < ‖z‖ → ‖z‖ < δ →
        ‖toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z‖ ≤ M := by
  by_cases hQ : Q = 0
  · subst hQ
    refine ⟨1, 0, zero_lt_one, le_rfl, ?_⟩
    intro z hz hz0 hzδ
    -- If the denominator polynomial is zero, the literal rational kernel is identically zero.
    have hzero : rationalEval P 0 = fun _ : ℂ ↦ 0 := by
      funext w
      simp [rationalEval]
    rw [hzero]
    have hmer : MeromorphicOn (fun _ : ℂ ↦ (0 : ℂ)) shiftedLogDomain := by
      intro w hw
      exact analyticAt_const.meromorphicAt
    have hself :
        toMeromorphicNFAt (fun _ : ℂ ↦ (0 : ℂ)) z z = 0 := by
      have hNF : MeromorphicNFAt (fun _ : ℂ ↦ (0 : ℂ)) z :=
        analyticAt_const.meromorphicNFAt
      simpa using congrFun ((toMeromorphicNFAt_eq_self).2 hNF) z
    by_cases hzU : z ∈ shiftedLogDomain
    · simp [toMeromorphicNFOn, hmer, hzU, hself]
    · simp [toMeromorphicNFOn, hmer, hzU]
  · let g : ℂ → ℂ := toMeromorphicNFOn (rationalEval P Q) Set.univ
    have hcont0 : ContinuousAt g 0 := by
      -- The global normal form is holomorphic at `0` because the positive axis is pole-free.
      exact
        (rationalEval_univNormalForm_differentiableAt_of_not_pole
          P Q (z := 0) (hcut' 0 le_rfl)).continuousAt
    have hnear : {z : ℂ | ‖g z - g 0‖ < 1} ∈ nhds (0 : ℂ) := by
      -- Continuity gives a neighborhood on which the global normal form stays within distance `1`
      -- of its value at the origin.
      simpa [Metric.mem_ball, dist_eq_norm] using
        hcont0.tendsto.eventually (Metric.ball_mem_nhds (g 0) zero_lt_one)
    rcases Metric.mem_nhds_iff.mp hnear with ⟨δ₀, hδ₀, hδ₀ball⟩
    obtain ⟨δ₁, hδ₁, hsep⟩ := exists_small_radius_denominator_ne_zero Q hQ
    let δ : ℝ := min δ₀ δ₁
    let M : ℝ := ‖g 0‖ + 1
    refine ⟨δ, M, by simpa [δ] using lt_min hδ₀ hδ₁, by positivity, ?_⟩
    intro z hz hz0 hzδ
    have hzδ₀ : ‖z‖ < δ₀ := lt_of_lt_of_le hzδ (min_le_left _ _)
    have hzδ₁ : ‖z‖ < δ₁ := lt_of_lt_of_le hzδ (min_le_right _ _)
    have hzball : z ∈ Metric.ball 0 δ₀ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzδ₀
    have hQz : Q.eval z ≠ 0 := hsep z hz0 hzδ₁
    have hshiftedEq :
        toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z = rationalEval P Q z :=
      rationalEval_shiftedNormalForm_eq_of_denominator_ne_zero P Q hz hQz
    have hunivEq : g z = rationalEval P Q z :=
      rationalEval_univNormalForm_eq_of_denominator_ne_zero P Q hQz
    have hclose : ‖g z - g 0‖ < 1 := hδ₀ball hzball
    have hgBound : ‖g z‖ ≤ M := by
      have hsum : g z = (g z - g 0) + g 0 := by
        ring
      rw [hsum]
      have hlt : ‖g z - g 0‖ + ‖g 0‖ < M := by
        simpa [M, add_comm, add_left_comm, add_assoc] using add_lt_add_right hclose ‖g 0‖
      exact le_trans (norm_add_le _ _) hlt.le
    -- Away from the denominator roots, both normal-form representatives agree with the literal
    -- quotient, so the global bound transfers directly to the shifted normal form.
    calc
      ‖toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain z‖ = ‖g z‖ := by
        rw [hshiftedEq, hunivEq]
      _ ≤ M := hgBound

/-- Helper for Remark III.6-extra-7: on a keyhole arc point, the shifted logarithm is controlled
by the real logarithm of the radius plus the universal angular bound `π`. -/
lemma norm_shiftedLog_on_keyhole_arc_le
    {ρ θ : ℝ} (hρ : 0 < ρ) (hθ₀ : 0 < θ) (hθ₂π : θ < 2 * Real.pi) :
    ‖Complex.log (-circleMap 0 ρ θ)‖ ≤ |Real.log ρ| + Real.pi := by
  -- Bound the complex norm by the sum of the absolute values of the real and imaginary parts.
  calc
    ‖Complex.log (-circleMap 0 ρ θ)‖ ≤
        |(Complex.log (-circleMap 0 ρ θ)).re| + |(Complex.log (-circleMap 0 ρ θ)).im| := by
          exact Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖-circleMap 0 ρ θ‖| + |(-circleMap 0 ρ θ).arg| := by
          rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log ‖-circleMap 0 ρ θ‖| + Real.pi := by
          gcongr
          exact Complex.abs_arg_le_pi _
    _ = |Real.log ρ| + Real.pi := by
          simp [norm_circleMap_zero, abs_of_pos hρ]

/-- Helper for Remark III.6-extra-7: every circle point on the repaired major arc of the positive-
axis keyhole lies in the shifted slit domain. This is the geometric bridge needed before the
small- and large-radius normal-form estimates can be applied on the circular branches. -/
lemma circleMap_mem_shiftedLogDomain_of_keyholeMajorArc
    {R ε ρ φ : ℝ} (hε : 0 < ε) (hεR : ε < R) (hρlo : ε ≤ ρ) (hρhi : ρ ≤ R)
    (hφ :
      φ ∈ Set.Icc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε)) :
    circleMap 0 ρ φ ∈ shiftedLogDomain := by
  have hρ : 0 < ρ := lt_of_lt_of_le hε hρlo
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  have hupperPos : 0 < positiveAxisKeyholeUpperAngle R ε := by
    simpa [positiveAxisKeyholeUpperAngle] using (positiveAxisKeyhole_angle_bounds hε hεR).1
  have hφ02π : φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    refine ⟨le_of_lt (lt_of_lt_of_le hupperPos hφ.1), le_of_lt (lt_of_le_of_lt hφ.2 horder.2)⟩
  have hmajor :
      φ ∈ Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
    simpa [Set.uIcc_of_le horder.1.le] using hφ
  have hnotWedge : circleMap 0 ρ φ ∉ positiveAxisWedge R ε := by
    exact
      (positiveAxisWedge_circleMap_not_mem_iff_majorArc R ε ρ hε hεR hρ hφ02π).2 hmajor
  have hmemAnnulus : circleMap 0 ρ φ ∈ positiveAxisWedgeAnnulus R ε := by
    refine ⟨?_, hnotWedge⟩
    simpa [norm_circleMap_zero, abs_of_pos hρ] using And.intro hρlo hρhi
  -- Move the geometric major-arc membership into the slit-domain owner used by the normal form.
  exact positiveAxisWedgeAnnulus_subset_shiftedLogDomain hε hεR hmemAnnulus

/-- Helper for Remark III.6-extra-7: a uniform bound on `‖z * f z‖` along a circular arc bounds
the norm of the corresponding `sectorArcIntegral` by that bound times the angular length. -/
lemma sectorArcIntegral_norm_le_of_circleMap_mul_bound
    (f : ℂ → ℂ) (r θ₁ θ₂ C : ℝ)
    (hC :
      ∀ θ ∈ Set.uIcc θ₁ θ₂, ‖circleMap 0 r θ * f (circleMap 0 r θ)‖ ≤ C) :
    ‖sectorArcIntegral f r θ₁ θ₂‖ ≤ C * |θ₂ - θ₁| := by
  -- Rewrite the arc integral into its textbook `I * z * f z` form and apply the standard norm
  -- estimate over the interval parameter.
  rw [sectorArcIntegral_def]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθmem ↦ ?_
  calc
    ‖Complex.I * circleMap 0 r θ * f (circleMap 0 r θ)‖
        = ‖circleMap 0 r θ * f (circleMap 0 r θ)‖ := by
          simp only [norm_mul, Complex.norm_I, one_mul]
    _ ≤ C := hC θ (Set.uIoc_subset_uIcc hθmem)

/-- Helper for Remark III.6-extra-7: every constant divided by `R` tends to `0` as
`R → +∞`. -/
lemma tendsto_const_div_atTop_zero (c : ℝ) :
    Tendsto (fun R : ℝ ↦ c / R) atTop (nhds 0) := by
  -- This is the standard inverse-decay limit, recorded here in the exact `c / R` shape used by
  -- the arc estimates.
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    Filter.Tendsto.const_mul c tendsto_inv_atTop_zero

/-- Helper for Remark III.6-extra-7: `(log R + c) / R` still tends to `0` as `R → +∞`. -/
lemma tendsto_log_add_const_div_atTop_zero (c : ℝ) :
    Tendsto (fun R : ℝ ↦ (Real.log R + c) / R) atTop (nhds 0) := by
  have hlog :
      Tendsto (fun R : ℝ ↦ Real.log R / R) atTop (nhds 0) := by
    -- Mathlib already packages the basic `log R / R → 0` asymptotic.
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hconst :
      Tendsto (fun R : ℝ ↦ c / R) atTop (nhds 0) :=
    tendsto_const_div_atTop_zero c
  have hsplit :
      (fun R : ℝ ↦ (Real.log R + c) / R) =
        fun R ↦ Real.log R / R + c / R := by
    funext R
    ring
  -- Split the numerator into its logarithmic and constant pieces and add the two vanishing limits.
  simpa [hsplit] using hlog.add hconst

/-- Helper for Remark III.6-extra-7: the inner-arc logarithmic factor
`(|log (1 / R)| + c) / R` also tends to `0` as `R → +∞`. -/
lemma tendsto_abs_log_inv_add_const_div_atTop_zero (c : ℝ) :
    Tendsto (fun R : ℝ ↦ (|Real.log (1 / R)| + c) / R) atTop (nhds 0) := by
  have hevent :
      (fun R : ℝ ↦ (|Real.log (1 / R)| + c) / R) =ᶠ[atTop]
        fun R ↦ (Real.log R + c) / R := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with R hR
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR.le
    have hlogInv : Real.log (1 / R) = -Real.log R := by
      simpa [one_div] using Real.log_inv (by linarith : R ≠ 0)
    rw [hlogInv, abs_neg, abs_of_nonneg hlogR]
  -- On the eventually positive half-line, `|log (1 / R)| = log R`.
  exact Filter.Tendsto.congr' hevent.symm (tendsto_log_add_const_div_atTop_zero c)

/-- Helper for Remark III.6-extra-7: for `R > 1`, the shifted logarithmic lip pair is exactly the
sum of the forward lower-lip interval integral and the reversed upper-lip interval integral at the
complementary angle `π - positiveAxisKeyholeAngle R (1 / R)`. -/
lemma positiveAxisShiftedLogLipPairTerm_eq_intervalSum
    (P Q : Polynomial ℂ) {R : ℝ} (hR : 1 < R) :
    let α := Real.pi - positiveAxisKeyholeAngle R (1 / R)
    positiveAxisShiftedLogLipPairTerm P Q R =
      -∫ x in (1 / R)..R, positiveAxisShiftedUpperLipKernel P Q α x +
        ∫ x in (1 / R)..R, positiveAxisShiftedLowerLipKernel P Q α x := by
  let α : ℝ := Real.pi - positiveAxisKeyholeAngle R (1 / R)
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hε : 0 < 1 / R := one_div_pos.mpr hRpos
  have hεR : 1 / R < R := by
    exact (div_lt_iff₀ hRpos).2 (by nlinarith [hR])
  have hα : α ∈ Set.Ioo (0 : ℝ) Real.pi := by
    -- The complementary lip angle stays in the principal strip once `R > 1`.
    simpa [α] using
      positiveAxisKeyhole_complementaryAngle_mem_Ioo
        (R := R) (ε := 1 / R) hε hεR
  have hupper :
      ∫ᶜ z in Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R (1 / R)))
          (circleMap 0 (1 / R) (positiveAxisKeyholeUpperAngle R (1 / R))),
        (((shiftedLogRationalNormalForm P Q) dz) z) =
        -∫ x in (1 / R)..R, positiveAxisShiftedUpperLipKernel P Q α x := by
    calc
      ∫ᶜ z in Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R (1 / R)))
          (circleMap 0 (1 / R) (positiveAxisKeyholeUpperAngle R (1 / R))),
        (((shiftedLogRationalNormalForm P Q) dz) z) =
          -∫ x in (1 / R)..R,
            Complex.exp ((Real.pi - α) * Complex.I) *
              shiftedLogRationalNormalForm P Q (circleMap 0 x (Real.pi - α)) := by
            -- Rewrite the upper slit lip against the common forward radius interval.
            simpa [α, positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle] using
              positiveAxisUpperLip_curveIntegral_eq_intervalIntegral
                (shiftedLogRationalNormalForm P Q) R (1 / R) (Real.pi - α) hRpos hε
      _ = -∫ x in (1 / R)..R, positiveAxisShiftedUpperLipKernel P Q α x := by
            -- On the upper lip, the shifted branch has the explicit value `log x - α i`.
            congr 1
            refine intervalIntegral.integral_congr ?_
            intro x hx
            have hxIcc : x ∈ Set.Icc (1 / R) R := by
              simpa [Set.uIcc_of_le hεR.le] using (hx : x ∈ Set.uIcc (1 / R) R)
            have hxpos : 0 < x := lt_of_lt_of_le hε hxIcc.1
            simp [positiveAxisShiftedUpperLipKernel, shiftedLogRationalNormalForm,
              positiveAxisShiftedBranch_upperLip_value (x := x) (α := α) hxpos hα, mul_assoc]
  have hlower :
      ∫ᶜ z in Path.segment
          (circleMap 0 (1 / R) (positiveAxisKeyholeLowerAngle R (1 / R)))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R (1 / R))),
        (((shiftedLogRationalNormalForm P Q) dz) z) =
        ∫ x in (1 / R)..R, positiveAxisShiftedLowerLipKernel P Q α x := by
    calc
      ∫ᶜ z in Path.segment
          (circleMap 0 (1 / R) (positiveAxisKeyholeLowerAngle R (1 / R)))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R (1 / R))),
        (((shiftedLogRationalNormalForm P Q) dz) z) =
          ∫ᶜ z in Path.segment
            (circleMap 0 (1 / R) (-positiveAxisKeyholeAngle R (1 / R)))
            (circleMap 0 R (-positiveAxisKeyholeAngle R (1 / R))),
          (((shiftedLogRationalNormalForm P Q) dz) z) := by
            -- The repaired lower slit lip is the old lower ray plus one full turn.
            congr 2
            · simpa using
                positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R (1 / R) (1 / R)
            · simpa using
                positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R (1 / R) R
      _ =
          ∫ x in (1 / R)..R,
            Complex.exp ((α - Real.pi) * Complex.I) *
              shiftedLogRationalNormalForm P Q (circleMap 0 x (α - Real.pi)) := by
            -- Rewrite the lower slit lip against the same forward interval.
            simpa [α, positiveAxisKeyholeAngle] using
              positiveAxisRadialSegment_curveIntegral_eq_intervalIntegral
                (shiftedLogRationalNormalForm P Q) (1 / R) R (α - Real.pi) hε hRpos
      _ = ∫ x in (1 / R)..R, positiveAxisShiftedLowerLipKernel P Q α x := by
            -- On the lower lip, the shifted branch has the reflected value `log x + α i`.
            refine intervalIntegral.integral_congr ?_
            intro x hx
            have hxIcc : x ∈ Set.Icc (1 / R) R := by
              simpa [Set.uIcc_of_le hεR.le] using (hx : x ∈ Set.uIcc (1 / R) R)
            have hxpos : 0 < x := lt_of_lt_of_le hε hxIcc.1
            simp [positiveAxisShiftedLowerLipKernel, shiftedLogRationalNormalForm,
              positiveAxisShiftedBranch_lowerLip_value (x := x) (α := α) hxpos hα, mul_assoc]
  -- Combine the normalized upper and lower slit pieces into the requested interval sum.
  simpa [α, positiveAxisShiftedLogLipPairTerm] using congrArg₂ (fun a b ↦ a + b) hupper hlower

/-- Helper for Remark III.6-extra-7: if a two-variable kernel is continuous on a compact strip,
its `α = π` slice vanishes there, and the angle parameter converges to `π` inside that strip, then
the corresponding interval integrals converge to `0`. This packages the compact-middle interval
argument used by both remaining lip-pair limits. -/
lemma intervalIntegral_tendsto_zero_of_compactStrip_uniformConvergence
    {K : ℝ → ℝ → ℂ} {α₀ δ S : ℝ}
    (hδS : δ ≤ S) (hα₀π : α₀ < Real.pi)
    (hcont :
      ContinuousOn (fun p : ℝ × ℝ ↦ K p.1 p.2)
        (Set.Icc α₀ Real.pi ×ˢ Set.Icc δ S))
    {αR : ℝ → ℝ} (hαR : Tendsto αR atTop (nhds Real.pi))
    (hmem : ∀ᶠ R : ℝ in atTop, αR R ∈ Set.Icc α₀ Real.pi)
    (hpi : ∀ x ∈ Set.Icc δ S, K Real.pi x = 0) :
    Tendsto (fun R : ℝ ↦ ∫ x in δ..S, K (αR R) x) atTop (nhds 0) := by
  let strip : Set (ℝ × ℝ) := Set.Icc α₀ Real.pi ×ˢ Set.Icc δ S
  have hcompactStrip : IsCompact strip := (isCompact_Icc.prod isCompact_Icc)
  have huc :
      UniformContinuousOn (fun p : ℝ × ℝ ↦ K p.1 p.2) strip :=
    hcompactStrip.uniformContinuousOn_of_continuous hcont
  have hπmem : Real.pi ∈ Set.Icc α₀ Real.pi := ⟨le_of_lt hα₀π, le_rfl⟩
  have huniform :
      TendstoUniformlyOn K (K Real.pi)
        (nhdsWithin Real.pi (Set.Icc α₀ Real.pi))
        (Set.Icc δ S) := by
    -- Uniform continuity on the compact strip upgrades the `α → π` convergence to a uniform
    -- `x ∈ Icc δ S` convergence statement.
    simpa [strip] using huc.tendstoUniformlyOn (x := Real.pi) hπmem
  have hαRwithin :
      Tendsto αR atTop (nhdsWithin Real.pi (Set.Icc α₀ Real.pi)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within αR hαR hmem
  refine NormedAddCommGroup.tendsto_nhds_zero.2 ?_
  intro ε hε
  let C : ℝ := ε / (|S - δ| + 1)
  have hCpos : 0 < C := by
    -- Shrink the uniform kernel bound by the interval length so that the integral norm is forced
    -- below the target `ε`.
    dsimp [C]
    positivity
  have hkernel :
      ∀ᶠ R : ℝ in atTop, ∀ x ∈ Set.uIoc δ S, ‖K (αR R) x‖ ≤ C := by
    have hmetric :
        ∀ᶠ a : ℝ in nhdsWithin Real.pi (Set.Icc α₀ Real.pi),
          ∀ x ∈ Set.Icc δ S, dist (K Real.pi x) (K a x) < C :=
      (Metric.tendstoUniformlyOn_iff.1 huniform) C hCpos
    have hmetricAtTop :
        ∀ᶠ R : ℝ in atTop,
          ∀ x ∈ Set.Icc δ S, dist (K Real.pi x) (K (αR R) x) < C := by
      exact hαRwithin.eventually hmetric
    filter_upwards [hmetricAtTop] with R hR x hx
    have hxIcc : x ∈ Set.Icc δ S := Set.uIoc_subset_uIcc hx
    have hxPi : K Real.pi x = 0 := hpi x hxIcc
    -- On the `π`-slice the kernel vanishes, so the uniform distance estimate is exactly the norm
    -- bound needed for `intervalIntegral.norm_integral_le_of_norm_le_const`.
    have hxNorm : ‖K (αR R) x‖ < C := by
      simpa [hxPi, dist_eq_norm] using hR x hxIcc
    exact le_of_lt hxNorm
  have hintegral :
      ∀ᶠ R : ℝ in atTop, ‖∫ x in δ..S, K (αR R) x‖ ≤ C * |S - δ| := by
    filter_upwards [hkernel] with R hR
    exact intervalIntegral.norm_integral_le_of_norm_le_const hR
  have hlength_lt : |S - δ| < |S - δ| + 1 := by
    linarith [abs_nonneg (S - δ)]
  have hmul_lt : C * |S - δ| < ε := by
    have hstep : C * |S - δ| < C * (|S - δ| + 1) :=
      mul_lt_mul_of_pos_left hlength_lt hCpos
    have hden : |S - δ| + 1 ≠ 0 := by positivity
    have hmul_eq : C * (|S - δ| + 1) = ε := by
      field_simp [C, hden]
    exact hstep.trans_eq hmul_eq
  -- The integral norm is eventually bounded by a quantity strictly smaller than `ε`.
  filter_upwards [hintegral] with R hR
  exact lt_of_le_of_lt hR hmul_lt

/-- Helper for Remark III.6-extra-7: the shifted-log contour already carries the full
`-(2π i) * ∫_0^∞ R(x) dx` asymptotic once its lip defect and circular remainder are shown to
vanish. -/
lemma positiveAxisShiftedLipPairSubTrunc_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        positiveAxisShiftedLogLipPairTerm P Q R -
          positiveAxisShiftedLogTruncTargetTerm P Q R)
      atTop
      (nhds 0) :=
  -- Route correction: the compact-strip convergence engine is now available in
  -- `intervalIntegral_tendsto_zero_of_compactStrip_uniformConvergence`, so the remaining shifted
  -- blocker is no longer interval analysis. The owner API still fixes
  -- `positiveAxisShiftedLipPairKernel_pi` with the `+2π i` jump, while
  -- `positiveAxisShiftedLogTruncTargetTerm` is normalized with `-(2π i)`, so the compact-middle
  -- interval cannot yet be rewritten against the truncation benchmark in one coherent sign world.
  sorry

/-- Helper for Remark III.6-extra-7: the shifted-log inner and outer circular branches vanish in
the large-keyhole limit once they are rewritten as sector arcs. -/
lemma positiveAxisShiftedLogArcPairTerm_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto (positiveAxisShiftedLogArcPairTerm P Q) atTop (nhds 0) := by
  let innerArcTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in ((Path.segment
        (positiveAxisKeyholeUpperAngle R (1 / R))
        (positiveAxisKeyholeLowerAngle R (1 / R))).map
          (continuous_circleMap 0 (1 / R))),
      (((shiftedLogRationalNormalForm P Q) dz) z)
  let outerArcTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in ((Path.segment
        (positiveAxisKeyholeLowerAngle R (1 / R))
        (positiveAxisKeyholeUpperAngle R (1 / R))).map
          (continuous_circleMap 0 R)),
      (((shiftedLogRationalNormalForm P Q) dz) z)
  obtain ⟨δ, M, hδ, hM, hsmall⟩ := exists_small_radius_bound_shiftedNormalForm P Q hcut'
  obtain ⟨K, R₀, hKR, hdecay⟩ := rationalEval_decay_of_degree_gap_two P Q hdeg
  have hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  obtain ⟨R₁, hR₁, hlarge⟩ := exists_large_radius_denominator_ne_zero Q hQ
  let innerBound : ℝ → ℝ := fun R ↦
    (M * (2 * Real.pi)) * ((|Real.log (1 / R)| + Real.pi) / R)
  let outerBound : ℝ → ℝ := fun R ↦
    (K * (2 * Real.pi)) * ((Real.log R + Real.pi) / R)
  have hinner :
      Tendsto innerArcTerm atTop (nhds 0) := by
    have hbound :
        ∀ᶠ R : ℝ in atTop, ‖innerArcTerm R‖ ≤ innerBound R := by
      filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / δ))] with R hR
      have hRgt1 : 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
      have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
      have hε : 0 < 1 / R := one_div_pos.mpr hRpos
      have hεR : 1 / R < R := (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
      have hεδ : 1 / R < δ := by
        have hδinv : 1 / δ < R := lt_of_le_of_lt (le_max_right _ _) hR
        nlinarith [hδ, hδinv]
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := 1 / R) hε hεR
      have hangle :=
        positiveAxisKeyhole_angle_bounds (R := R) (ε := 1 / R) hε hεR
      -- Rewrite the inner circular branch as a sector arc and apply the small-radius normal-form
      -- bound together with the logarithm estimate on the repaired major arc.
      rw [show innerArcTerm R =
        sectorArcIntegral
          (shiftedLogRationalNormalForm P Q)
          (1 / R)
          (positiveAxisKeyholeUpperAngle R (1 / R))
          (positiveAxisKeyholeLowerAngle R (1 / R)) by
            simp [innerArcTerm, positiveAxisCircleArc_curveIntegral_eq_sectorArcIntegral]]
      refine
        le_trans
          (sectorArcIntegral_norm_le_of_circleMap_mul_bound
            (f := shiftedLogRationalNormalForm P Q)
            (r := 1 / R)
            (θ₁ := positiveAxisKeyholeUpperAngle R (1 / R))
            (θ₂ := positiveAxisKeyholeLowerAngle R (1 / R))
            (C := M * ((|Real.log (1 / R)| + Real.pi) / R))
            (fun θ hθmem ↦ ?_))
          ?_
      · have hθIcc :
            θ ∈ Set.Icc
              (positiveAxisKeyholeUpperAngle R (1 / R))
              (positiveAxisKeyholeLowerAngle R (1 / R)) := by
          simpa [Set.uIcc_of_le horder.1.le] using Set.uIoc_subset_uIcc hθmem
        have hzDomain :
            circleMap 0 (1 / R) θ ∈ shiftedLogDomain :=
          circleMap_mem_shiftedLogDomain_of_keyholeMajorArc
            (hε := hε) (hεR := hεR) (hρlo := le_rfl) (hρhi := hεR.le) hθIcc
        have hzNormPos : 0 < ‖circleMap 0 (1 / R) θ‖ := by
          simpa [norm_circleMap_zero, abs_of_pos hε] using hε
        have hzNormLt : ‖circleMap 0 (1 / R) θ‖ < δ := by
          simpa [norm_circleMap_zero, abs_of_pos hε] using hεδ
        have hNF :
            ‖toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
                (circleMap 0 (1 / R) θ)‖ ≤ M :=
          hsmall
            (circleMap 0 (1 / R) θ) hzDomain hzNormPos hzNormLt
        have hθpos : 0 < θ := lt_of_lt_of_le hangle.1 hθIcc.1
        have hθlt : θ < 2 * Real.pi := lt_of_le_of_lt hθIcc.2 horder.2
        have hlog :
            ‖Complex.log (-circleMap 0 (1 / R) θ)‖ ≤
              |Real.log (1 / R)| + Real.pi :=
          norm_shiftedLog_on_keyhole_arc_le hε hθpos hθlt
        calc
          ‖circleMap 0 (1 / R) θ *
              shiftedLogRationalNormalForm P Q (circleMap 0 (1 / R) θ)‖ =
              (1 / R) *
                ‖toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
                    (circleMap 0 (1 / R) θ)‖ *
                ‖Complex.log (-circleMap 0 (1 / R) θ)‖ := by
                  simp [shiftedLogRationalNormalForm, norm_mul, norm_circleMap_zero,
                    abs_of_pos hε, mul_assoc]
          _ ≤ (1 / R) * M * (|Real.log (1 / R)| + Real.pi) := by
                gcongr
          _ = M * ((|Real.log (1 / R)| + Real.pi) / R) := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring
      · have hlength :
            |positiveAxisKeyholeLowerAngle R (1 / R) -
                positiveAxisKeyholeUpperAngle R (1 / R)| ≤ 2 * Real.pi :=
          positiveAxisKeyhole_majorArc_angleLength_le_two_pi hε hεR
        gcongr
    have hlimit :
        Tendsto innerBound atTop (nhds 0) := by
      -- The inner radius contributes the standard `(|log (1 / R)| + π) / R` decay.
      simpa [innerBound, mul_assoc] using
        Filter.Tendsto.const_mul (M * (2 * Real.pi))
          (tendsto_abs_log_inv_add_const_div_atTop_zero Real.pi)
    exact squeeze_zero_norm' hbound hlimit
  have houter :
      Tendsto outerArcTerm atTop (nhds 0) := by
    have hbound :
        ∀ᶠ R : ℝ in atTop, ‖outerArcTerm R‖ ≤ outerBound R := by
      filter_upwards [Filter.eventually_gt_atTop (max 1 (max R₀ R₁))] with R hR
      have hRgt1 : 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
      have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
      have hε : 0 < 1 / R := one_div_pos.mpr hRpos
      have hεR : 1 / R < R := (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
      have hRR₀ : R₀ < R := by
        have hmax : max R₀ R₁ < R := lt_of_le_of_lt (le_max_right _ _) hR
        exact lt_of_le_of_lt (le_max_left _ _) hmax
      have hRR₁ : R₁ < R := by
        have hmax : max R₀ R₁ < R := lt_of_le_of_lt (le_max_right _ _) hR
        exact lt_of_le_of_lt (le_max_right _ _) hmax
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := 1 / R) hε hεR
      have hangle :=
        positiveAxisKeyhole_angle_bounds (R := R) (ε := 1 / R) hε hεR
      -- Rewrite the outer branch as a sector arc and use the large-radius `R(z) = O(‖z‖⁻²)`
      -- estimate after transporting the shifted normal form back to the literal rational quotient.
      rw [show outerArcTerm R =
        sectorArcIntegral
          (shiftedLogRationalNormalForm P Q)
          R
          (positiveAxisKeyholeLowerAngle R (1 / R))
          (positiveAxisKeyholeUpperAngle R (1 / R)) by
            simp [outerArcTerm, positiveAxisCircleArc_curveIntegral_eq_sectorArcIntegral]]
      refine
        le_trans
          (sectorArcIntegral_norm_le_of_circleMap_mul_bound
            (f := shiftedLogRationalNormalForm P Q)
            (r := R)
            (θ₁ := positiveAxisKeyholeLowerAngle R (1 / R))
            (θ₂ := positiveAxisKeyholeUpperAngle R (1 / R))
            (C := K * ((Real.log R + Real.pi) / R))
            (fun θ hθmem ↦ ?_))
          ?_
      · have hθIcc :
            θ ∈ Set.Icc
              (positiveAxisKeyholeUpperAngle R (1 / R))
              (positiveAxisKeyholeLowerAngle R (1 / R)) := by
          simpa [Set.uIcc_of_le horder.1.le, Set.uIcc_comm] using Set.uIoc_subset_uIcc hθmem
        have hzDomain :
            circleMap 0 R θ ∈ shiftedLogDomain :=
          circleMap_mem_shiftedLogDomain_of_keyholeMajorArc
            (hε := hε) (hεR := hεR) (hρlo := hεR.le) (hρhi := le_rfl) hθIcc
        have hQz : Q.eval (circleMap 0 R θ) ≠ 0 := by
          apply hlarge (circleMap 0 R θ)
          simpa [norm_circleMap_zero, abs_of_pos hRpos] using hRR₁.le
        have hEq :
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain (circleMap 0 R θ) =
              rationalEval P Q (circleMap 0 R θ) :=
          rationalEval_shiftedNormalForm_eq_of_denominator_ne_zero P Q hzDomain hQz
        have hrat :
            ‖rationalEval P Q (circleMap 0 R θ)‖ ≤ K / R ^ (2 : ℕ) := by
          simpa [norm_circleMap_zero, abs_of_pos hRpos] using
            hdecay (circleMap 0 R θ) hRR₀.le
        have hscale :
            R * ‖rationalEval P Q (circleMap 0 R θ)‖ ≤ K / R := by
          calc
            R * ‖rationalEval P Q (circleMap 0 R θ)‖ ≤ R * (K / R ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hrat hRpos.le
            _ = K / R := by
              field_simp [pow_two, hRpos.ne']
              ring
        have hθpos : 0 < θ := lt_of_lt_of_le hangle.1 hθIcc.1
        have hθlt : θ < 2 * Real.pi := lt_of_le_of_lt hθIcc.2 horder.2
        have hlogAbs :
            ‖Complex.log (-circleMap 0 R θ)‖ ≤ |Real.log R| + Real.pi :=
          norm_shiftedLog_on_keyhole_arc_le hRpos hθpos hθlt
        have hlog :
            ‖Complex.log (-circleMap 0 R θ)‖ ≤ Real.log R + Real.pi := by
          have hlogR : 0 ≤ Real.log R := Real.log_nonneg hRgt1.le
          calc
            ‖Complex.log (-circleMap 0 R θ)‖ ≤ |Real.log R| + Real.pi := hlogAbs
            _ = Real.log R + Real.pi := by rw [abs_of_nonneg hlogR]
        calc
          ‖circleMap 0 R θ * shiftedLogRationalNormalForm P Q (circleMap 0 R θ)‖ =
              R * ‖rationalEval P Q (circleMap 0 R θ)‖ *
                ‖Complex.log (-circleMap 0 R θ)‖ := by
                  simp [shiftedLogRationalNormalForm, hEq, norm_mul, norm_circleMap_zero,
                    abs_of_pos hRpos, mul_assoc]
          _ ≤ (K / R) * (Real.log R + Real.pi) := by
                gcongr
          _ = K * ((Real.log R + Real.pi) / R) := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring
      · have hlength :
            |positiveAxisKeyholeUpperAngle R (1 / R) -
                positiveAxisKeyholeLowerAngle R (1 / R)| ≤ 2 * Real.pi :=
          positiveAxisKeyhole_majorArc_angleLength_le_two_pi hε hεR
        simpa [abs_sub_comm] using mul_le_mul_of_nonneg_left hlength (by positivity : 0 ≤ K * ((Real.log R + Real.pi) / R))
    have hlimit :
        Tendsto outerBound atTop (nhds 0) := by
      -- The outer radius contributes the standard `(log R + π) / R` decay.
      simpa [outerBound, mul_assoc] using
        Filter.Tendsto.const_mul (K * (2 * Real.pi))
          (tendsto_log_add_const_div_atTop_zero Real.pi)
    exact squeeze_zero_norm' hbound hlimit
  have hsplit :
      positiveAxisShiftedLogArcPairTerm P Q = fun R ↦ innerArcTerm R + outerArcTerm R := by
    funext R
    simp [positiveAxisShiftedLogArcPairTerm, innerArcTerm, outerArcTerm]
  -- Add the vanishing inner and outer sector-arc contributions.
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.of_eq hsplit.symm) ?_
  simpa [innerArcTerm, outerArcTerm] using hinner.add houter

/-- Helper for Remark III.6-extra-7: the shifted-log contour already carries the full
`-(2π i) * ∫_0^∞ R(x) dx` asymptotic once its lip defect and circular remainder are shown to
vanish. -/
lemma positiveAxisShiftedLogRemainder_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        (∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
            (((shiftedLogRationalNormalForm P Q) dz) z)) -
          positiveAxisShiftedLogTruncTargetTerm P Q R)
      atTop
      (nhds 0) := by
  have hsplit :
      (fun R : ℝ ↦
        (∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
            (((shiftedLogRationalNormalForm P Q) dz) z)) -
          positiveAxisShiftedLogTruncTargetTerm P Q R) =ᶠ[atTop]
        fun R : ℝ ↦
          (positiveAxisShiftedLogLipPairTerm P Q R -
              positiveAxisShiftedLogTruncTargetTerm P Q R) +
            positiveAxisShiftedLogArcPairTerm P Q R := by
    -- Route correction: first replace the grouped remainder by the stabilized lip-plus-arc
    -- decomposition from the theorem-local support file.
    exact eventually_positiveAxisShiftedLogRemainder_eq_lipPair_add_arcPair P Q hdeg hcut'
  have hlip :
      Tendsto
        (fun R : ℝ ↦
          positiveAxisShiftedLogLipPairTerm P Q R -
            positiveAxisShiftedLogTruncTargetTerm P Q R)
        atTop
        (nhds 0) := by
    -- The remaining lip defect is isolated in its own closing lemma.
    exact positiveAxisShiftedLipPairSubTrunc_tendsto_zero P Q hdeg hcut'
  have harc :
      Tendsto (positiveAxisShiftedLogArcPairTerm P Q) atTop (nhds 0) := by
    -- The circular remainder is handled independently by the sector-arc estimates.
    exact positiveAxisShiftedLogArcPairTerm_tendsto_zero P Q hdeg hcut'
  -- Replace the grouped contour remainder by the stabilized decomposition and add the two
  -- vanishing pieces.
  refine Filter.Tendsto.congr' hsplit.symm ?_
  simpa using hlip.add harc

/-- Helper for Remark III.6-extra-7: the shifted-log contour already carries the full
`-(2π i) * ∫_0^∞ R(x) dx` asymptotic once its grouped remainder is known to vanish. -/
lemma shiftedLogKeyhole_curveIntegral_tendsto_neg_two_pi_I_integral
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((shiftedLogRationalNormalForm P Q) dz) z))
      atTop
      (nhds
        ((-(2 * Real.pi * Complex.I : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
  let contourTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
      (((shiftedLogRationalNormalForm P Q) dz) z)
  let truncTerm : ℝ → ℂ := positiveAxisShiftedLogTruncTargetTerm P Q
  have hsplit :
      contourTerm = fun R ↦ (contourTerm R - truncTerm R) + truncTerm R := by
    -- Split the contour into the already-controlled remainder plus the explicit real-axis term.
    funext R
    simp [contourTerm, truncTerm]
  have hrem :
      Tendsto (fun R ↦ contourTerm R - truncTerm R) atTop (nhds 0) := by
    -- The grouped contour remainder has already been isolated in its own theorem.
    simpa [contourTerm, truncTerm] using
      positiveAxisShiftedLogRemainder_tendsto_zero P Q hdeg hcut'
  have htruncReal :
      Tendsto
        (fun R : ℝ ↦ ∫ x in (1 / R)..R, rationalEval P Q (x : ℂ))
        atTop
        (nhds (∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
    -- The positive-real truncations converge to the improper integral independently of the
    -- contour normalization.
    exact rationalEval_intervalIntegral_tendsto_integral_Ioi P Q hdeg hcut'
  have htrunc :
      Tendsto
        (positiveAxisShiftedLogTruncTargetTerm P Q)
        atTop
        (nhds
          ((-(2 * Real.pi * Complex.I : ℂ)) *
            ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
    -- The truncation term is just the fixed scalar `-(2π i)` times the real-axis truncation.
    change
      Tendsto
        (fun R : ℝ ↦
          (-(2 * Real.pi * Complex.I : ℂ)) *
            ∫ x in (1 / R)..R, rationalEval P Q (x : ℂ))
        atTop
        (nhds
          ((-(2 * Real.pi * Complex.I : ℂ)) *
            ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume))
    simpa [positiveAxisShiftedLogTruncTargetTerm] using
      Filter.Tendsto.const_mul (-(2 * Real.pi * Complex.I : ℂ)) htruncReal
  have hsum :
      Tendsto
        (fun R ↦ (contourTerm R - truncTerm R) + truncTerm R)
        atTop
        (nhds
          ((-(2 * Real.pi * Complex.I : ℂ)) *
            ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
    -- Add the already-vanishing grouped remainder to the truncation limit.
    simpa [truncTerm] using hrem.add htrunc
  -- Replace the contour by remainder plus truncation and read off the resulting limit.
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.of_eq hsplit.symm) hsum

/-- Helper for Remark III.6-extra-7: once the positive-axis keyhole frontier is pole-free, the
bare rational normal-form contour splits into the same lip-pair plus arc-pair decomposition as the
shifted logarithmic contour. -/
lemma eventually_positiveAxisBareNormalFormContour_eq_lipPair_add_arcPair
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∀ᶠ R : ℝ in atTop,
      let G := toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
      ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath, ((G dz) z) =
        positiveAxisKeyholeLipPairIntegral G R (1 / R) +
          positiveAxisKeyholeArcPairIntegral G R (1 / R) := by
  let s : Finset ℂ := rationalEvalPoleFinset P Q
  let G : ℂ → ℂ := toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
  let hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  have hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s :=
    rationalEval_pole_iff_mem_poleFinset P Q hQ
  have hscalarCont : ContinuousOn G (shiftedLogDomain \ (↑s : Set ℂ)) := by
    -- Off the finite pole set, the shifted-domain rational normal form is holomorphic and hence
    -- continuous.
    exact
      (rationalNormalForm_differentiableOn_shiftedLogDomain_off_poles P Q hpoles').continuousOn
  filter_upwards
      [eventually_rationalEvalPoleFinset_subset_interior_positiveAxisWedgeAnnulus P Q hdeg hcut']
      with R hR
  rcases hR with ⟨hRgt1, hInterior⟩
  let ε : ℝ := 1 / R
  have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
  have hε : 0 < ε := by
    dsimp [ε]
    exact one_div_pos.mpr hRpos
  have hεR : ε < R := by
    dsimp [ε]
    exact (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
  have hfrontier :
      frontier (positiveAxisWedgeAnnulus R ε) = Set.range (positiveAxisKeyhole R ε) :=
    positiveAxisWedgeAnnulus_frontier_eq_range R ε hε hεR
  have hpathRange :
      Set.range (positiveAxisKeyhole R ε) ⊆ shiftedLogDomain \ (↑s : Set ℂ) := by
    intro z hz
    have hzFrontier : z ∈ frontier (positiveAxisWedgeAnnulus R ε) := by
      simpa [hfrontier] using hz
    have hzClosure : z ∈ closure (positiveAxisWedgeAnnulus R ε) :=
      frontier_subset_closure hzFrontier
    have hzWedge : z ∈ positiveAxisWedgeAnnulus R ε := by
      simpa [isClosed_positiveAxisWedgeAnnulus R ε |>.closure_eq] using hzClosure
    have hzNotPole : z ∉ (↑s : Set ℂ) := by
      intro hzPole
      have hzInterior : z ∈ interior (positiveAxisWedgeAnnulus R ε) := hInterior z hzPole
      have hzFrontier' := hzFrontier
      change z ∈ closure (positiveAxisWedgeAnnulus R ε) \ interior (positiveAxisWedgeAnnulus R ε)
        at hzFrontier'
      exact hzFrontier'.2 hzInterior
    exact ⟨positiveAxisWedgeAnnulus_subset_shiftedLogDomain hε hεR hzWedge, hzNotPole⟩
  have hupperRange :
      Set.range
          (Path.segment
            (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inl (Or.inl (Or.inl hz))
  have hinnerRange :
      Set.range
          (((Path.segment
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)).map
                (continuous_circleMap 0 ε))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inl (Or.inl (Or.inr hz))
  have hlowerRange :
      Set.range
          (Path.segment
            (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
            (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inl (Or.inr hz)
  have houterRange :
      Set.range
          (((Path.segment
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)).map
                (continuous_circleMap 0 R))) ⊆
        Set.range (positiveAxisKeyhole R ε) := by
    intro z hz
    rw [positiveAxisKeyhole_range_eq_four_piece_union]
    dsimp
    exact Or.inr hz
  have hupper :
      CurveIntegrable
        (G dz)
        (Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))) := by
    have hupperReal :
        CurveIntegrable
          (Complex.realScalarOneForm G)
          (Path.segment
            (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))) := by
      have hupperRealCont :
          ContinuousOn
            (Complex.realScalarOneForm G)
            (shiftedLogDomain \ (↑s : Set ℂ)) := by
        rw [show Complex.realScalarOneForm G =
            fun z ↦ G z • (1 : ℂ →L[ℝ] ℂ) by
              funext z
              exact Complex.realScalarOneForm_eq_smul G z]
        exact hscalarCont.smul
          (continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ)))
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hupperRealCont (Path.segment_isPiecewiseDifferentiable _ _)
        (Set.Subset.trans hupperRange hpathRange)
    simpa [G, Complex.realScalarOneForm] using hupperReal
  have hinner :
      CurveIntegrable
        (G dz)
        ((Path.segment
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)).map
              (continuous_circleMap 0 ε)) := by
    have hinnerReal :
        CurveIntegrable
          (Complex.realScalarOneForm G)
          ((Path.segment
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)).map
                (continuous_circleMap 0 ε)) := by
      have hinnerRealCont :
          ContinuousOn
            (Complex.realScalarOneForm G)
            (shiftedLogDomain \ (↑s : Set ℂ)) := by
        rw [show Complex.realScalarOneForm G =
            fun z ↦ G z • (1 : ℂ →L[ℝ] ℂ) by
              funext z
              exact Complex.realScalarOneForm_eq_smul G z]
        exact hscalarCont.smul
          (continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ)))
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hinnerRealCont
        ((positiveAxisKeyhole_circle_segment_isDifferentiable ε
          (positiveAxisKeyholeUpperAngle R ε)
          (positiveAxisKeyholeLowerAngle R ε)).isPiecewiseDifferentiable)
        (Set.Subset.trans hinnerRange hpathRange)
    simpa [G, Complex.realScalarOneForm] using hinnerReal
  have hlower :
      CurveIntegrable
        (G dz)
        (Path.segment
          (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))) := by
    have hlowerReal :
        CurveIntegrable
          (Complex.realScalarOneForm G)
          (Path.segment
            (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
            (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))) := by
      have hlowerRealCont :
          ContinuousOn
            (Complex.realScalarOneForm G)
            (shiftedLogDomain \ (↑s : Set ℂ)) := by
        rw [show Complex.realScalarOneForm G =
            fun z ↦ G z • (1 : ℂ →L[ℝ] ℂ) by
              funext z
              exact Complex.realScalarOneForm_eq_smul G z]
        exact hscalarCont.smul
          (continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ)))
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hlowerRealCont (Path.segment_isPiecewiseDifferentiable _ _)
        (Set.Subset.trans hlowerRange hpathRange)
    simpa [G, Complex.realScalarOneForm] using hlowerReal
  have houter :
      CurveIntegrable
        (G dz)
        ((Path.segment
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)).map
              (continuous_circleMap 0 R)) := by
    have houterReal :
        CurveIntegrable
          (Complex.realScalarOneForm G)
          ((Path.segment
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)).map
                (continuous_circleMap 0 R)) := by
      have houterRealCont :
          ContinuousOn
            (Complex.realScalarOneForm G)
            (shiftedLogDomain \ (↑s : Set ℂ)) := by
        rw [show Complex.realScalarOneForm G =
            fun z ↦ G z • (1 : ℂ →L[ℝ] ℂ) by
              funext z
              exact Complex.realScalarOneForm_eq_smul G z]
        exact hscalarCont.smul
          (continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ))
              (shiftedLogDomain \ (↑s : Set ℂ)))
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        houterRealCont
        ((positiveAxisKeyhole_circle_segment_isDifferentiable R
          (positiveAxisKeyholeLowerAngle R ε)
          (positiveAxisKeyholeUpperAngle R ε)).isPiecewiseDifferentiable)
        (Set.Subset.trans houterRange hpathRange)
    simpa [G, Complex.realScalarOneForm] using houterReal
  -- Once each branch is integrable, the generic keyhole contour theorem groups them into the lip
  -- pair and the arc pair.
  simpa [G, ε] using
    positiveAxisKeyhole_curveIntegral_eq_lipPairIntegral_add_arcIntegrals G R ε
      hupper hinner hlower houter

/-- Helper for Remark III.6-extra-7: for `R > 1`, the bare meromorphic-normal-form lip pair is
the sum of the forward lower-lip interval integral and the reversed upper-lip interval integral at
the same complementary angle `π - positiveAxisKeyholeAngle R (1 / R)`. -/
lemma positiveAxisBareNormalFormLipPairIntegral_eq_intervalSum
    (P Q : Polynomial ℂ) {R : ℝ} (hR : 1 < R) :
    let α := Real.pi - positiveAxisKeyholeAngle R (1 / R)
    positiveAxisKeyholeLipPairIntegral
      (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) R (1 / R) =
      -∫ x in (1 / R)..R,
          Complex.exp ((Real.pi - α) * Complex.I) *
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
              (circleMap 0 x (Real.pi - α)) +
        ∫ x in (1 / R)..R,
          Complex.exp ((α - Real.pi) * Complex.I) *
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
              (circleMap 0 x (α - Real.pi)) := by
  let α : ℝ := Real.pi - positiveAxisKeyholeAngle R (1 / R)
  let G : ℂ → ℂ := toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hε : 0 < 1 / R := one_div_pos.mpr hRpos
  have hupper :
      ∫ᶜ z in Path.segment
          (circleMap 0 R (positiveAxisKeyholeUpperAngle R (1 / R)))
          (circleMap 0 (1 / R) (positiveAxisKeyholeUpperAngle R (1 / R))),
        ((G dz) z) =
        -∫ x in (1 / R)..R,
          Complex.exp ((Real.pi - α) * Complex.I) * G (circleMap 0 x (Real.pi - α)) := by
    -- Rewrite the upper bare lip to the common radius interval.
    simpa [α, G, positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle] using
      positiveAxisUpperLip_curveIntegral_eq_intervalIntegral
        G R (1 / R) (Real.pi - α) hRpos hε
  have hlower :
      ∫ᶜ z in Path.segment
          (circleMap 0 (1 / R) (positiveAxisKeyholeLowerAngle R (1 / R)))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R (1 / R))),
        ((G dz) z) =
        ∫ x in (1 / R)..R,
          Complex.exp ((α - Real.pi) * Complex.I) * G (circleMap 0 x (α - Real.pi)) := by
    calc
      ∫ᶜ z in Path.segment
          (circleMap 0 (1 / R) (positiveAxisKeyholeLowerAngle R (1 / R)))
          (circleMap 0 R (positiveAxisKeyholeLowerAngle R (1 / R))),
        ((G dz) z) =
          ∫ᶜ z in Path.segment
            (circleMap 0 (1 / R) (-positiveAxisKeyholeAngle R (1 / R)))
            (circleMap 0 R (-positiveAxisKeyholeAngle R (1 / R))),
          ((G dz) z) := by
            -- Replace the repaired lower angle by the old negative-angle ray.
            congr 2
            · simpa using
                positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R (1 / R) (1 / R)
            · simpa using
                positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower R (1 / R) R
      _ =
          ∫ x in (1 / R)..R,
            Complex.exp ((α - Real.pi) * Complex.I) * G (circleMap 0 x (α - Real.pi)) := by
            -- Rewrite the lower bare lip against the same forward interval.
            simpa [α, G, positiveAxisKeyholeAngle] using
              positiveAxisRadialSegment_curveIntegral_eq_intervalIntegral
                G (1 / R) R (α - Real.pi) hε hRpos
  -- With both radial pieces straightened, the lip pair is exactly the claimed interval sum.
  simpa [α, G, positiveAxisKeyholeLipPairIntegral] using congrArg₂ (fun a b ↦ a + b) hupper hlower

/-- Helper for Remark III.6-extra-7: after deleting the center point itself, a sufficiently small
ball around any point avoids all denominator roots. This is the local root-separation package used
when the slit-lip points are transported to the global meromorphic normal form. -/
lemma exists_small_radius_denominator_ne_zero_around_point
    (Q : Polynomial ℂ) (hQ : Q ≠ 0) (w : ℂ) :
    ∃ δ > 0, ∀ z : ℂ, 0 < ‖z - w‖ → ‖z - w‖ < δ → Q.eval z ≠ 0 := by
  let bad : Set ℂ := (Q.roots.toFinset : Set ℂ) \ ({w} : Set ℂ)
  have hbadFinite : bad.Finite :=
    Q.roots.toFinset.finite_toSet.subset fun _ hz ↦ hz.1
  have hbadClosed : IsClosed bad := hbadFinite.isClosed
  have hwnot : w ∉ bad := by
    simp [bad]
  have hnhds : badᶜ ∈ nhds w :=
    IsClosed.compl_mem_nhds hbadClosed hwnot
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hδball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro z hzw hzδ hQz
  have hzball : z ∈ Metric.ball w δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzδ
  have hznotbad : z ∉ bad := hδball hzball
  have hzroot : z ∈ (Q.roots.toFinset : Set ℂ) := by
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hQ).2 hQz)
  have hzne : z ≠ w := by
    simpa using norm_ne_zero_iff.mp (ne_of_gt hzw)
  -- Any nonzero root in this small ball would belong to the forbidden finite set `bad`.
  exact hznotbad ⟨hzroot, by simpa [hzne]⟩

/-- Helper for Remark III.6-extra-7: at each fixed positive radius, the bare paired lip kernel
converges to `0` as the complementary angle tends to `π`. This isolates the pointwise limiting
behavior needed for the compact-middle interval estimate. -/
lemma positiveAxisBareLipPairKernel_tendsto_zero_at_pi
    (P Q : Polynomial ℂ) {x : ℝ} (hx : 0 < x)
    (hcut' :
      ∀ y : ℝ, 0 ≤ y → ¬ meromorphicOrderAt (rationalEval P Q) (y : ℂ) < 0) :
    Tendsto
      (fun α : ℝ ↦
        Complex.exp ((α - Real.pi) * Complex.I) *
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
              (circleMap 0 x (α - Real.pi)) -
          Complex.exp ((Real.pi - α) * Complex.I) *
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
              (circleMap 0 x (Real.pi - α)))
      (nhds Real.pi)
      (nhds 0) := by
  by_cases hQ : Q = 0
  · subst hQ
    -- If the denominator is the zero polynomial, the rational kernel and both slit-lip terms are
    -- identically zero.
    simp [rationalEval]
  let G : ℂ → ℂ := toMeromorphicNFOn (rationalEval P Q) Set.univ
  obtain ⟨δroot, hδrootPos, hrootSep⟩ :=
    exists_small_radius_denominator_ne_zero_around_point Q hQ (x : ℂ)
  have hGcont : ContinuousAt G (x : ℂ) := by
    -- On the positive real axis, the global normal form is holomorphic because there are no poles
    -- on the cut.
    exact
      (rationalEval_univNormalForm_differentiableAt_of_not_pole
        P Q (z := (x : ℂ)) (hcut' x hx.le)).continuousAt
  have hlowerMap :
      Tendsto
        (fun α : ℝ ↦ circleMap 0 x (α - Real.pi))
        (nhds Real.pi)
        (nhds (x : ℂ)) := by
    have harg :
        Tendsto (fun α : ℝ ↦ α - Real.pi) (nhds Real.pi) (nhds 0) :=
      (continuous_id.sub continuous_const).continuousAt.tendsto
    simpa [circleMap_zero] using
      (((continuous_circleMap 0 x).continuousAt : ContinuousAt (circleMap 0 x) 0).tendsto.comp harg)
  have hupperMap :
      Tendsto
        (fun α : ℝ ↦ circleMap 0 x (Real.pi - α))
        (nhds Real.pi)
        (nhds (x : ℂ)) := by
    have harg :
        Tendsto (fun α : ℝ ↦ Real.pi - α) (nhds Real.pi) (nhds 0) :=
      (continuous_const.sub continuous_id).continuousAt.tendsto
    simpa [circleMap_zero] using
      (((continuous_circleMap 0 x).continuousAt : ContinuousAt (circleMap 0 x) 0).tendsto.comp harg)
  have hlowerClose :
      ∀ᶠ α : ℝ in nhds Real.pi,
        ‖circleMap 0 x (α - Real.pi) - (x : ℂ)‖ < δroot :=
    hlowerMap.eventually (Metric.ball_mem_nhds (x : ℂ) hδrootPos)
  have hupperClose :
      ∀ᶠ α : ℝ in nhds Real.pi,
        ‖circleMap 0 x (Real.pi - α) - (x : ℂ)‖ < δroot :=
    hupperMap.eventually (Metric.ball_mem_nhds (x : ℂ) hδrootPos)
  have hargSmall :
      ∀ᶠ α : ℝ in nhds Real.pi, |α - Real.pi| < Real.pi / 2 := by
    filter_upwards [Metric.ball_mem_nhds Real.pi (by positivity : 0 < Real.pi / 2)] with α hα
    simpa [Metric.mem_ball, Real.dist_eq] using hα
  have hkernelEq :
      (fun α : ℝ ↦
        Complex.exp ((α - Real.pi) * Complex.I) *
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
              (circleMap 0 x (α - Real.pi)) -
          Complex.exp ((Real.pi - α) * Complex.I) *
            toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
              (circleMap 0 x (Real.pi - α))) =ᶠ[nhds Real.pi]
        (fun α : ℝ ↦
          Complex.exp ((α - Real.pi) * Complex.I) * G (circleMap 0 x (α - Real.pi)) -
            Complex.exp ((Real.pi - α) * Complex.I) * G (circleMap 0 x (Real.pi - α))) := by
    filter_upwards [hlowerClose, hupperClose, hargSmall] with α hLowerClose hUpperClose hαsmall
    by_cases hαπ : α = Real.pi
    · -- At the limiting angle, both kernels collapse to the same positive-real value and cancel.
      subst hαπ
      simp [G, circleMap_zero]
    · set β : ℝ := α - Real.pi
      have hβIcc : β ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        refine ⟨?_, ?_⟩ <;> dsimp [β] at * <;> linarith
      have hβne : β ≠ 0 := by
        dsimp [β]
        linarith
      have hsinβ : Real.sin β ≠ 0 := by
        intro hsinβ0
        have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> positivity
        have hβzero : β = 0 :=
          Real.strictMonoOn_sin.injOn hβIcc hzeroIcc (by simpa [hsinβ0])
        exact hβne hβzero
      let zLower : ℂ := circleMap 0 x β
      let zUpper : ℂ := circleMap 0 x (-β)
      have hzLowerMem : zLower ∈ shiftedLogDomain := by
        change -zLower ∈ Complex.slitPlane
        rw [Complex.mem_slitPlane_iff]
        right
        have hzLowerIm : zLower.im ≠ 0 := by
          simpa [zLower, β, circleMap_zero_im] using mul_ne_zero hx.ne' hsinβ
        simpa [zLower] using neg_ne_zero.mpr hzLowerIm
      have hzUpperMem : zUpper ∈ shiftedLogDomain := by
        change -zUpper ∈ Complex.slitPlane
        rw [Complex.mem_slitPlane_iff]
        right
        have hzUpperIm : zUpper.im ≠ 0 := by
          have hsinNeg : Real.sin (-β) ≠ 0 := by
            simpa using neg_ne_zero.mpr hsinβ
          simpa [zUpper, circleMap_zero_im] using mul_ne_zero hx.ne' hsinNeg
        simpa [zUpper] using neg_ne_zero.mpr hzUpperIm
      have hzLowerNe : zLower ≠ (x : ℂ) := by
        intro hzEq
        have hzLowerIm : zLower.im ≠ 0 := by
          simpa [zLower, β, circleMap_zero_im] using mul_ne_zero hx.ne' hsinβ
        exact hzLowerIm (by simpa [hzEq])
      have hzUpperNe : zUpper ≠ (x : ℂ) := by
        intro hzEq
        have hzUpperIm : zUpper.im ≠ 0 := by
          have hsinNeg : Real.sin (-β) ≠ 0 := by
            simpa using neg_ne_zero.mpr hsinβ
          simpa [zUpper, circleMap_zero_im] using mul_ne_zero hx.ne' hsinNeg
        exact hzUpperIm (by simpa [hzEq])
      have hzLowerDistPos : 0 < ‖zLower - (x : ℂ)‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hzLowerNe)
      have hzUpperDistPos : 0 < ‖zUpper - (x : ℂ)‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hzUpperNe)
      have hQlower : Q.eval zLower ≠ 0 :=
        hrootSep zLower hzLowerDistPos (by simpa [zLower, β] using hLowerClose)
      have hQupper : Q.eval zUpper ≠ 0 :=
        hrootSep zUpper hzUpperDistPos (by simpa [zUpper, β] using hUpperClose)
      have hshiftLower :
          toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain zLower = rationalEval P Q zLower :=
        rationalEval_shiftedNormalForm_eq_of_denominator_ne_zero P Q hzLowerMem hQlower
      have hshiftUpper :
          toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain zUpper = rationalEval P Q zUpper :=
        rationalEval_shiftedNormalForm_eq_of_denominator_ne_zero P Q hzUpperMem hQupper
      have hglobalLower : G zLower = rationalEval P Q zLower :=
        rationalEval_univNormalForm_eq_of_denominator_ne_zero P Q hQlower
      have hglobalUpper : G zUpper = rationalEval P Q zUpper :=
        rationalEval_univNormalForm_eq_of_denominator_ne_zero P Q hQupper
      -- Away from the center point, both slit-side normal forms agree with the literal quotient,
      -- so the paired kernel can be transported to the global normal form.
      simp [G, zLower, zUpper, β, hshiftLower, hshiftUpper, hglobalLower, hglobalUpper]
  have hlowerCoeff :
      Tendsto (fun α : ℝ ↦ Complex.exp ((α - Real.pi) * Complex.I)) (nhds Real.pi) (nhds 1) := by
    have harg :
        Tendsto (fun α : ℝ ↦ (α - Real.pi) * Complex.I) (nhds Real.pi) (nhds 0) := by
      simpa using
        Filter.Tendsto.const_mul Complex.I
          ((continuous_id.sub continuous_const).continuousAt.tendsto
            : Tendsto (fun α : ℝ ↦ α - Real.pi) (nhds Real.pi) (nhds 0))
    simpa using Complex.continuous_exp.continuousAt.tendsto.comp harg
  have hupperCoeff :
      Tendsto (fun α : ℝ ↦ Complex.exp ((Real.pi - α) * Complex.I)) (nhds Real.pi) (nhds 1) := by
    have harg :
        Tendsto (fun α : ℝ ↦ (Real.pi - α) * Complex.I) (nhds Real.pi) (nhds 0) := by
      simpa using
        Filter.Tendsto.const_mul Complex.I
          ((continuous_const.sub continuous_id).continuousAt.tendsto
            : Tendsto (fun α : ℝ ↦ Real.pi - α) (nhds Real.pi) (nhds 0))
    simpa using Complex.continuous_exp.continuousAt.tendsto.comp harg
  have hlowerTerm :
      Tendsto
        (fun α : ℝ ↦ Complex.exp ((α - Real.pi) * Complex.I) * G (circleMap 0 x (α - Real.pi)))
        (nhds Real.pi)
        (nhds (G (x : ℂ))) := by
    -- The lower slit chart and its tangent factor both converge to the positive real point.
    simpa [one_mul] using hlowerCoeff.mul (hGcont.tendsto.comp hlowerMap)
  have hupperTerm :
      Tendsto
        (fun α : ℝ ↦ Complex.exp ((Real.pi - α) * Complex.I) * G (circleMap 0 x (Real.pi - α)))
        (nhds Real.pi)
        (nhds (G (x : ℂ))) := by
    -- The upper slit chart has the same limiting value on the global normal form.
    simpa [one_mul] using hupperCoeff.mul (hGcont.tendsto.comp hupperMap)
  have haux :
      Tendsto
        (fun α : ℝ ↦
          Complex.exp ((α - Real.pi) * Complex.I) * G (circleMap 0 x (α - Real.pi)) -
            Complex.exp ((Real.pi - α) * Complex.I) * G (circleMap 0 x (Real.pi - α)))
        (nhds Real.pi)
        (nhds 0) := by
    -- After transporting to the global normal form, both slit-side terms converge to the same
    -- limit and therefore cancel.
    simpa using hlowerTerm.sub hupperTerm
  -- Replace the shifted-domain kernel by the global-normal-form kernel and use the common limit.
  exact Filter.Tendsto.congr' hkernelEq haux

/-- Helper for Remark III.6-extra-7: after shrinking to a sufficiently thin angular neighborhood
of the positive ray, the bare paired lip kernel is continuous on the compact strip
`Set.Icc α₀ π ×ˢ Set.Icc δ S`. This is the pole-avoidance package needed for the compact-middle
interval estimate in the bare lip-pair limit. -/
lemma positiveAxisBareLipPairKernel_continuousOnCompactStrip
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    {δ S : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    ∃ α₀ < Real.pi,
      ContinuousOn
        (fun p : ℝ × ℝ ↦
          Complex.exp ((p.1 - Real.pi) * Complex.I) *
              toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
                (circleMap 0 p.2 (p.1 - Real.pi)) -
            Complex.exp ((Real.pi - p.1) * Complex.I) *
              toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
                (circleMap 0 p.2 (Real.pi - p.1)))
        (Set.Icc α₀ Real.pi ×ˢ Set.Icc δ S) := by
  -- TODO: choose `α₀ < π` by a tube-lemma argument around the compact positive segment
  -- `Set.Icc δ S`, so both lip charts stay inside the pole-free slit domain and the meromorphic
  -- normal form becomes uniformly continuous on the resulting strip.
  sorry

/-- Helper for Remark III.6-extra-7: the explicit `π i` correction contour from the source/shifted
split tends to `0`. This is the only extra term that survives after reusing the shifted contour
normalization. -/
lemma positiveAxisBareNormalFormLipPairIntegral_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        positiveAxisKeyholeLipPairIntegral
          (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) R (1 / R))
      atTop
      (nhds 0) :=
  -- Route correction: the compact-middle interval can now be discharged abstractly by
  -- `intervalIntegral_tendsto_zero_of_compactStrip_uniformConvergence`. The first remaining
  -- blocker is upstream of that helper: we still need a theorem-local pole-free strip package
  -- around the compact positive segment `Icc δ S` so that the bare lip-pair kernel is continuous
  -- and uniformly bounded on `Icc α₀ π ×ˢ Icc δ S` before the three-piece split can close.
  sorry

/-- Helper for Remark III.6-extra-7: the bare rational inner and outer circular branches vanish
in the large-keyhole limit after the sector-arc rewrite. -/
lemma positiveAxisBareNormalFormArcPairIntegral_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        positiveAxisKeyholeArcPairIntegral
          (toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) R (1 / R))
      atTop
      (nhds 0) := by
  let G : ℂ → ℂ := toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
  let innerArcTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in ((Path.segment
        (positiveAxisKeyholeUpperAngle R (1 / R))
        (positiveAxisKeyholeLowerAngle R (1 / R))).map
          (continuous_circleMap 0 (1 / R))),
      (((G) dz) z)
  let outerArcTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in ((Path.segment
        (positiveAxisKeyholeLowerAngle R (1 / R))
        (positiveAxisKeyholeUpperAngle R (1 / R))).map
          (continuous_circleMap 0 R)),
      (((G) dz) z)
  obtain ⟨δ, M, hδ, hM, hsmall⟩ := exists_small_radius_bound_shiftedNormalForm P Q hcut'
  obtain ⟨K, R₀, hKR, hdecay⟩ := rationalEval_decay_of_degree_gap_two P Q hdeg
  have hQ : Q ≠ 0 := denominator_ne_zero_of_degree_gap_two P Q hdeg
  obtain ⟨R₁, hR₁, hlarge⟩ := exists_large_radius_denominator_ne_zero Q hQ
  let innerBound : ℝ → ℝ := fun R ↦ (M * (2 * Real.pi)) / R
  let outerBound : ℝ → ℝ := fun R ↦ (K * (2 * Real.pi)) / R
  have hinner :
      Tendsto innerArcTerm atTop (nhds 0) := by
    have hbound :
        ∀ᶠ R : ℝ in atTop, ‖innerArcTerm R‖ ≤ innerBound R := by
      filter_upwards [Filter.eventually_gt_atTop (max 1 (1 / δ))] with R hR
      have hRgt1 : 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
      have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
      have hε : 0 < 1 / R := one_div_pos.mpr hRpos
      have hεR : 1 / R < R := (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
      have hεδ : 1 / R < δ := by
        have hδinv : 1 / δ < R := lt_of_le_of_lt (le_max_right _ _) hR
        nlinarith [hδ, hδinv]
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := 1 / R) hε hεR
      -- Rewrite the inner bare arc as a sector arc and apply the small-radius uniform bound.
      rw [show innerArcTerm R =
        sectorArcIntegral
          G
          (1 / R)
          (positiveAxisKeyholeUpperAngle R (1 / R))
          (positiveAxisKeyholeLowerAngle R (1 / R)) by
            simp [innerArcTerm, G, positiveAxisCircleArc_curveIntegral_eq_sectorArcIntegral]]
      refine
        le_trans
          (sectorArcIntegral_norm_le_of_circleMap_mul_bound
            (f := G)
            (r := 1 / R)
            (θ₁ := positiveAxisKeyholeUpperAngle R (1 / R))
            (θ₂ := positiveAxisKeyholeLowerAngle R (1 / R))
            (C := M / R)
            (fun θ hθmem ↦ ?_))
          ?_
      · have hθIcc :
            θ ∈ Set.Icc
              (positiveAxisKeyholeUpperAngle R (1 / R))
              (positiveAxisKeyholeLowerAngle R (1 / R)) := by
          simpa [Set.uIcc_of_le horder.1.le] using Set.uIoc_subset_uIcc hθmem
        have hzDomain :
            circleMap 0 (1 / R) θ ∈ shiftedLogDomain :=
          circleMap_mem_shiftedLogDomain_of_keyholeMajorArc
            (hε := hε) (hεR := hεR) (hρlo := le_rfl) (hρhi := hεR.le) hθIcc
        have hzNormPos : 0 < ‖circleMap 0 (1 / R) θ‖ := by
          simpa [norm_circleMap_zero, abs_of_pos hε] using hε
        have hzNormLt : ‖circleMap 0 (1 / R) θ‖ < δ := by
          simpa [norm_circleMap_zero, abs_of_pos hε] using hεδ
        have hNF :
            ‖G (circleMap 0 (1 / R) θ)‖ ≤ M :=
          hsmall
            (circleMap 0 (1 / R) θ) hzDomain hzNormPos hzNormLt
        calc
          ‖circleMap 0 (1 / R) θ * G (circleMap 0 (1 / R) θ)‖ =
              (1 / R) * ‖G (circleMap 0 (1 / R) θ)‖ := by
                simp [G, norm_mul, norm_circleMap_zero, abs_of_pos hε, mul_comm]
          _ ≤ (1 / R) * M := by
                gcongr
          _ = M / R := by ring
      · have hlength :
            |positiveAxisKeyholeLowerAngle R (1 / R) -
                positiveAxisKeyholeUpperAngle R (1 / R)| ≤ 2 * Real.pi :=
          positiveAxisKeyhole_majorArc_angleLength_le_two_pi hε hεR
        calc
          (M / R) * |positiveAxisKeyholeLowerAngle R (1 / R) -
              positiveAxisKeyholeUpperAngle R (1 / R)| ≤
              (M / R) * (2 * Real.pi) := by
                gcongr
          _ = (M * (2 * Real.pi)) / R := by
                field_simp [hRpos.ne']
                ring
    have hlimit :
        Tendsto innerBound atTop (nhds 0) := by
      -- The inner bare arc is bounded by a fixed constant divided by `R`.
      exact tendsto_const_div_atTop_zero (M * (2 * Real.pi))
    exact squeeze_zero_norm' hbound hlimit
  have houter :
      Tendsto outerArcTerm atTop (nhds 0) := by
    have hbound :
        ∀ᶠ R : ℝ in atTop, ‖outerArcTerm R‖ ≤ outerBound R := by
      filter_upwards [Filter.eventually_gt_atTop (max 1 (max R₀ R₁))] with R hR
      have hRgt1 : 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
      have hRpos : 0 < R := lt_trans zero_lt_one hRgt1
      have hε : 0 < 1 / R := one_div_pos.mpr hRpos
      have hεR : 1 / R < R := (div_lt_iff₀ hRpos).2 (by nlinarith [hRgt1])
      have hRR₀ : R₀ < R := by
        have hmax : max R₀ R₁ < R := lt_of_le_of_lt (le_max_right _ _) hR
        exact lt_of_le_of_lt (le_max_left _ _) hmax
      have hRR₁ : R₁ < R := by
        have hmax : max R₀ R₁ < R := lt_of_le_of_lt (le_max_right _ _) hR
        exact lt_of_le_of_lt (le_max_right _ _) hmax
      have horder :=
        positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := 1 / R) hε hεR
      -- Rewrite the outer bare arc as a sector arc and transport the normal form to the literal
      -- rational function away from the denominator roots.
      rw [show outerArcTerm R =
        sectorArcIntegral
          G
          R
          (positiveAxisKeyholeLowerAngle R (1 / R))
          (positiveAxisKeyholeUpperAngle R (1 / R)) by
            simp [outerArcTerm, G, positiveAxisCircleArc_curveIntegral_eq_sectorArcIntegral]]
      refine
        le_trans
          (sectorArcIntegral_norm_le_of_circleMap_mul_bound
            (f := G)
            (r := R)
            (θ₁ := positiveAxisKeyholeLowerAngle R (1 / R))
            (θ₂ := positiveAxisKeyholeUpperAngle R (1 / R))
            (C := K / R)
            (fun θ hθmem ↦ ?_))
          ?_
      · have hθIcc :
            θ ∈ Set.Icc
              (positiveAxisKeyholeUpperAngle R (1 / R))
              (positiveAxisKeyholeLowerAngle R (1 / R)) := by
          simpa [Set.uIcc_of_le horder.1.le, Set.uIcc_comm] using Set.uIoc_subset_uIcc hθmem
        have hzDomain :
            circleMap 0 R θ ∈ shiftedLogDomain :=
          circleMap_mem_shiftedLogDomain_of_keyholeMajorArc
            (hε := hε) (hεR := hεR) (hρlo := hεR.le) (hρhi := le_rfl) hθIcc
        have hQz : Q.eval (circleMap 0 R θ) ≠ 0 := by
          apply hlarge (circleMap 0 R θ)
          simpa [norm_circleMap_zero, abs_of_pos hRpos] using hRR₁.le
        have hEq :
            G (circleMap 0 R θ) = rationalEval P Q (circleMap 0 R θ) := by
          exact rationalEval_shiftedNormalForm_eq_of_denominator_ne_zero P Q hzDomain hQz
        have hrat :
            ‖rationalEval P Q (circleMap 0 R θ)‖ ≤ K / R ^ (2 : ℕ) := by
          simpa [norm_circleMap_zero, abs_of_pos hRpos] using
            hdecay (circleMap 0 R θ) hRR₀.le
        have hscale :
            R * ‖rationalEval P Q (circleMap 0 R θ)‖ ≤ K / R := by
          calc
            R * ‖rationalEval P Q (circleMap 0 R θ)‖ ≤ R * (K / R ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hrat hRpos.le
            _ = K / R := by
              field_simp [pow_two, hRpos.ne']
              ring
        calc
          ‖circleMap 0 R θ * G (circleMap 0 R θ)‖ =
              R * ‖rationalEval P Q (circleMap 0 R θ)‖ := by
                simp [G, hEq, norm_mul, norm_circleMap_zero, abs_of_pos hRpos, mul_comm]
          _ ≤ K / R := hscale
      · have hlength :
            |positiveAxisKeyholeUpperAngle R (1 / R) -
                positiveAxisKeyholeLowerAngle R (1 / R)| ≤ 2 * Real.pi :=
          positiveAxisKeyhole_majorArc_angleLength_le_two_pi hε hεR
        calc
          (K / R) * |positiveAxisKeyholeUpperAngle R (1 / R) -
              positiveAxisKeyholeLowerAngle R (1 / R)| ≤
              (K / R) * (2 * Real.pi) := by
                gcongr
          _ = (K * (2 * Real.pi)) / R := by
                field_simp [hRpos.ne']
                ring
    have hlimit :
        Tendsto outerBound atTop (nhds 0) := by
      -- The outer bare arc is bounded by the same `1 / R` decay coming from the degree gap.
      exact tendsto_const_div_atTop_zero (K * (2 * Real.pi))
    exact squeeze_zero_norm' hbound hlimit
  have hsplit :
      (fun R : ℝ ↦ positiveAxisKeyholeArcPairIntegral G R (1 / R)) =
        fun R ↦ innerArcTerm R + outerArcTerm R := by
    funext R
    simp [positiveAxisKeyholeArcPairIntegral, innerArcTerm, outerArcTerm, G]
  -- Add the vanishing inner and outer bare arcs.
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.of_eq hsplit.symm) ?_
  simpa [innerArcTerm, outerArcTerm] using hinner.add houter

/-- Helper for Remark III.6-extra-7: the explicit `π i` correction contour from the source/shifted
split tends to `0`. This is the only extra term that survives after reusing the shifted contour
normalization. -/
lemma positiveAxisBareNormalFormKeyhole_curveIntegral_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)))
      atTop
      (nhds 0) := by
  let G : ℂ → ℂ := toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain
  have hsplit :
      (fun R : ℝ ↦
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath, ((G dz) z)) =ᶠ[atTop]
        fun R : ℝ ↦
          positiveAxisKeyholeLipPairIntegral G R (1 / R) +
            positiveAxisKeyholeArcPairIntegral G R (1 / R) := by
    -- Route correction: the geometric contour decomposition is now closed in a dedicated helper.
    filter_upwards
        [eventually_positiveAxisBareNormalFormContour_eq_lipPair_add_arcPair P Q hdeg hcut']
        with R hR
    simpa [G] using hR
  have hlip :
      Tendsto
        (fun R : ℝ ↦ positiveAxisKeyholeLipPairIntegral G R (1 / R))
        atTop
        (nhds 0) := by
    -- The bare radial lips are isolated in their own closing lemma.
    simpa [G] using positiveAxisBareNormalFormLipPairIntegral_tendsto_zero P Q hdeg hcut'
  have harc :
      Tendsto
        (fun R : ℝ ↦ positiveAxisKeyholeArcPairIntegral G R (1 / R))
        atTop
        (nhds 0) := by
    -- The circular remainder is treated independently by the bare sector-arc limit.
    simpa [G] using positiveAxisBareNormalFormArcPairIntegral_tendsto_zero P Q hdeg hcut'
  -- Replace the contour family by the grouped lip-plus-arc presentation and add the two vanishing
  -- contributions.
  refine Filter.Tendsto.congr' hsplit.symm ?_
  simpa using hlip.add harc

/-- Helper for Remark III.6-extra-7: the explicit `π i` correction contour from the source/shifted
split tends to `0`. This is the only extra term that survives after reusing the shifted contour
normalization. -/
lemma positiveAxisPiCorrectionContourTerm_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto (positiveAxisPiCorrectionContourTerm P Q) atTop (nhds 0) := by
  have hbare :
      Tendsto
        (fun R : ℝ ↦
          ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
            ((((toMeromorphicNFOn (rationalEval P Q) shiftedLogDomain) dz) z)))
        atTop
        (nhds 0) := by
    -- Route correction: the remaining analytic blocker is exactly the bare-rational keyhole limit.
    exact positiveAxisBareNormalFormKeyhole_curveIntegral_tendsto_zero P Q hdeg hcut'
  -- The correction contour is just the fixed scalar `π i` times the bare keyhole contour.
  simpa [positiveAxisPiCorrectionContourTerm] using
    Filter.Tendsto.const_mul (Real.pi * Complex.I : ℂ) hbare

/-- Helper for Remark III.6-extra-7: once the source-branch meromorphic normal form satisfies the
positive-axis isolated-residue package, the large-keyhole contour integrals are eventually
constant and therefore converge to the residue-side constant `2π i * ∑ residue`. -/
lemma sourceLogKeyhole_curveIntegral_tendsto_two_pi_I_mul_sum_residue
    (P Q : Polynomial ℂ) {s : Finset ℂ} (residue : ℂ → ℂ)
    (hhol :
      DifferentiableOn ℂ
        (sourceLogRationalNormalForm P Q)
        (shiftedLogDomain \ (↑s : Set ℂ)))
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (sourceLogRationalNormalForm P Q)
          z
          (residue z)) :
    Tendsto
      (fun R : ℝ ↦
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((sourceLogRationalNormalForm P Q) dz) z))
      atTop
      (nhds ((2 * Real.pi * Complex.I : ℂ) * s.sum residue)) := by
  have hresidue_eventually_eq :
      (fun R : ℝ ↦
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((sourceLogRationalNormalForm P Q) dz) z)) =ᶠ[atTop]
        fun _ : ℝ ↦ (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
    -- The positive-axis residue-localization package turns the contour family into an eventual
    -- constant with the expected residue sum.
    exact
      eventually_positiveAxisKeyhole_curveIntegral_eq_two_pi_I_mul_sum_residue
        residue hhol hresidue
  -- An eventually constant contour family has the same limit as that constant function.
  exact Filter.Tendsto.congr' hresidue_eventually_eq.symm tendsto_const_nhds

/-- Helper for Remark III.6-extra-7: the source-branch positive-axis keyhole contour tends to
`-(2π i)` times the improper real integral. -/
lemma sourceLogKeyhole_curveIntegral_tendsto_neg_two_pi_I_integral
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    (hcut' :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0) :
    Tendsto
      (fun R : ℝ ↦
        ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
          (((sourceLogRationalNormalForm P Q) dz) z))
      atTop
      (nhds
        ((-(2 * Real.pi * Complex.I : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
  -- Route correction: the old theorem-body blocker was the missing source-to-shifted contour
  -- normalization. The remaining proof is now reduced to the stable skeleton
  -- `source = shifted + πi correction`, followed by the shifted limit and the vanishing
  -- correction-contour limit.
  let sourceContourTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
      (((sourceLogRationalNormalForm P Q) dz) z)
  let shiftedContourTerm : ℝ → ℂ := fun R ↦
    ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
      (((shiftedLogRationalNormalForm P Q) dz) z)
  have hsplit :
      sourceContourTerm =ᶠ[atTop]
        fun R ↦ shiftedContourTerm R + positiveAxisPiCorrectionContourTerm P Q R := by
    -- The contour-level branch split is the only algebraic rewrite needed for the source theorem.
    simpa only [sourceContourTerm, shiftedContourTerm] using
      eventually_sourceLogKeyhole_curveIntegral_eq_shiftedLog_add_piCorrection P Q hdeg hcut'
  have hshifted :
      Tendsto shiftedContourTerm atTop
        (nhds
          ((-(2 * Real.pi * Complex.I : ℂ)) *
            ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
    -- Reuse the dedicated shifted-contour limit once its lip and arc remainder limits are known.
    simpa [shiftedContourTerm] using
      shiftedLogKeyhole_curveIntegral_tendsto_neg_two_pi_I_integral P Q hdeg hcut'
  have hcorr :
      Tendsto (positiveAxisPiCorrectionContourTerm P Q) atTop (nhds 0) := by
    -- The explicit `π i` correction is the only extra term created by the branch change.
    exact positiveAxisPiCorrectionContourTerm_tendsto_zero P Q hdeg hcut'
  -- Replace the source contour by the shifted-plus-correction decomposition and add the two
  -- limiting contributions.
  refine Filter.Tendsto.congr' hsplit.symm ?_
  simpa using hshifted.add hcorr

-- Semantic search found no canonical complex-analysis `Residue` operator in the local API, so the
-- source residue sum is recorded by explicit `IsolatedLocalResidueCircle` data.
/-- Remark III.6-extra-7: for a rational function `R(z) = P(z) / Q(z)` with
`deg Q ≥ deg P + 2` and no poles on the nonnegative real axis, Cartan's formula (5.4) says
`∫_0^∞ R(x) dx = -∑ Res (R(z) log z)`. In this file the source integrand `R(z) log z` is
represented on `shiftedLogDomain` by the named branch `sourceLogRationalEval P Q`, and the
right-hand side sums the explicit source-side residue data supplied by `hresidue`. -/
theorem integral_eq_neg_sum_residues_mul_log
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    {s : Finset ℂ}
    (residue : ℂ → ℂ)
    (hpoles :
      ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hcut :
      ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) (x : ℂ) < 0)
    (hresidue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (sourceLogRationalEval P Q)
          z
          (residue z)) :
    ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) =
      -s.sum residue := by
  let hpoles' : ∀ z : ℂ, meromorphicOrderAt (rationalEval P Q) z < 0 ↔ z ∈ s :=
    rationalEval_pole_iff_mem P Q hpoles
  let hcut' : ∀ x : ℝ, 0 ≤ x → ¬ meromorphicOrderAt (rationalEval P Q) (x : ℂ) < 0 :=
    rationalEval_not_pole_of_nonneg_real P Q hcut
  have hhol :
      DifferentiableOn ℂ
        (sourceLogRationalNormalForm P Q)
        (shiftedLogDomain \ (↑s : Set ℂ)) :=
    sourceLogRationalNF_differentiableOn_shiftedLogDomain_off_poles P Q hpoles'
  have hresidueNF :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle
          shiftedLogDomain
          shiftedLogDomain
          s
          (sourceLogRationalNormalForm P Q)
          z
          (residue z) :=
    sourceLogRationalNormalForm_isolatedLocalResidueCircle P Q hpoles' residue hresidue
  let F : ℝ → ℂ := fun R ↦
    ∫ᶜ z in (positiveAxisKeyhole R (1 / R)).toClosedPath.toPath,
      (((sourceLogRationalNormalForm P Q) dz) z)
  have hresidue_tendsto :
      Tendsto F atTop (nhds ((2 * Real.pi * Complex.I : ℂ) * s.sum residue)) := by
    -- The residue side is now completely packaged: the keyhole contour is eventually equal to the
    -- standard `2π i` residue sum constant.
    simpa [F] using
      sourceLogKeyhole_curveIntegral_tendsto_two_pi_I_mul_sum_residue
        P Q residue hhol hresidueNF
  have hcontour_tendsto :
      Tendsto F atTop
        (nhds
          ((-(2 * Real.pi * Complex.I : ℂ)) *
            ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) := by
    -- The contour side is reduced to the dedicated source-branch limit helper above.
    simpa [F] using
      sourceLogKeyhole_curveIntegral_tendsto_neg_two_pi_I_integral P Q hdeg hcut'
  have hlimit_eq :
      (-(2 * Real.pi * Complex.I : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume =
        (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
    -- Compare the contour-side and residue-side limits of the same keyhole family.
    exact tendsto_nhds_unique hcontour_tendsto hresidue_tendsto
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc_ne : c ≠ 0 := Complex.two_pi_I_ne_zero
  have hcancel :
      -(∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume) =
        s.sum residue := by
    have hrewrite : c *
        (-(∫ x in Set.Ioi (0 : ℝ), rationalEval P Q (x : ℂ) ∂volume)) =
          c * s.sum residue := by
      simpa [c, mul_assoc, mul_left_comm, mul_comm, neg_mul] using hlimit_eq
    exact mul_left_cancel₀ hc_ne hrewrite
  -- Negate the comparison once to put the real-axis integral on the left in the source-text form.
  simpa using congrArg Neg.neg hcancel
