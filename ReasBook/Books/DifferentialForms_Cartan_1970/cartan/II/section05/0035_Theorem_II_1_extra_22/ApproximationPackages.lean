import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»

open MeasureTheory
open scoped BigOperators

universe u

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: an exact stage decomposition
`target = stage n + error n` together with `error n → 0` forces `stage n → target`. -/
theorem tendsto_of_eq_target_add_error
    {target : ℝ} {stage error : ℕ → ℝ}
    (hstage : ∀ n, target = stage n + error n)
    (herror : Filter.Tendsto error Filter.atTop (nhds 0)) :
    Filter.Tendsto stage Filter.atTop (nhds target) := by
  have htargetMinus :
      Filter.Tendsto (fun n ↦ target - error n) Filter.atTop (nhds (target - 0)) := by
    -- Subtract the vanishing error term from the constant target sequence.
    exact tendsto_const_nhds.sub herror
  have hrewrite :
      stage = fun n ↦ target - error n := by
    -- Solve the exact stage identity for the stage term before taking limits.
    funext n
    exact eq_sub_of_add_eq (hstage n).symm
  rw [hrewrite]
  simpa using htargetMinus

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the `Q dy` half of Green's formula on
the interior of an oriented boundary region. -/
theorem coordinateHalfFormulas_onInterior_of_stageApproximation
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ} {Λ : ℕ → ι → ClosedPath ℂ} {U : ℕ → Set ℂ}
    (hStageQ :
      ∀ n,
        (∑ i, ∫ᶜ z in (Λ n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
          ∫ z in U n, dQdx z)
    (hStageP :
      ∀ n,
        (∑ i, ∫ᶜ z in (Λ n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
          -∫ z in U n, dPdy z)
    (hContourQ :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in (Λ n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)))
    (hContourP :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in (Λ n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)))
    (hSetQ :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dQdx z) Filter.atTop
        (nhds (∫ z in interior K, dQdx z)))
    (hSetP :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dPdy z) Filter.atTop
        (nhds (∫ z in interior K, dPdy z))) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        - ∫ z in interior K, dPdy z) := by
  have hSetQ_toContour :
      Filter.Tendsto (fun n ↦ ∫ z in U n, dQdx z) Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)) := by
    -- Rewrite the exact stage identities into a limit statement for the set integrals.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ hStageQ n) hContourQ
  have hSetP_toContour :
      Filter.Tendsto (fun n ↦ ∫ z in U n, dPdy z) Filter.atTop
        (nhds (-∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)) := by
    -- Rewrite the stage identity before passing to the limit on the `P dx` half-formula.
    refine Filter.Tendsto.congr' ?_ (hContourP.neg)
    refine Filter.Eventually.of_forall fun n ↦ ?_
    have hNegStage := congrArg (fun x : ℝ => -x) (hStageP n)
    simpa using hNegStage
  constructor
  · -- The two limits of the same stage set integrals must agree.
    exact tendsto_nhds_unique hSetQ_toContour hSetQ
  · -- The same uniqueness argument applies after pulling the minus sign into the contour limit.
    have hNegEq :
        -∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z =
          ∫ z in interior K, dPdy z :=
      tendsto_nhds_unique hSetP_toContour hSetP
    have hEqP := congrArg (fun x : ℝ => -x) hNegEq
    simpa using hEqP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: vanishing stage errors do not affect
the final coordinate half-formulas on `interior K`. -/
theorem coordinateHalfFormulas_onInterior_of_asymptoticStageApproximation
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ} {Λ : ℕ → ι → ClosedPath ℂ} {U : ℕ → Set ℂ}
    {eQ eP : ℕ → ℝ}
    (hStageQ :
      ∀ n,
        (∑ i, ∫ᶜ z in (Λ n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
          (∫ z in U n, dQdx z) + eQ n)
    (hStageP :
      ∀ n,
        (∑ i, ∫ᶜ z in (Λ n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
          -(∫ z in U n, dPdy z) + eP n)
    (hContourQ :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in (Λ n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)))
    (hContourP :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in (Λ n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)))
    (hSetQ :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dQdx z) Filter.atTop
        (nhds (∫ z in interior K, dQdx z)))
    (hSetP :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dPdy z) Filter.atTop
        (nhds (∫ z in interior K, dPdy z)))
    (heQ : Filter.Tendsto eQ Filter.atTop (nhds 0))
    (heP : Filter.Tendsto eP Filter.atTop (nhds 0)) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        - ∫ z in interior K, dPdy z) := by
  have hContourQ_toSet :
      Filter.Tendsto
        (fun n ↦ (∫ z in U n, dQdx z) + eQ n)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)) := by
    -- Rewrite the stage identity so the contour limit is expressed through the set side plus the
    -- vanishing error sequence.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ hStageQ n) hContourQ
  have hSetQ_withError :
      Filter.Tendsto
        (fun n ↦ (∫ z in U n, dQdx z) + eQ n)
        Filter.atTop
        (nhds ((∫ z in interior K, dQdx z) + 0)) := by
    -- The set integrals converge to the target integral and the added error converges to zero.
    exact hSetQ.add heQ
  have hContourP_toSet :
      Filter.Tendsto
        (fun n ↦ -(∫ z in U n, dPdy z) + eP n)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)) := by
    -- Apply the same rewrite to the `P dx` half-formula, now keeping the explicit minus sign.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ hStageP n) hContourP
  have hSetP_withError :
      Filter.Tendsto
        (fun n ↦ -(∫ z in U n, dPdy z) + eP n)
        Filter.atTop
        (nhds (-(∫ z in interior K, dPdy z) + 0)) := by
    -- The minus sign is handled by continuity of negation before adding the vanishing error.
    exact hSetP.neg.add heP
  constructor
  · -- The contour limit agrees with the set-integral limit because both describe the same stage
    -- sequence after the stage rewrite.
    have hEq :
        (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
          (∫ z in interior K, dQdx z) + 0 :=
      tendsto_nhds_unique hContourQ_toSet hSetQ_withError
    simpa using hEq
  · -- The same uniqueness argument closes the `P dx` half after absorbing the vanishing error.
    have hEq :
        (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
          -(∫ z in interior K, dPdy z) + 0 :=
      tendsto_nhds_unique hContourP_toSet hSetP_withError
    simpa using hEq

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once the set-side approximation data
`U`, `eQ`, and `eP` are available, the full asymptotic-stage package is obtained by keeping the
contour family constantly equal to `Γ`. -/
theorem constantContourPackage_of_setApproximation
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ} {U : ℕ → Set ℂ} {eQ eP : ℕ → ℝ}
    (hStageQ :
      ∀ n,
        (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
          (∫ z in U n, dQdx z) + eQ n)
    (hStageP :
      ∀ n,
        (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
          -(∫ z in U n, dPdy z) + eP n)
    (hSetQ :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dQdx z) Filter.atTop
        (nhds (∫ z in interior K, dQdx z)))
    (hSetP :
      Filter.Tendsto
        (fun n ↦ ∫ z in U n, dPdy z) Filter.atTop
        (nhds (∫ z in interior K, dPdy z)))
    (heQ : Filter.Tendsto eQ Filter.atTop (nhds 0))
    (heP : Filter.Tendsto eP Filter.atTop (nhds 0)) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        - ∫ z in interior K, dPdy z) := by
  -- Keep the contour family constant so only the set-side approximation remains to be supplied.
  have hContourQ :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in ((fun _ : ℕ ↦ Γ) n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)) := by
    -- The `Q dy` contour sequence is literally constant after freezing `Λ n := Γ`.
    exact
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : ℕ ↦ ∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)))
  have hContourP :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in ((fun _ : ℕ ↦ Γ) n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)) := by
    -- The same constant-family reduction works for the `P dx` contour sequence.
    exact
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : ℕ ↦ ∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)
          Filter.atTop
          (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)))
  -- The asymptotic endgame now consumes the set-side approximation package directly.
  exact
    coordinateHalfFormulas_onInterior_of_asymptoticStageApproximation
      (Γ := Γ) (Λ := fun _ i ↦ Γ i) (U := U) (eQ := eQ) (eP := eP)
      (hStageQ := fun n ↦ by simpa using hStageQ n)
      (hStageP := fun n ↦ by simpa using hStageP n)
      hContourQ hContourP hSetQ hSetP heQ heP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: an existential set-approximation
package already suffices to close the two interior coordinate half-formulas. -/
theorem coordinateHalfFormulas_onInterior_of_setApproximation
    {ι : Type u} [Fintype ι] {K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ}
    (hApprox :
      ∃ U : ℕ → Set ℂ,
        ∃ eQ : ℕ → ℝ,
          ∃ eP : ℕ → ℝ,
            (∀ n,
              ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
                  (∫ z in U n, dQdx z) + eQ n) ∧
                ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
                  -(∫ z in U n, dPdy z) + eP n)) ∧
            Filter.Tendsto
              (fun n ↦ ∫ z in U n, dQdx z)
              Filter.atTop
              (nhds (∫ z in interior K, dQdx z)) ∧
            Filter.Tendsto
              (fun n ↦ ∫ z in U n, dPdy z)
              Filter.atTop
              (nhds (∫ z in interior K, dPdy z)) ∧
            Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
            Filter.Tendsto eP Filter.atTop (nhds 0)) :
    ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) z) =
        ∫ z in interior K, dQdx z) ∧
      ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) z) =
        - ∫ z in interior K, dPdy z) := by
  rcases hApprox with ⟨U, eQ, eP, hStage, hSetQ, hSetP, heQ, heP⟩
  -- Unpack the approximation package and feed it into the constant-contour endgame.
  exact
    constantContourPackage_of_setApproximation
      (Γ := Γ) (U := U) (eQ := eQ) (eP := eP)
      (hStageQ := fun n ↦ (hStage n).1)
      (hStageP := fun n ↦ (hStage n).2)
      hSetQ hSetP heQ heP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: if `U n` stays inside `interior K`
and the omitted volume `interior K \ U n` tends to zero, then the set integrals over `U n`
converge to the set integral over `interior K`. -/
theorem setIntegral_tendsto_of_volumeInteriorDiff_tendsto_zero
    {K : Set ℂ} {f : ℂ → ℝ} {U : ℕ → Set ℂ}
    (hInt : IntegrableOn f (interior K))
    (hU_subset : ∀ n, U n ⊆ interior K)
    (hU_meas : ∀ n, MeasurableSet (U n))
    (hDiff :
      Filter.Tendsto (fun n ↦ volume (interior K \ U n)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ ∫ z in U n, f z) Filter.atTop (nhds (∫ z in interior K, f z)) := by
  have hDiff' :
      Filter.Tendsto
        (fun n ↦ (volume.restrict (interior K)) (interior K \ U n))
        Filter.atTop (nhds 0) := by
    -- Move the vanishing-volume hypothesis to the restricted measure on `interior K`.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall ?_) hDiff
    intro n
    have hsubset : interior K \ U n ⊆ interior K := by
      intro z hz
      exact hz.1
    have hEq :
        (volume.restrict (interior K)) (interior K \ U n) =
          volume (interior K \ U n) := by
      calc
        (volume.restrict (interior K)) (interior K \ U n) =
            volume ((interior K \ U n) ∩ interior K) := by
          simpa using
            (Measure.restrict_apply' (μ := volume) (s := interior K)
              (t := interior K \ U n) isOpen_interior.measurableSet)
        _ = volume (interior K \ U n) := by
          rw [Set.inter_eq_left.mpr hsubset]
    simpa using hEq.symm
  have hZeroRestricted :
      Filter.Tendsto
        (fun n ↦ ∫ z in interior K \ U n, f z ∂(volume.restrict (interior K)))
        Filter.atTop (nhds 0) :=
    hInt.tendsto_setIntegral_nhds_zero hDiff'
  have hZero :
      Filter.Tendsto (fun n ↦ ∫ z in interior K \ U n, f z) Filter.atTop (nhds 0) := by
    -- The omitted-set integrals are the same whether viewed in the ambient measure or in the
    -- restriction to `interior K`.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall ?_) hZeroRestricted
    intro n
    have hsubset : interior K \ U n ⊆ interior K := by
      intro z hz
      exact hz.1
    have hmeasDiff : MeasurableSet (interior K \ U n) :=
      isOpen_interior.measurableSet.diff (hU_meas n)
    have hEq :
        ∫ z in interior K \ U n, f z ∂(volume.restrict (interior K)) =
          ∫ z in interior K \ U n, f z := by
      calc
        ∫ z in interior K \ U n, f z ∂(volume.restrict (interior K)) =
            ∫ z in (interior K \ U n) ∩ interior K, f z := by
          rw [Measure.restrict_restrict hmeasDiff]
        _ = ∫ z in interior K \ U n, f z := by
          rw [Set.inter_eq_left.mpr hsubset]
    simpa using hEq
  have hSub :
      Filter.Tendsto
        (fun n ↦ (∫ z in interior K, f z) - ∫ z in U n, f z)
        Filter.atTop (nhds 0) := by
    -- The difference between the target integral and the stage integral is exactly the omitted-set
    -- integral.
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall ?_) hZero
    intro n
    simpa using MeasureTheory.setIntegral_diff (hU_meas n) hInt (hU_subset n)
  have hMain :
      Filter.Tendsto
        (fun n ↦ (∫ z in interior K, f z) - ((∫ z in interior K, f z) - ∫ z in U n, f z))
        Filter.atTop (nhds ((∫ z in interior K, f z) - 0)) :=
    tendsto_const_nhds.sub hSub
  have hEqFun :
      (fun n ↦ ∫ z in U n, f z) =
        (fun n ↦ (∫ z in interior K, f z) - ((∫ z in interior K, f z) - ∫ z in U n, f z)) := by
    -- Rearranging the real-valued difference recovers the original stage integral.
    funext n
    ring
  rw [hEqFun]
  simpa using hMain

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: once an internal contour family `Λ n`
has exact stage formulas and its contour sums converge to those of `Γ`, the discrepancy can be
recorded as vanishing scalar errors for the constant contour family `Γ`. -/
theorem constantContourErrors_of_asymptoticStageApproximation
    {ι : Type u} [Fintype ι] {Γ : ι → ClosedPath ℂ}
    {P Q dPdy dQdx : ℂ → ℝ} {Λ : ℕ → ι → ClosedPath ℂ} {U : ℕ → Set ℂ}
    (hStageQ :
      ∀ n,
        (∑ i, ∫ᶜ z in (Λ n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
          ∫ z in U n, dQdx z)
    (hStageP :
      ∀ n,
        (∑ i, ∫ᶜ z in (Λ n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
          -∫ z in U n, dPdy z)
    (hContourQ :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in (Λ n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z)))
    (hContourP :
      Filter.Tendsto
        (fun n ↦ ∑ i, ∫ᶜ z in (Λ n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z))) :
    ∃ eQ : ℕ → ℝ,
      ∃ eP : ℕ → ℝ,
        (∀ n,
          ((∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z) =
              (∫ z in U n, dQdx z) + eQ n) ∧
            ((∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z) =
              -(∫ z in U n, dPdy z) + eP n)) ∧
        Filter.Tendsto eQ Filter.atTop (nhds 0) ∧
        Filter.Tendsto eP Filter.atTop (nhds 0) := by
  let contourQ : ℝ :=
    ∑ i, ∫ᶜ z in (Γ i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z
  let contourP : ℝ :=
    ∑ i, ∫ᶜ z in (Γ i).toPath, (P dx+(0 : ℂ → ℝ) dy) z
  let stageContourQ : ℕ → ℝ := fun n ↦
    ∑ i, ∫ᶜ z in (Λ n i).toPath, (((0 : ℂ → ℝ) dx+Q dy)) z
  let stageContourP : ℕ → ℝ := fun n ↦
    ∑ i, ∫ᶜ z in (Λ n i).toPath, (P dx+(0 : ℂ → ℝ) dy) z
  let eQ : ℕ → ℝ := fun n ↦ contourQ - stageContourQ n
  let eP : ℕ → ℝ := fun n ↦ contourP - stageContourP n
  refine ⟨eQ, eP, ?_, ?_, ?_⟩
  · intro n
    constructor
    · -- Replace the internal contour sum by the exact stage set integral and keep the remaining
      -- contour discrepancy as the explicit error term for `Γ`.
      dsimp [eQ, contourQ, stageContourQ]
      rw [hStageQ n]
      ring
    · -- The same discrepancy packaging works for the `P dx` half-formula.
      dsimp [eP, contourP, stageContourP]
      rw [hStageP n]
      ring
  · -- The `Q dy` error tends to zero because the internal contour sums converge to the target
    -- contour sum of `Γ`.
    have hStageContourQ :
        Filter.Tendsto stageContourQ Filter.atTop (nhds contourQ) := by
      simpa [stageContourQ, contourQ] using hContourQ
    have hErrorQ :
        Filter.Tendsto (fun n ↦ contourQ - stageContourQ n) Filter.atTop
          (nhds (contourQ - contourQ)) := by
      exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ ↦ contourQ) Filter.atTop (nhds contourQ)).sub hStageContourQ
    simpa [eQ] using hErrorQ
  · -- The same limit argument turns the `P dx` contour discrepancy into a vanishing error.
    have hStageContourP :
        Filter.Tendsto stageContourP Filter.atTop (nhds contourP) := by
      simpa [stageContourP, contourP] using hContourP
    have hErrorP :
        Filter.Tendsto (fun n ↦ contourP - stageContourP n) Filter.atTop
          (nhds (contourP - contourP)) := by
      exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ ↦ contourP) Filter.atTop (nhds contourP)).sub hStageContourP
    simpa [eP] using hErrorP

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: conjugating a closed loop by a
connector path preserves its contour integral. -/
theorem curveIntegral_conjugateLoop_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {z₀ z₁ : ℂ} {ω : ℂ → ℂ →L[ℝ] F} {ρ : Path z₀ z₁} {γ : Path z₁ z₁}
    (hρ : CurveIntegrable ω ρ) (hγ : CurveIntegrable ω γ) :
    ∫ᶜ ζ in (ρ.trans γ).trans ρ.symm, ω ζ = ∫ᶜ ζ in γ, ω ζ := by
  -- Split the rooted loop into the forward transport, the closed loop, and the return leg.
  calc
    ∫ᶜ ζ in (ρ.trans γ).trans ρ.symm, ω ζ =
        ∫ᶜ ζ in ρ.trans γ, ω ζ + ∫ᶜ ζ in ρ.symm, ω ζ := by
      rw [curveIntegral_trans (CurveIntegrable.trans hρ hγ) hρ.symm]
    _ = (∫ᶜ ζ in ρ, ω ζ + ∫ᶜ ζ in γ, ω ζ) + ∫ᶜ ζ in ρ.symm, ω ζ := by
      rw [curveIntegral_trans hρ hγ]
    _ = (∫ᶜ ζ in ρ, ω ζ + ∫ᶜ ζ in γ, ω ζ) + (-∫ᶜ ζ in ρ, ω ζ) := by
      rw [curveIntegral_symm]
    _ = ∫ᶜ ζ in γ, ω ζ := by
      abel

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a finite family of
connector-conjugated boundary loops can be accumulated into one rooted loop without changing the
total contour sum. -/
theorem existsRootedLoopWithSameIntegral
    {ι : Type u} (s : Finset ι) {z0 : ℂ}
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : ℂ → ℂ →L[ℝ] F}
    (hρ_piece : ∀ i ∈ s, (ρ i).IsPiecewiseDifferentiable)
    (hΓ_piece : ∀ i ∈ s, ((Γ i).toPath).IsPiecewiseDifferentiable)
    (hρ_int : ∀ i ∈ s, CurveIntegrable ω (ρ i))
    (hΓ_int : ∀ i ∈ s, CurveIntegrable ω ((Γ i).toPath)) :
    ∃ γ : Path z0 z0,
      γ.IsPiecewiseDifferentiable ∧
      CurveIntegrable ω γ ∧
      (∫ᶜ z in γ, ω z = s.sum fun i => ∫ᶜ z in (Γ i).toPath, ω z) := by
  classical
  revert hρ_piece hΓ_piece hρ_int hΓ_int
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _ _
    -- The empty family contributes the constant rooted loop and the empty contour sum.
    refine ⟨Path.refl z0, Path.isPiecewiseDifferentiable_refl z0, CurveIntegrable.refl ω z0, ?_⟩
    simp
  · intro i s hi ih hρ_piece hΓ_piece hρ_int hΓ_int
    have hρs : ∀ j ∈ s, (ρ j).IsPiecewiseDifferentiable := by
      intro j hj
      exact hρ_piece j (by simp [hj])
    have hΓs : ∀ j ∈ s, ((Γ j).toPath).IsPiecewiseDifferentiable := by
      intro j hj
      exact hΓ_piece j (by simp [hj])
    have hρs_int : ∀ j ∈ s, CurveIntegrable ω (ρ j) := by
      intro j hj
      exact hρ_int j (by simp [hj])
    have hΓs_int : ∀ j ∈ s, CurveIntegrable ω ((Γ j).toPath) := by
      intro j hj
      exact hΓ_int j (by simp [hj])
    rcases ih hρs hΓs hρs_int hΓs_int with ⟨γs, hγs_piece, hγs_int, hγs_eq⟩
    have hρi_piece : (ρ i).IsPiecewiseDifferentiable := hρ_piece i (by simp)
    have hΓi_piece : ((Γ i).toPath).IsPiecewiseDifferentiable := hΓ_piece i (by simp)
    have hρi_int : CurveIntegrable ω (ρ i) := hρ_int i (by simp)
    have hΓi_int : CurveIntegrable ω ((Γ i).toPath) := hΓ_int i (by simp)
    let γ : Path z0 z0 := γs.trans ((ρ i).trans ((Γ i).toPath.trans (ρ i).symm))
    have hγ_piece : γ.IsPiecewiseDifferentiable := by
      -- Appending one connector-conjugated loop preserves piecewise differentiability.
      dsimp [γ]
      exact hγs_piece.trans (hρi_piece.trans (hΓi_piece.trans hρi_piece.symm))
    have hγ_int : CurveIntegrable ω γ := by
      -- The same concatenation preserves curve integrability.
      dsimp [γ]
      exact hγs_int.trans (hρi_int.trans (hΓi_int.trans hρi_int.symm))
    have hconj :
        ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z =
          ∫ᶜ z in (Γ i).toPath, ω z := by
      -- Expand the connector-conjugated loop and cancel the reverse connector contribution.
      calc
        ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z =
            ∫ᶜ z in ρ i, ω z + ∫ᶜ z in ((Γ i).toPath.trans (ρ i).symm), ω z := by
          simpa using curveIntegral_trans hρi_int (hΓi_int.trans hρi_int.symm)
        _ = ∫ᶜ z in ρ i, ω z +
              (∫ᶜ z in (Γ i).toPath, ω z + ∫ᶜ z in (ρ i).symm, ω z) := by
          exact congrArg (fun t => ∫ᶜ z in ρ i, ω z + t) (curveIntegral_trans hΓi_int hρi_int.symm)
        _ = ∫ᶜ z in (Γ i).toPath, ω z := by
          rw [curveIntegral_symm]
          abel
    refine ⟨γ, hγ_piece, hγ_int, ?_⟩
    -- Compare the new rooted loop with the previous rooted loop and the new conjugated summand.
    calc
      ∫ᶜ z in γ, ω z =
          ∫ᶜ z in γs, ω z + ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z := by
        simpa [γ] using
          curveIntegral_trans hγs_int (hρi_int.trans (hΓi_int.trans hρi_int.symm))
      _ = s.sum (fun j => ∫ᶜ z in (Γ j).toPath, ω z) + ∫ᶜ z in (Γ i).toPath, ω z := by
        rw [hγs_eq, hconj]
      _ = (insert i s).sum (fun j => ∫ᶜ z in (Γ j).toPath, ω z) := by
        simp [Finset.sum_insert, hi, add_comm]
