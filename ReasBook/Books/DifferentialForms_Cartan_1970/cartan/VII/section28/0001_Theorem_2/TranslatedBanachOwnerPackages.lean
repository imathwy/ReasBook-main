import DifferentialForms_Cartan_1970.cartan.VII.section28.«0001_Theorem_2».TranslatedMixedCoefficientOwners

open Filter
open Set

open scoped Topology

/-- Helper for Cartan section28 0001_Theorem_2: after packaging the translated Taylor owner into a
common Banach-valued owner, evaluating the exact Banach formal solution at a frozen parameter
recovers the canonical scalar formal solution for that slice. -/
theorem translatedCommonBanachOwner_evalEqLiftedSliceOwner
    {k j : ℕ} {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j)
    {Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ)}
    {R : ENNReal}
    (hQtrBall :
      HasFPowerSeriesOnBall
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        Qtr
        ((0 : ℂ), (0 : Fin k → ℂ), 0)
        R)
    {ρu : NNReal}
    (hρupos : 0 < ρu)
    (hρult : (ρu : ENNReal) < R)
    {u : ℂ}
    (hu : ‖u‖ < ρu)
    {Qslice0 : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ)}
    (hQlifted :
      let L := weightedParameterEvalCLM ρu u hu
      HasFPowerSeriesAt
        (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
          F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
        (Qslice0.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
        ((0 : ℂ), 0)) :
    let QB :
      FormalMultilinearSeries
        ℂ
        (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
        (lp (fun _ : ℕ => Fin k → ℂ) 1) :=
      fun m ↦ translatedQtrMixedCoeffToLp Qtr hρupos (lt_of_lt_of_le hρult hQtrBall.r_le) m
    let L := weightedParameterEvalCLM ρu u hu
    PowerSeries.mk (fun m ↦ L ((formalSeriesSolutionSeries QB).coeff m)) =
      formalRecenteredVectorSolutionSeries Qslice0 := by
  intro QB L
  have hQleft :
      HasFPowerSeriesAt
        (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
          F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
        ((Qtr.changeOrigin ((0 : ℂ), (0 : Fin k → ℂ), u)).compContinuousLinearMap
          ((ContinuousLinearMap.fst ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)).prod
            (((L.comp (ContinuousLinearMap.snd ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1))).prod
              (0 : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] ℂ)))))
        ((0 : ℂ), 0) := by
    -- The translated Taylor owner already yields an explicit lifted owner after shifting the scalar
    -- parameter center to `u` and freezing the last coordinate.
    simpa [L] using
      translatedLiftedSliceOwner_changeOrigin_fromQtr
        (F := F) (t0 := t0) (r := r) (Qtr := Qtr) (R := R)
        hQtrBall hρult (u := u) hu
  have hQlifted' :
      HasFPowerSeriesAt
        (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
          F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
        (Qslice0.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
        ((0 : ℂ), 0) := by
    simpa [L] using hQlifted
  have hExplicitEqLQB :
      ((Qtr.changeOrigin ((0 : ℂ), (0 : Fin k → ℂ), u)).compContinuousLinearMap
        ((ContinuousLinearMap.fst ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)).prod
          (((L.comp (ContinuousLinearMap.snd ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1))).prod
            (0 : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] ℂ))))) =
        L.compFormalMultilinearSeries QB := by
    funext m
    ext v x
    let P : FormalMultilinearSeries ℂ ℂ (Fin k → ℂ) := translatedQtrMixedCoeffSeries Qtr m v
    have huP : (‖u‖₊ + ‖(0 : ℂ)‖₊ : ENNReal) < P.radius := by
      have hu' : (‖u‖₊ : ENNReal) < P.radius := by
        exact lt_of_lt_of_le (by exact_mod_cast hu)
          (le_radius_translatedQtrMixedCoeffSeries (Qtr := Qtr) hρupos
            (lt_of_lt_of_le hρult hQtrBall.r_le) m v)
      simpa using hu'
    have hLeft :
        (((Qtr.changeOrigin ((0 : ℂ), (0 : Fin k → ℂ), u)).compContinuousLinearMap
              ((ContinuousLinearMap.fst ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)).prod
                (((L.comp (ContinuousLinearMap.snd ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1))).prod
                  (0 : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] ℂ))))) m)
          v x =
        P.sum u x := by
      calc
        (((Qtr.changeOrigin ((0 : ℂ), (0 : Fin k → ℂ), u)).compContinuousLinearMap
                ((ContinuousLinearMap.fst ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)).prod
                  (((L.comp (ContinuousLinearMap.snd ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1))).prod
                    (0 : (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1) →L[ℂ] ℂ))))) m)
            v x =
            ((P.changeOrigin u).sum 0) x := by
              simp [P, translatedQtrMixedCoeffSeries, translatedQtrMixedCoeffMap_apply]
        _ = P.sum u x := by
              simpa [add_comm] using congrArg (fun w : Fin k → ℂ ↦ w x)
                (FormalMultilinearSeries.changeOrigin_eval (p := P) huP)
    rw [ContinuousLinearMap.compFormalMultilinearSeries_apply']
    rw [weightedParameterEvalCLM_translatedQtrMixedCoeffToLp_eq_sum
      (Qtr := Qtr) hρupos (lt_of_lt_of_le hρult hQtrBall.r_le) (hu := hu) m v]
    simpa [P] using hLeft
  have hQleftQB :
      HasFPowerSeriesAt
        (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
          F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
        (L.compFormalMultilinearSeries QB)
        ((0 : ℂ), 0) := by
    rw [← hExplicitEqLQB]
    exact hQleft
  have hQBRadius : 0 < QB.radius := by
    simpa [QB] using
      translatedCommonBanachOwner_radiusPos
        (Qtr := Qtr) hρupos (lt_of_lt_of_le hρult hQtrBall.r_le)
  have hSeriesRadius : 0 < (formalSeriesSolutionSeries QB).radius :=
    formalSeriesSolutionSeries_radiusPos_of_positiveOwnerRadius (Q := QB) hQBRadius
  have hSeriesBall :
      HasFPowerSeriesOnBall
        (formalSeriesSolutionSeries QB).sum
        (formalSeriesSolutionSeries QB)
        0
        (formalSeriesSolutionSeries QB).radius :=
    (formalSeriesSolutionSeries QB).hasFPowerSeriesOnBall hSeriesRadius
  have hSeriesAt :
      HasFPowerSeriesAt
        (formalSeriesSolutionSeries QB).sum
        (oneVariableSeriesOfCoefficients fun n ↦ (formalSeriesSolutionSeries QB).coeff n)
        0 := by
    convert hSeriesBall.hasFPowerSeriesAt using 1
    exact
      (formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients
        (formalSeriesSolutionSeries QB)).symm
  have hSeriesZero : (formalSeriesSolutionSeries QB).sum 0 = 0 := by
    have hcoeffZero' :
        (formalSeriesSolutionSeries QB 0) 0 = (formalSeriesSolutionSeries QB).coeff 0 := by
      simpa [ContinuousMultilinearMap.mkPiRing_apply] using
        congrArg (fun f => f 0)
          (FormalMultilinearSeries.mkPiRing_coeff_eq (formalSeriesSolutionSeries QB) 0).symm
    exact
      (hSeriesBall.coeff_zero 0).symm.trans <|
        hcoeffZero'.trans (formalSeriesSolutionSeries_coeff_zero (Q := QB))
  -- The direct Banach package and the lifted scalar slice owner represent the same germ after
  -- composing with the exact Banach solution curve, so the scalar formal solution follows from
  -- the shared-curve uniqueness bridge.
  refine
    evaluatedBanachFormalSolution_eq_formalRecenteredVectorSolution
      (L := L) (Q := QB) (Qslice := Qslice0) ?_
  intro m
  exact
    recenteredComposedCoeffBanach_eval_eq_of_sharedCurveOwner
      (f := fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
        F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
      (L := L)
      (QB := QB)
      (Qslice := Qslice0)
      (u := (formalSeriesSolutionSeries QB).sum)
      (a := fun n ↦ (formalSeriesSolutionSeries QB).coeff n)
      hSeriesZero
      hSeriesAt
      hQleftQB
      hQlifted'
      m

/-- Helper for Cartan section28 0001_Theorem_2: the remaining owner-level bridge is to package
the translated Taylor owner `Qtr` into one Banach-valued owner whose weighted evaluations recover
all frozen scalar slice owners on the chosen parameter ball. -/
theorem translatedCommonBanachOwnerPackageFromQtr
    {k j : ℕ} {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr' : Set ℂ}
    {Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ)}
    {R : ENNReal}
    (hQtrBall :
      HasFPowerSeriesOnBall
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        Qtr
        ((0 : ℂ), (0 : Fin k → ℂ), 0)
        R)
    {ρu : NNReal}
    (hρult : (ρu : ENNReal) < R)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu) :
    ∃ QB :
      FormalMultilinearSeries
        ℂ
        (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
        (lp (fun _ : ℕ => Fin k → ℂ) 1),
      0 < QB.radius ∧
      ∀ u, ∀ hu : u ∈ Vr',
        ∃ Qslice0 : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update t0 r (t0 r + u)))
            Qslice0
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          let L := weightedParameterEvalCLM ρu u (hVr'norm u hu)
          PowerSeries.mk (fun m ↦ L ((formalSeriesSolutionSeries QB).coeff m)) =
            formalRecenteredVectorSolutionSeries Qslice0 := by
  -- Route correction: the remaining proof work is now isolated to the support API that converts
  -- the translated scalar-parameter Taylor owner into one common Banach owner.
  have hliftedSlice :
      ∀ u, ∀ hu : u ∈ Vr',
        ∃ Qslice0 : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update t0 r (t0 r + u)))
            Qslice0
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          let L := weightedParameterEvalCLM ρu u (hVr'norm u hu)
          HasFPowerSeriesAt
            (fun p : ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1 ↦
              F p.1 (L p.2) (Function.update t0 r (t0 r + u)))
            (Qslice0.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
            ((0 : ℂ), 0) := by
    intro u hu
    -- Each frozen translated scalar slice already has a genuine two-variable owner, and the
    -- weighted evaluation map transports it to an explicit owner on `ℂ × lp`.
    exact
      translatedLiftedSliceOwner_fromQtr
        (F := F) (t0 := t0) (r := r) (Qtr := Qtr) (R := R)
        hQtrBall hρult (hVr'norm u hu)
  by_cases hEmpty : Vr' = ∅
  · rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hQtrBall.r_pos with ⟨ρ0, hρ0pos, hρ0lt⟩
    have hρ0pos' : 0 < ρ0 := by
      simpa [NNReal.coe_pos] using hρ0pos
    have hρ0ltQtr : (ρ0 : ENNReal) < Qtr.radius := by
      exact lt_of_lt_of_le hρ0lt hQtrBall.r_le
    let QB :
        FormalMultilinearSeries
          ℂ
          (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
          (lp (fun _ : ℕ => Fin k → ℂ) 1) :=
      fun m ↦ translatedQtrMixedCoeffToLp Qtr hρ0pos' hρ0ltQtr m
    refine ⟨QB, ?_, ?_⟩
    · -- In the empty-parameter branch, any positive-radius Banach package suffices because the
      -- evaluation clause is vacuous.
      simpa [QB] using translatedCommonBanachOwner_radiusPos (Qtr := Qtr) hρ0pos' hρ0ltQtr
    · intro u hu
      exfalso
      simpa [hEmpty] using hu
  · have hVr'nonempty : Set.Nonempty Vr' := by
      by_contra hVr'empty
      apply hEmpty
      ext u
      simp only [Set.mem_empty_iff_false]
      constructor
      · intro hu
        exact (hVr'empty ⟨u, hu⟩).elim
      · intro hu
        exact False.elim hu
    rcases hVr'nonempty with ⟨u0, hu0⟩
    have hρuposReal : 0 < (ρu : ℝ) := by
      exact lt_of_le_of_lt (norm_nonneg u0) (hVr'norm u0 hu0)
    have hρupos : 0 < ρu := by
      exact_mod_cast hρuposReal
    have hρultQtr : (ρu : ENNReal) < Qtr.radius := by
      exact lt_of_lt_of_le hρult hQtrBall.r_le
    let QB :
        FormalMultilinearSeries
          ℂ
          (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
          (lp (fun _ : ℕ => Fin k → ℂ) 1) :=
      fun m ↦ translatedQtrMixedCoeffToLp Qtr hρupos hρultQtr m
    refine ⟨QB, ?_, ?_⟩
    · -- A nonempty parameter ball yields `0 < ρu`, so the direct Banach package inherits a
      -- positive radius from `translatedCommonBanachOwner_radiusPos`.
      simpa [QB] using translatedCommonBanachOwner_radiusPos (Qtr := Qtr) hρupos hρultQtr
    · intro u hu
      rcases hliftedSlice u hu with ⟨Qslice0, hQslice0At, hQlifted⟩
      refine ⟨Qslice0, hQslice0At, ?_⟩
      -- Evaluate the exact Banach formal solution at the frozen parameter and identify the
      -- resulting scalar formal solution directly.
      simpa [QB] using
        translatedCommonBanachOwner_evalEqLiftedSliceOwner
          (F := F) (t0 := t0) (r := r) (Qtr := Qtr) (R := R)
          hQtrBall hρupos hρult (u := u) (Qslice0 := Qslice0) (hu := hVr'norm u hu)
          hQlifted
