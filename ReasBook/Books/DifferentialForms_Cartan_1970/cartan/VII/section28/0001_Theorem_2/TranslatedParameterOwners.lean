import DifferentialForms_Cartan_1970.VII.section27.«0001_Theorem_I»
import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».BanachFormalSeries
import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».LocalHolomorphicSystems
import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».TranslatedParameterAnalysis
import Mathlib

open Filter
open Set

open scoped Topology

/-- Helper for Cartan section28 0001_Theorem_2: once a Banach-valued translated owner is fixed,
evaluating its exact formal solution along a scalar parameter slice recovers the canonical
section-27 scalar formal solution for the evaluated owner. -/
theorem evaluatedBanachFormalSolution_eq_formalRecenteredVectorSolution
    {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] (Fin k → ℂ))
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E)
    (Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ))
    (hcoeff :
      ∀ m,
        L
            (recenteredComposedCoeffBanach Q
              (fun k ↦ (formalSeriesSolutionSeries Q).coeff k)
              m) =
          recenteredComposedCoeff Qslice
            (fun k ↦ L ((formalSeriesSolutionSeries Q).coeff k))
            m) :
    PowerSeries.mk (fun m ↦ L ((formalSeriesSolutionSeries Q).coeff m)) =
      formalRecenteredVectorSolutionSeries Qslice := by
  let ψ : PowerSeries (Fin k → ℂ) := PowerSeries.mk fun m ↦ L ((formalSeriesSolutionSeries Q).coeff m)
  have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
    -- The evaluated scalar series inherits the vanishing constant term of the Banach solution.
    simp [ψ, formalSeriesSolutionSeries_coeff_zero]
  have hψrec :
      ∀ m,
        PowerSeries.coeff (m + 1) ψ =
          ((m + 1 : ℂ)⁻¹) •
            recenteredComposedCoeff Qslice (fun k ↦ PowerSeries.coeff k ψ) m := by
    intro m
    -- Evaluate the Banach coefficient recursion and rewrite the right-hand side through the
    -- supplied scalar slice recursion.
    calc
      PowerSeries.coeff (m + 1) ψ
          = L ((formalSeriesSolutionSeries Q).coeff (m + 1)) := by
              simp [ψ]
      _ =
          L
            (((m + 1 : ℂ)⁻¹) •
              recenteredComposedCoeffBanach Q
                (fun k ↦ (formalSeriesSolutionSeries Q).coeff k)
                m) := by
                  rw [formalSeriesSolutionSeries_next_coeff_eq]
      _ =
          ((m + 1 : ℂ)⁻¹) •
            L
              (recenteredComposedCoeffBanach Q
                (fun k ↦ (formalSeriesSolutionSeries Q).coeff k)
                m) := by
                  simp
      _ =
          ((m + 1 : ℂ)⁻¹) •
            recenteredComposedCoeff
              Qslice
              (fun k ↦ L ((formalSeriesSolutionSeries Q).coeff k))
              m := by
                simpa using
                  congrArg
                    (fun v : Fin k → ℂ ↦ ((m + 1 : ℂ)⁻¹) • v)
                    (hcoeff m)
      _ =
          ((m + 1 : ℂ)⁻¹) •
            recenteredComposedCoeff Qslice (fun k ↦ PowerSeries.coeff k ψ) m := by
                congr
                funext k
                simp [ψ]
  -- The section-27 uniqueness theorem identifies the evaluated scalar recursion with the canonical
  -- formal solution of the evaluated owner.
  rcases existsUnique_formal_series_solution_for_recentered_multilinear_system
      Qslice with ⟨ξ, hξ, hξuniq⟩
  have hψeq : ψ = ξ := hξuniq ψ ⟨hψ0, hψrec⟩
  have hξeq :
      formalRecenteredVectorSolutionSeries Qslice = ξ :=
    hξuniq _ (formalRecenteredVectorSolutionSeries_isSolution (Q := Qslice))
  exact hψeq.trans hξeq.symm

/-- Helper for Cartan section28 0001_Theorem_2: once an analytic comparison family is available
for the translated scalar system, slice-wise uniqueness identifies it with the original
translated slice on the whole preconnected `x`-domain. -/
theorem eqOn_translatedCoordinateSlice_of_comparisonFamily
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Ux : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ ψtr : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hUxPreconnected : IsPreconnected Ux)
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr : Set ℂ}
    (hVrmap : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr Vx)
    (hψsol :
      ∀ u ∈ Vr,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          Ux
          (fun x ↦ ψtr (x, Function.update t0 r (t0 r + u)))) :
    Set.EqOn
      (fun p : ℂ × ℂ ↦ ψtr (p.1, Function.update t0 r (t0 r + p.2)))
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (Ux ×ˢ Vr) := by
  intro p hp
  let τ : ℂ → Fin j → ℂ := fun u ↦ Function.update t0 r (t0 r + u)
  let Ωp : Set (ℂ × (Fin k → ℂ)) :=
    {q : ℂ × (Fin k → ℂ) |
      AnalyticAt ℂ (fun z : ℂ × (Fin k → ℂ) ↦ F z.1 z.2 (τ p.2)) q}
  have hΩp : IsOpen Ωp := isOpen_analyticAt ℂ (fun z : ℂ × (Fin k → ℂ) ↦ F z.1 z.2 (τ p.2))
  have h0Ωp : ((0 : ℂ), (0 : Fin k → ℂ)) ∈ Ωp := by
    -- The translated parameter stays inside `Vx`, so the scalar slice is analytic at the origin.
    exact analyticAt_slice_rhs_of_mem hF (zero_section_mem_coeff_domain hsol (hVrmap hp.2))
  have hsliceφ :
      IsHolomorphicSystemSolutionOn
        Ωp
        (fun x y ↦ F x y (τ p.2))
        0
        0
        Ux
        (fun x ↦ φ (x, τ p.2)) := by
    have hbase := coordinateUpdateOneParamHypotheses (Vx := Vx) (hsol := hsol)
      (r := r) (t0 := t0) (u := p.2) (hVrmap hp.2)
    refine hbase.restrict hbase.isOpen hbase.mem (fun _ hx ↦ hx) ?_
    intro x hx
    exact analyticAt_slice_rhs_of_mem hF (hbase.mapsTo hx)
  have hsliceψ :
      IsHolomorphicSystemSolutionOn
        Ωp
        (fun x y ↦ F x y (τ p.2))
        0
        0
        Ux
        (fun x ↦ ψtr (x, τ p.2)) := by
    have hbase := hψsol p.2 hp.2
    refine hbase.restrict hbase.isOpen hbase.mem (fun _ hx ↦ hx) ?_
    intro x hx
    exact analyticAt_slice_rhs_of_mem hF (hbase.mapsTo hx)
  have hFΩp : AnalyticOnNhd ℂ (fun q : ℂ × (Fin k → ℂ) ↦ F q.1 q.2 (τ p.2)) Ωp := by
    intro q hq
    exact hq
  -- The two translated slices solve the same scalar ODE with the same zero initial value on the
  -- same preconnected `x`-domain, so uniqueness forces equality everywhere on `Ux`.
  exact eqOn_of_same_initial_holomorphic_solution hΩp h0Ωp hFΩp hUxPreconnected
    hsliceψ hsliceφ hp.1

/-- Helper for Cartan section28 0001_Theorem_2: a translated comparison family transfers its
joint analyticity to the original translated slice once slice-wise uniqueness identifies the two
families on the full product neighborhood. -/
theorem analyticOnNhd_translatedCoordinateSlice_of_comparisonFamily
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr : Set ℂ}
    {φ ψtr : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hBx : IsOpen Bx) (hBxPreconnected : IsPreconnected Bx)
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    (hVr : IsOpen Vr)
    (hVrmap : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr Vx)
    (hψanalytic :
      AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ ↦ ψtr (p.1, Function.update t0 r (t0 r + p.2)))
        (Bx ×ˢ Vr))
    (hψsol :
      ∀ u ∈ Vr,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          Bx
          (fun x ↦ ψtr (x, Function.update t0 r (t0 r + u)))) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (Bx ×ˢ Vr) := by
  -- First identify the comparison family with the original translated slice on the whole product
  -- neighborhood by uniqueness of scalar ODE solutions on the preconnected `x`-domain.
  have hEq :
      Set.EqOn
        (fun p : ℂ × ℂ ↦ ψtr (p.1, Function.update t0 r (t0 r + p.2)))
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (Bx ×ˢ Vr) :=
    eqOn_translatedCoordinateSlice_of_comparisonFamily
      (hF := hF) (hUxPreconnected := hBxPreconnected) (hsol := hsol)
      (r := r) (hVrmap := hVrmap) hψsol
  intro p hp
  -- Then replace the comparison family by the original family on a neighborhood of each point.
  have hEventually :
      (fun q : ℂ × ℂ ↦ ψtr (q.1, Function.update t0 r (t0 r + q.2))) =ᶠ[𝓝 p]
        (fun q : ℂ × ℂ ↦ φ (q.1, Function.update t0 r (t0 r + q.2))) :=
    Filter.mem_of_superset ((hBx.prod hVr).mem_nhds hp) fun q hq ↦ hEq hq
  exact (hψanalytic p hp).congr hEventually

/-- Helper for Cartan section28 0001_Theorem_2: any frozen translated parameter inside the
verified Taylor ball for `Qtr` gives an analytic two-variable slice at the origin. -/
theorem analyticAt_translatedScalarSlice_fromQtr
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
    {ρ : NNReal} (hρR : (ρ : ENNReal) < R)
    {u : ℂ} (hu : ‖u‖ < ρ) :
    AnalyticAt ℂ
      (fun p : ℂ × (Fin k → ℂ) ↦
        F p.1 p.2 (Function.update t0 r (t0 r + u)))
      ((0 : ℂ), (0 : Fin k → ℂ)) := by
  -- First place the frozen translated parameter inside the verified Taylor ball for `Qtr`.
  have huBall :
      ((0 : ℂ), (0 : Fin k → ℂ), u) ∈ Metric.eball (0 : ℂ × (Fin k → ℂ) × ℂ) R := by
    rw [Metric.mem_eball']
    have hnorm : ‖u‖₊ < ρ := by
      simpa using hu
    have hlt : (‖u‖₊ : ENNReal) < R := lt_trans (by exact_mod_cast hnorm) hρR
    simpa using hlt
  have hAtTriple :
      AnalyticAt ℂ
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        ((0 : ℂ), (0 : Fin k → ℂ), u) :=
    hQtrBall.analyticOnNhd _ huBall
  -- Then freeze the scalar parameter by composing with the constant-parameter inclusion.
  have hfreezePair :
      AnalyticAt ℂ (fun p : ℂ × (Fin k → ℂ) ↦ (p.2, u)) ((0 : ℂ), (0 : Fin k → ℂ)) := by
    simpa using analyticAt_snd.prod
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × (Fin k → ℂ) ↦ u)
        ((0 : ℂ), (0 : Fin k → ℂ)))
  have hfreeze :
      AnalyticAt ℂ (fun p : ℂ × (Fin k → ℂ) ↦ (p.1, p.2, u))
        ((0 : ℂ), (0 : Fin k → ℂ)) := by
    simpa using analyticAt_fst.prod hfreezePair
  simpa using hAtTriple.comp_of_eq hfreeze rfl

/-- Helper for Cartan section28 0001_Theorem_2: freezing the scalar parameter in the translated
three-variable Taylor model produces a genuine two-variable owner for that slice. -/
theorem translatedScalarSliceOwner_fromQtr
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
    {ρ : NNReal} (hρR : (ρ : ENNReal) < R)
    {u : ℂ} (hu : ‖u‖ < ρ) :
    ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
      HasFPowerSeriesAt
        (fun p : ℂ × (Fin k → ℂ) ↦
          F p.1 p.2 (Function.update t0 r (t0 r + u)))
        Qslice
        ((0 : ℂ), (0 : Fin k → ℂ)) := by
  -- Unpack the analytic slice from the translated Taylor ball into an explicit owner witness.
  simpa using
    (analyticAt_translatedScalarSlice_fromQtr (F := F) (t0 := t0) (r := r)
      (Qtr := Qtr) (R := R) hQtrBall hρR hu)

/-- Helper for Cartan section28 0001_Theorem_2: once a Banach-valued translated owner evaluates
to a frozen scalar slice owner after precomposition by `id × L`, the recentered composition
coefficients agree under evaluation without any fresh coefficient induction. -/
theorem recenteredComposedCoeffBanach_eval_eq_of_sharedCurveOwner
    {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ × E → Fin k → ℂ}
    (L : E →L[ℂ] (Fin k → ℂ))
    (QB : FormalMultilinearSeries ℂ (ℂ × E) E)
    (Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ))
    {u : ℂ → E} {a : ℕ → E}
    (hu0 : u 0 = 0)
    (hu : HasFPowerSeriesAt u (oneVariableSeriesOfCoefficients a) 0)
    (hleft :
      HasFPowerSeriesAt f (L.compFormalMultilinearSeries QB) ((0 : ℂ), 0))
    (hright :
      HasFPowerSeriesAt f
        (Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
        ((0 : ℂ), 0))
    (m : ℕ) :
    L (recenteredComposedCoeffBanach QB a m) =
      recenteredComposedCoeff Qslice (fun n ↦ L (a n)) m := by
  -- Compare the two owners only after composing with the same recentered Banach curve; at that
  -- point the problem is one-variable, so the standard uniqueness theorem applies.
  have hcurve :
      HasFPowerSeriesAt (fun z : ℂ ↦ (z, u z)) (recenteredCurveSeriesBanach a) 0 := by
    simpa using recenteredCurveSeriesBanach_hasFPowerSeriesAt (u := u) (a := a) hu
  let γ : ℂ → ℂ × E := fun z ↦ (z, u z)
  have hleftComp :
      HasFPowerSeriesAt
        (fun z : ℂ ↦ f (z, u z))
        ((L.compFormalMultilinearSeries QB).comp (recenteredCurveSeriesBanach a))
        0 := by
    -- The Banach owner and the recentered curve meet at `(0, 0)`, so the composed germ is
    -- centered at the origin in one complex variable.
    have hleft0 :
        HasFPowerSeriesAt f (L.compFormalMultilinearSeries QB) (γ 0) := by
      simpa [γ, hu0] using hleft
    simpa [γ, Function.comp] using
      (HasFPowerSeriesAt.comp (g := f) (f := γ) hleft0 hcurve)
  have hrightComp :
      HasFPowerSeriesAt
        (fun z : ℂ ↦ f (z, u z))
        ((Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)).comp
          (recenteredCurveSeriesBanach a))
        0 := by
    -- The scalar slice owner is already transported to the Banach domain by `id × L`, so the
    -- same recentered curve can be fed into it directly.
    have hright0 :
        HasFPowerSeriesAt f
          (Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
          (γ 0) := by
      simpa [γ, hu0] using hright
    simpa [γ, Function.comp] using
      (HasFPowerSeriesAt.comp (g := f) (f := γ) hright0 hcurve)
  have hcompEq :
      ((L.compFormalMultilinearSeries QB).comp (recenteredCurveSeriesBanach a)) =
        ((Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)).comp
          (recenteredCurveSeriesBanach a)) := by
    exact hleftComp.eq_formalMultilinearSeries hrightComp
  have hleftCoeff :
      ((L.compFormalMultilinearSeries QB).comp (recenteredCurveSeriesBanach a)).coeff m =
        L (recenteredComposedCoeffBanach QB a m) := by
    -- The evaluated Banach owner records the recentered Banach composition coefficient
    -- coefficientwise.
    rw [recenteredComposedCoeffBanach]
    rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff]
    simp [FormalMultilinearSeries.comp, ContinuousLinearMap.compFormalMultilinearSeries, map_sum]
  have hrightCoeff :
      ((Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)).comp
          (recenteredCurveSeriesBanach a)).coeff m =
        recenteredComposedCoeff Qslice (fun n ↦ L (a n)) m := by
    -- Move the input-side transport `id × L` through the composed recentered curve once, then
    -- read off the scalar recentered coefficient in the normalized one-variable spelling.
    calc
      ((Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)).comp
          (recenteredCurveSeriesBanach a)).coeff m
          =
            (Qslice.comp
              (((ContinuousLinearMap.id ℂ ℂ).prodMap L).compFormalMultilinearSeries
                (recenteredCurveSeriesBanach a))).coeff m := by
                  rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff]
                  rfl
      _ = (Qslice.comp (recenteredCurveSeriesBanach (fun n ↦ L (a n)))).coeff m := by
            rw [recenteredCurveSeriesBanach_comp_prodMap]
      _ = recenteredComposedCoeff Qslice (fun n ↦ L (a n)) m := by
            simpa [recenteredComposedCoeffBanach] using
              (recenteredComposedCoeffBanach_eq_recenteredComposedCoeff
                (Q := Qslice) (a := fun n ↦ L (a n)) (m := m))
  calc
    L (recenteredComposedCoeffBanach QB a m)
        = ((L.compFormalMultilinearSeries QB).comp (recenteredCurveSeriesBanach a)).coeff m :=
          hleftCoeff.symm
    _ =
        ((Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)).comp
          (recenteredCurveSeriesBanach a)).coeff m := by
            rw [hcompEq]
    _ = recenteredComposedCoeff Qslice (fun n ↦ L (a n)) m := hrightCoeff

/-- Helper for Cartan section28 0001_Theorem_2: once a Banach-valued translated owner evaluates
to a frozen scalar slice owner after precomposition by `id × L`, the recentered composition
coefficients agree under evaluation without any fresh coefficient induction. -/
theorem recenteredComposedCoeffBanach_eval_eq_of_owner_eq
    {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] (Fin k → ℂ))
    (QB : FormalMultilinearSeries ℂ (ℂ × E) E)
    (Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ))
    (heq :
      L.compFormalMultilinearSeries QB =
        Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L))
    (a : ℕ → E) (m : ℕ) :
    L (recenteredComposedCoeffBanach QB a m) =
      recenteredComposedCoeff Qslice (fun n ↦ L (a n)) m := by
  have hleft :
      ((L.compFormalMultilinearSeries QB).comp (recenteredCurveSeriesBanach a)).coeff m =
        L (recenteredComposedCoeffBanach QB a m) := by
    -- Postcomposition by `L` commutes with taking the degree-`m` coefficient of the composed
    -- recentered Banach curve.
    rw [recenteredComposedCoeffBanach]
    rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff]
    simp [FormalMultilinearSeries.comp, ContinuousLinearMap.compFormalMultilinearSeries, map_sum]
  have hcomp :
      ((Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)).comp
          (recenteredCurveSeriesBanach a)).coeff m =
        (Qslice.comp
            (((ContinuousLinearMap.id ℂ ℂ).prodMap L).compFormalMultilinearSeries
              (recenteredCurveSeriesBanach a))).coeff m := by
    -- The input-side precomposition can be moved inside the composed recentered curve once at the
    -- coefficient level.
    rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff]
    rfl
  calc
    L (recenteredComposedCoeffBanach QB a m)
        = ((L.compFormalMultilinearSeries QB).comp (recenteredCurveSeriesBanach a)).coeff m :=
          hleft.symm
    _ =
        ((Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)).comp
            (recenteredCurveSeriesBanach a)).coeff m := by
              rw [heq]
    _ =
        (Qslice.comp
            (((ContinuousLinearMap.id ℂ ℂ).prodMap L).compFormalMultilinearSeries
              (recenteredCurveSeriesBanach a))).coeff m := hcomp
    _ = (Qslice.comp (recenteredCurveSeriesBanach (fun n ↦ L (a n)))).coeff m := by
          rw [recenteredCurveSeriesBanach_comp_prodMap]
    _ = recenteredComposedCoeff Qslice (fun n ↦ L (a n)) m := by
          simpa [recenteredComposedCoeffBanach] using
            (recenteredComposedCoeffBanach_eq_recenteredComposedCoeff
              (Q := Qslice) (a := fun n ↦ L (a n)) (m := m))

/-- Helper for Cartan section28 0001_Theorem_2: the owner-level equality from the Banach
translated model to a frozen scalar slice automatically identifies the evaluated exact formal
Banach solution with the canonical scalar formal solution for that slice. -/
theorem evaluatedBanachFormalSolution_eq_of_owner_eq
    {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] (Fin k → ℂ))
    (QB : FormalMultilinearSeries ℂ (ℂ × E) E)
    (Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ))
    (heq :
      L.compFormalMultilinearSeries QB =
        Qslice.compContinuousLinearMap ((ContinuousLinearMap.id ℂ ℂ).prodMap L)) :
    PowerSeries.mk (fun m ↦ L ((formalSeriesSolutionSeries QB).coeff m)) =
      formalRecenteredVectorSolutionSeries Qslice := by
  -- Feed the recentered coefficient bridge obtained from the owner equality into the existing
  -- formal-solution uniqueness lemma for the scalar slice.
  refine evaluatedBanachFormalSolution_eq_formalRecenteredVectorSolution
    (L := L) (Q := QB) (Qslice := Qslice) ?_
  intro m
  exact recenteredComposedCoeffBanach_eval_eq_of_owner_eq
    (L := L) (QB := QB) (Qslice := Qslice) heq
    (fun n ↦ (formalSeriesSolutionSeries QB).coeff n) m
