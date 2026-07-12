import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».TranslatedComparisonFamilies
import Mathlib

open Filter
open Set

open scoped Topology

/-- Helper for Cartan section28 0001_Theorem_2: two one-variable maps with the same formal owner
at the origin agree on some punctured neighborhood of `0`. -/
theorem sameFormalOwnerEventuallyEqAtZero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {u v : ℂ → E} {P : FormalMultilinearSeries ℂ ℂ E}
    (hu : HasFPowerSeriesAt u P 0) (hv : HasFPowerSeriesAt v P 0) :
    u =ᶠ[𝓝 (0 : ℂ)] v := by
  -- Shrink the two power-series witnesses to a common positive ball around the origin.
  rcases hu with ⟨ru, huBall⟩
  rcases hv with ⟨rv, hvBall⟩
  have hrmin : 0 < min ru rv := lt_min huBall.r_pos hvBall.r_pos
  -- On that common ball, uniqueness of `HasFPowerSeriesOnBall` identifies the two functions.
  exact
    (huBall.mono hrmin inf_le_left).unique (hvBall.mono hrmin inf_le_right)
      |>.eventuallyEq_of_mem (Metric.eball_mem_nhds (0 : ℂ) hrmin)

/-- Helper for Cartan section28 0001_Theorem_2: a one-variable germ at the origin has a unique
formal multilinear owner. -/
theorem formalMultilinearSeries_eq_of_same_hasFPowerSeriesAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {P₁ P₂ : FormalMultilinearSeries ℂ ℂ E} {z : ℂ}
    (h₁ : HasFPowerSeriesAt f P₁ z)
    (h₂ : HasFPowerSeriesAt f P₂ z) :
    P₁ = P₂ := by
  -- Mathlib already identifies the one-variable formal owner of a germ uniquely.
  exact h₁.eq_formalMultilinearSeries h₂

/-- Helper for Cartan section28 0001_Theorem_2: two formal owners of the same germ on a Banach
domain agree on every diagonal evaluation. -/
theorem formalMultilinearSeries_apply_diag_eq_of_same_hasFPowerSeriesAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {P₁ P₂ : FormalMultilinearSeries ℂ E F} {x : E}
    (h₁ : HasFPowerSeriesAt f P₁ x)
    (h₂ : HasFPowerSeriesAt f P₂ x) :
    ∀ n y, P₁ n (fun _ ↦ y) = P₂ n (fun _ ↦ y) := by
  intro n y
  -- Subtract the two owners and apply the generic diagonal-vanishing criterion for the zero germ.
  have hzero : HasFPowerSeriesAt (fun _ : E ↦ (0 : F)) (P₁ - P₂) x := by
    simpa using h₁.sub h₂
  exact sub_eq_zero.mp <| by simpa using hzero.apply_eq_zero n y

/-- Helper for Cartan section28 0001_Theorem_2: a zero-initial holomorphic solution of a scalar
slice has the canonical section-27 formal owner attached to the recentered system. -/
theorem holomorphicSolutionOn_hasCanonicalFormalOwner
    {k : ℕ} {Ω : Set (ℂ × (Fin k → ℂ))}
    {f : ℂ → (Fin k → ℂ) → Fin k → ℂ}
    {U : Set ℂ} {ψ : ℂ → Fin k → ℂ}
    {Q : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ)}
    (hψ : IsHolomorphicSystemSolutionOn Ω f 0 0 U ψ)
    (hQ : HasFPowerSeriesAt (fun p : ℂ × (Fin k → ℂ) ↦ f p.1 p.2) Q ((0 : ℂ), 0)) :
    HasFPowerSeriesAt ψ
      (vectorOfScalarsSeries fun m ↦
        PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q))
      0 := by
  obtain ⟨P, hP⟩ := hψ.analytic 0 hψ.mem
  let ψSeries : PowerSeries (Fin k → ℂ) := PowerSeries.mk fun m ↦ P.coeff m
  have hψOwner :
      HasFPowerSeriesAt ψ
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m ψSeries)
        0 := by
    -- Replace the arbitrary one-variable owner by its coefficient package.
    have hpack :
        P = vectorOfScalarsSeries (fun m ↦ PowerSeries.coeff m ψSeries) := by
      simpa [ψSeries] using formalMultilinearSeries_eq_vectorOfScalarsSeries (P := P)
    exact hpack ▸ hP
  have hψSeries0 :
      PowerSeries.constantCoeff ψSeries = 0 := by
    -- The solution starts at the prescribed zero initial value, so the recentered constant term
    -- must vanish.
    have hcoeff0 : PowerSeries.coeff 0 ψSeries = 0 := by
      have hP0 : P.coeff 0 = 0 := by
        have hP0Eval : P 0 (fun _ ↦ (0 : ℂ)) = 0 := by
          simpa [hψ.initial] using hP.coeff_zero (fun _ ↦ (0 : ℂ))
        have hone : (1 : Fin 0 → ℂ) = fun _ ↦ (0 : ℂ) := by
          funext i
          exact Fin.elim0 i
        rw [FormalMultilinearSeries.coeff, hone, hP0Eval]
      simpa [ψSeries] using hP0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff0
  have hψCurve :
      HasFPowerSeriesAt
        (fun z : ℂ ↦ (z, ψ z))
        (recenteredCurveSeries fun m ↦ PowerSeries.coeff m ψSeries)
        0 := by
    -- Pair the realized centered series with the identity coordinate.
    simpa using recenteredCurve_hasFPowerSeriesAt hψOwner
  have hQAt :
      HasFPowerSeriesAt
        (fun p : ℂ × (Fin k → ℂ) ↦ f p.1 p.2)
        Q
        ((fun z : ℂ ↦ (z, ψ z)) 0) := by
    simpa [hψ.initial] using hQ
  have hψRhs :
      HasFPowerSeriesAt
        (fun z : ℂ ↦ f z (ψ z))
        (Q.comp (recenteredCurveSeries fun m ↦ PowerSeries.coeff m ψSeries))
        0 := by
    -- Compose the slice owner with the realized centered curve.
    simpa [Function.comp] using
      (HasFPowerSeriesAt.comp
        (g := fun p : ℂ × (Fin k → ℂ) ↦ f p.1 p.2)
        (f := fun z : ℂ ↦ (z, ψ z))
        hQAt
        hψCurve)
  rcases hψOwner with ⟨rψ, hψBall⟩
  have hψOwnerAt :
      HasFPowerSeriesAt ψ
        (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m ψSeries)
        0 :=
    hψBall.hasFPowerSeriesAt
  have hψDeriv :
      HasFPowerSeriesAt
        (deriv ψ)
        ((ContinuousLinearMap.apply ℂ (Fin k → ℂ) (1 : ℂ)).compFormalMultilinearSeries
          (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m ψSeries).derivSeries)
        0 := by
    -- Differentiate the realized one-variable owner once and evaluate the derivative at `1`.
    convert
      ((ContinuousLinearMap.apply ℂ (Fin k → ℂ) (1 : ℂ)).comp_hasFPowerSeriesOnBall
        hψBall.fderiv).hasFPowerSeriesAt using 1
  have hEventuallyDeriv :
      deriv ψ =ᶠ[𝓝 (0 : ℂ)] fun z ↦ f z (ψ z) := by
    -- The slice owner already records the differential equation on a neighborhood of `0`.
    filter_upwards [hψ.isOpen.mem_nhds hψ.mem] with z hz
    simpa using (hψ.deriv_eq hz).deriv
  have hDerivOwners :
      ((ContinuousLinearMap.apply ℂ (Fin k → ℂ) (1 : ℂ)).compFormalMultilinearSeries
          (vectorOfScalarsSeries fun m ↦ PowerSeries.coeff m ψSeries).derivSeries)
        =
      Q.comp (recenteredCurveSeries fun m ↦ PowerSeries.coeff m ψSeries) :=
    hψDeriv.eq_formalMultilinearSeries_of_eventually hψRhs hEventuallyDeriv
  have hψRec :
      ∀ m, PowerSeries.coeff (m + 1) ψSeries =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q
          (fun k ↦ PowerSeries.coeff k ψSeries) m := by
    intro m
    have hcoeff :=
      congrArg
        (fun P : FormalMultilinearSeries ℂ ℂ (Fin k → ℂ) ↦ P.coeff m)
        hDerivOwners
    have hscaled :
        (m + 1 : ℂ) • PowerSeries.coeff (m + 1) ψSeries =
          recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ψSeries) m := by
      calc
        (m + 1 : ℂ) • PowerSeries.coeff (m + 1) ψSeries
            =
              (((ContinuousLinearMap.apply ℂ (Fin k → ℂ) (1 : ℂ)).compFormalMultilinearSeries
                  (vectorOfScalarsSeries fun k ↦ PowerSeries.coeff k ψSeries).derivSeries).coeff
                m) := by
                  rw [FormalMultilinearSeries.coeff,
                    ContinuousLinearMap.compFormalMultilinearSeries_apply']
                  change
                    (m + 1 : ℂ) • PowerSeries.coeff (m + 1) ψSeries =
                      ((vectorOfScalarsSeries fun k ↦ PowerSeries.coeff k ψSeries).derivSeries.coeff
                        m) 1
                  rw [FormalMultilinearSeries.derivSeries_coeff_one]
                  rw [vectorOfScalarsSeries_coeff]
                  rw [← Nat.cast_smul_eq_nsmul ℂ]
                  simp
        _ = (Q.comp (recenteredCurveSeries fun k ↦ PowerSeries.coeff k ψSeries)).coeff m := hcoeff
        _ = recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ψSeries) m := rfl
    have hinv :
        ((m + 1 : ℂ)⁻¹) * (m + 1 : ℂ) = 1 := by
      exact inv_mul_cancel₀ <| by exact_mod_cast Nat.succ_ne_zero m
    calc
      PowerSeries.coeff (m + 1) ψSeries
          = (((m + 1 : ℂ)⁻¹) * (m + 1 : ℂ)) • PowerSeries.coeff (m + 1) ψSeries := by
              simp [hinv]
      _ = ((m + 1 : ℂ)⁻¹) • ((m + 1 : ℂ) • PowerSeries.coeff (m + 1) ψSeries) := by
            simp [smul_smul]
      _ = ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q
            (fun k ↦ PowerSeries.coeff k ψSeries) m := by
              rw [hscaled]
  have hcanonical :
      ψSeries = formalRecenteredVectorSolutionSeries Q := by
    rcases existsUnique_formal_series_solution_for_recentered_multilinear_system Q with
      ⟨ξ, hξ, hξuniq⟩
    exact (hξuniq _ ⟨hψSeries0, hψRec⟩).trans
      (hξuniq _ (formalRecenteredVectorSolutionSeries_isSolution (Q := Q))).symm
  -- Replace the temporary slice owner by the canonical formal solution owner.
  simpa [hcanonical] using hψOwnerAt

/-- Helper for Cartan section28 0001_Theorem_2: the real missing source-faithful step is the
construction of an analytic comparison family for the translated scalar system on a product
neighborhood. -/
theorem translatedSliceCanonicalFormalOwner_fromTaylorBall
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ} {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    {Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ)}
    {R : ENNReal}
    (hQtrBall :
      HasFPowerSeriesOnBall
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        Qtr
        ((0 : ℂ), (0 : Fin k → ℂ), 0)
        R)
    {ρu : NNReal} (hρuR : (ρu : ENNReal) < R)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu) :
    ∀ u ∈ Vr',
      ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
        HasFPowerSeriesAt
          (fun p : ℂ × (Fin k → ℂ) ↦
            F p.1 p.2 (Function.update t0 r (t0 r + u)))
          Qslice
          ((0 : ℂ), (0 : Fin k → ℂ)) ∧
        HasFPowerSeriesAt
          (fun x ↦ φ (x, Function.update t0 r (t0 r + u)))
          (vectorOfScalarsSeries fun m ↦
            PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
          0 := by
  intro u hu
  -- First freeze the translated Taylor model to a genuine scalar owner for the `u`-slice.
  rcases translatedScalarSliceOwner_fromQtr
      (F := F) (t0 := t0) (r := r) (Qtr := Qtr) (R := R)
      hQtrBall hρuR (hVr'norm u hu) with
    ⟨Qslice, hQsliceAt⟩
  refine ⟨Qslice, hQsliceAt, ?_⟩
  have hsliceSolution :=
    hsolBx (Function.update t0 r (t0 r + u)) (hVr'map hu)
  -- Then the actual translated slice inherits the canonical section-27 formal owner for that
  -- frozen scalar system.
  simpa using
    holomorphicSolutionOn_hasCanonicalFormalOwner
      (hψ := hsliceSolution)
      (hQ := hQsliceAt)

/-- Helper for Cartan section28 0001_Theorem_2: the real missing source-faithful step is the
construction of an analytic comparison family for the translated scalar system on a product
neighborhood. -/
theorem translatedSliceCanonicalFormalOwner
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ} {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    (hQslice :
      ∀ u ∈ Vr',
        ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update t0 r (t0 r + u)))
            Qslice
            ((0 : ℂ), (0 : Fin k → ℂ))) :
    ∀ u ∈ Vr',
      ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
        HasFPowerSeriesAt
          (fun p : ℂ × (Fin k → ℂ) ↦
            F p.1 p.2 (Function.update t0 r (t0 r + u)))
          Qslice
          ((0 : ℂ), (0 : Fin k → ℂ)) ∧
        HasFPowerSeriesAt
          (fun x ↦ φ (x, Function.update t0 r (t0 r + u)))
          (vectorOfScalarsSeries fun m ↦
            PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
          0 := by
  intro u hu
  rcases hQslice u hu with ⟨Qslice, hQsliceAt⟩
  have hsliceSolution :=
    hsolBx (Function.update t0 r (t0 r + u)) (hVr'map hu)
  refine ⟨Qslice, hQsliceAt, ?_⟩
  -- The actual translated slice already has the canonical scalar formal owner for `Qslice`.
  simpa using
    holomorphicSolutionOn_hasCanonicalFormalOwner
      (hψ := hsliceSolution)
      (hQ := hQsliceAt)

/-- Helper for Cartan section28 0001_Theorem_2: the real missing source-faithful step is the
construction of an analytic comparison family for the translated scalar system on a product
neighborhood. -/
theorem translatedSliceEqOn_of_sharedCanonicalOwner
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hBxPreconnected : IsPreconnected Bx)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr' : Set ℂ}
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    {u : ℂ} (hu : u ∈ Vr')
    {Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ)}
    (hφowner :
      HasFPowerSeriesAt
        (fun x ↦ φ (x, Function.update t0 r (t0 r + u)))
        (vectorOfScalarsSeries fun m ↦
          PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
        0)
    {ψ : ℂ → Fin k → ℂ}
    (hψanalytic : AnalyticOnNhd ℂ ψ Bx)
    (hψowner :
      HasFPowerSeriesAt ψ
        (vectorOfScalarsSeries fun m ↦
          PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
        0) :
    Set.EqOn ψ (fun x ↦ φ (x, Function.update t0 r (t0 r + u))) Bx := by
  have hφanalytic :
      AnalyticOnNhd ℂ (fun x ↦ φ (x, Function.update t0 r (t0 r + u))) Bx :=
    (hsolBx (Function.update t0 r (t0 r + u)) (hVr'map hu)).analytic
  have hEventually :
      ψ =ᶠ[𝓝 (0 : ℂ)] fun x ↦ φ (x, Function.update t0 r (t0 r + u)) :=
    sameFormalOwnerEventuallyEqAtZero hψowner hφowner
  -- Once the two slice realizations share the same canonical owner, analyticity upgrades their
  -- germ equality at `0` to equality on the full preconnected `x`-domain.
  exact hψanalytic.eqOn_of_preconnected_of_eventuallyEq
    hφanalytic hBxPreconnected
    (hsolBx (Function.update t0 r (t0 r + u)) (hVr'map hu)).mem
    hEventually

/-- Helper for Cartan section28 0001_Theorem_2: once an analytic translated slice shares the
canonical scalar owner of the actual slice, equality on `Bx` upgrades it to the full
holomorphic-system solution predicate on `Bx`. -/
theorem translatedSliceSolutionOn_of_sharedCanonicalOwner
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hBxPreconnected : IsPreconnected Bx)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr' : Set ℂ}
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    {u : ℂ} (hu : u ∈ Vr')
    {Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ)}
    (hφowner :
      HasFPowerSeriesAt
        (fun x ↦ φ (x, Function.update t0 r (t0 r + u)))
        (vectorOfScalarsSeries fun m ↦
          PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
        0)
    {ψ : ℂ → Fin k → ℂ}
    (hψanalytic : AnalyticOnNhd ℂ ψ Bx)
    (hψowner :
      HasFPowerSeriesAt ψ
        (vectorOfScalarsSeries fun m ↦
          PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
        0) :
    IsHolomorphicSystemSolutionOn
      {p : ℂ × (Fin k → ℂ) |
        (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
      (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
      0
      0
      Bx
      ψ := by
  let hbase := hsolBx (Function.update t0 r (t0 r + u)) (hVr'map hu)
  have hEq :
      Set.EqOn ψ (fun x ↦ φ (x, Function.update t0 r (t0 r + u))) Bx :=
    translatedSliceEqOn_of_sharedCanonicalOwner
      (hBxPreconnected := hBxPreconnected) (hsolBx := hsolBx)
      (r := r) (hVr'map := hVr'map) hu hφowner hψanalytic hψowner
  refine ⟨hbase.isOpen, hbase.mem, hψanalytic, ?_, ?_, ?_⟩
  · -- Equality with the actual slice pushes the competitor graph into the same coefficient domain.
    intro x hx
    simpa [hEq hx] using hbase.mapsTo hx
  · -- The shared canonical owner already forces the same zero initial value at `x = 0`.
    simpa [hEq hbase.mem] using hbase.initial
  · intro x hx
    -- On the open `x`-domain, local equality identifies the derivatives as well.
    have hEventually :
        ψ =ᶠ[𝓝 x] fun z ↦ φ (z, Function.update t0 r (t0 r + u)) := by
      exact Filter.mem_of_superset (hbase.isOpen.mem_nhds hx) fun z hz ↦ hEq hz
    have hderiv :
        HasDerivAt ψ
          (F x (φ (x, Function.update t0 r (t0 r + u))) (Function.update t0 r (t0 r + u)))
          x :=
      (hbase.deriv_eq hx).congr_of_eventuallyEq hEventually
    -- Rewrite the derivative value through the pointwise slice equality at `x`.
    exact hderiv.congr_deriv <| by rw [hEq hx]

/-- Helper for Cartan section28 0001_Theorem_2: the source-faithful local goal is joint
analyticity of the actual translated scalar slice on a small product neighborhood. -/
theorem translatedWeightedComparisonFamilyOnShrunkBall
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hBx : IsOpen Bx) (_hBxPreconnected : IsPreconnected Bx)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr' : Set ℂ}
    (hVr' : IsOpen Vr')
    (h0Vr' : (0 : ℂ) ∈ Vr')
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    {ρu : NNReal}
    (hρupos : 0 < ρu)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu)
    {QB :
      FormalMultilinearSeries
        ℂ
        (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
        (lp (fun _ : ℕ => Fin k → ℂ) 1)}
    (hQBrad : 0 < QB.radius)
    (hQBanachEval :
      ∀ u, ∀ hu : u ∈ Vr',
        ∃ Qslice0 : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update t0 r (t0 r + u)))
            Qslice0
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          let L := weightedParameterEvalCLM ρu u (hVr'norm u hu)
          PowerSeries.mk (fun m ↦ L ((formalSeriesSolutionSeries QB).coeff m)) =
            formalRecenteredVectorSolutionSeries Qslice0)
    (hQsliceCanonical :
      ∀ u ∈ Vr',
        ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update t0 r (t0 r + u)))
            Qslice
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          HasFPowerSeriesAt
            (fun x ↦ φ (x, Function.update t0 r (t0 r + u)))
            (vectorOfScalarsSeries fun m ↦
              PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
            0) :
    ∃ B0 : Set ℂ,
      IsOpen B0 ∧
      IsPreconnected B0 ∧
      (0 : ℂ) ∈ B0 ∧
      B0 ⊆ Bx ∧
      ∃ Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1,
        AnalyticOnNhd ℂ
          (weightedParameterComparisonFamily ρu Ψ)
          (B0 ×ˢ Vr') ∧
        (∀ u ∈ Vr',
          IsHolomorphicSystemSolutionOn
            {p : ℂ × (Fin k → ℂ) |
              (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
            (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
            0
            0
            B0
            (fun x ↦ weightedParameterComparisonFamily ρu Ψ (x, u))) := by
  have h0Bx : (0 : ℂ) ∈ Bx :=
    zero_mem_xDomain_of_translatedNeighborhood
      (hsolBx := hsolBx) (r := r) h0Vr' hVr'map
  -- Realize the exact Banach solution on its natural convergence ball.
  rcases banachFormalSolutionOnShrunkBall (Q := QB) hQBrad with ⟨Rx, hRx, hΨball⟩
  rcases choosePreconnectedSubballInsideXDomain hBx h0Bx hRx with
    ⟨B0, hB0, hB0Preconnected, h0B0, hB0subBx, hB0subBall⟩
  let Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1 := (formalSeriesSolutionSeries QB).sum
  have hψsol :
      ∀ u ∈ Vr',
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          B0
          (fun x ↦ weightedParameterComparisonFamily ρu Ψ (x, u)) := by
    intro u hu
    rcases hQBanachEval u hu with ⟨Qslice0, hQslice0At, hQslice0SeriesEq⟩
    rcases hQsliceCanonical u hu with ⟨Qslice, hQsliceAt, hφownerCanonical⟩
    have hφownerFromQslice0 :
        HasFPowerSeriesAt
          (fun x ↦ φ (x, Function.update t0 r (t0 r + u)))
          (vectorOfScalarsSeries fun m ↦
            PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice0))
          0 := by
      have hsliceSolution :=
        hsolBx (Function.update t0 r (t0 r + u)) (hVr'map hu)
      -- The actual translated slice has the canonical section-27 owner for any valid frozen
      -- two-variable owner of its right-hand side.
      simpa using
        holomorphicSolutionOn_hasCanonicalFormalOwner
          (hψ := hsliceSolution)
          (hQ := hQslice0At)
    have hQsliceSeriesEq :
        formalRecenteredVectorSolutionSeries Qslice0 =
          formalRecenteredVectorSolutionSeries Qslice := by
      have hOwnerEq :
          vectorOfScalarsSeries (fun m ↦
            PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice0)) =
            vectorOfScalarsSeries (fun m ↦
              PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice)) := by
        -- The actual one-variable slice has a unique one-variable formal owner at the origin.
        exact formalMultilinearSeries_eq_of_same_hasFPowerSeriesAt
          hφownerFromQslice0 hφownerCanonical
      ext m i
      have hcoeff :=
        congrArg
          (fun P : FormalMultilinearSeries ℂ ℂ (Fin k → ℂ) ↦ P.coeff m)
          hOwnerEq
      simpa [vectorOfScalarsSeries_coeff] using
        congrArg (fun v : Fin k → ℂ ↦ v i) hcoeff
    have hψanalytic :
        AnalyticOnNhd ℂ
          (fun x ↦ weightedParameterComparisonFamily ρu Ψ (x, u))
          B0 := by
      -- The Banach formal solution is analytic on its convergence ball, so every frozen weighted
      -- slice is analytic on the chosen smaller `x`-domain `B0`.
      exact weightedParameterComparisonFamily_sliceAnalyticOnNhd_mono
        (hu := hVr'norm u hu) (P := formalSeriesSolutionSeries QB) hΨball hB0subBall
    have hΨownerAt :
        HasFPowerSeriesAt
          (fun x ↦ weightedParameterEvalCLM ρu u (hVr'norm u hu) (Ψ x))
          ((weightedParameterEvalCLM ρu u (hVr'norm u hu)).compFormalMultilinearSeries
            (formalSeriesSolutionSeries QB))
          0 := by
      -- Evaluate the Banach-valued formal solution owner once at the frozen parameter `u`.
      simpa [Ψ] using
        HasFPowerSeriesOnBall.hasFPowerSeriesAt
          ((weightedParameterEvalCLM ρu u (hVr'norm u hu)).comp_hasFPowerSeriesOnBall hΨball)
    have hΨownerCanonical :
        HasFPowerSeriesAt
          (fun x ↦ weightedParameterComparisonFamily ρu Ψ (x, u))
          (vectorOfScalarsSeries fun m ↦
            PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
          0 := by
      -- Rewrite the evaluated Banach solution owner to the canonical scalar owner for the frozen
      -- slice before invoking slice-wise uniqueness.
      have hseriesEq :
          ((weightedParameterEvalCLM ρu u (hVr'norm u hu)).compFormalMultilinearSeries
              (formalSeriesSolutionSeries QB)) =
            vectorOfScalarsSeries (fun m ↦
              weightedParameterEvalCLM ρu u (hVr'norm u hu)
                ((formalSeriesSolutionSeries QB).coeff m)) := by
        calc
          ((weightedParameterEvalCLM ρu u (hVr'norm u hu)).compFormalMultilinearSeries
                (formalSeriesSolutionSeries QB))
              =
                vectorOfScalarsSeries
                  (fun m ↦
                    (((weightedParameterEvalCLM ρu u (hVr'norm u hu)).compFormalMultilinearSeries
                      (formalSeriesSolutionSeries QB)).coeff m)) := by
                    exact formalMultilinearSeries_eq_vectorOfScalarsSeries _
          _ =
              vectorOfScalarsSeries (fun m ↦
                weightedParameterEvalCLM ρu u (hVr'norm u hu)
                  ((formalSeriesSolutionSeries QB).coeff m)) := by
                    apply congrArg vectorOfScalarsSeries
                    funext m
                    rw [compFormalMultilinearSeries_coeff_apply]
      have hownerEq :
          PowerSeries.mk
              (fun m ↦
                weightedParameterEvalCLM ρu u (hVr'norm u hu)
                  ((formalSeriesSolutionSeries QB).coeff m))
            =
            formalRecenteredVectorSolutionSeries Qslice := by
        let L : lp (fun _ : ℕ => Fin k → ℂ) 1 →L[ℂ] (Fin k → ℂ) :=
          weightedParameterEvalCLM ρu u (hVr'norm u hu)
        -- Replace the auxiliary frozen owner by the canonical one before transporting the
        -- evaluated Banach formal solution.
        calc
          PowerSeries.mk
              (fun m ↦
                weightedParameterEvalCLM ρu u (hVr'norm u hu)
                  ((formalSeriesSolutionSeries QB).coeff m))
              = formalRecenteredVectorSolutionSeries Qslice0 := by
                  simpa [L] using hQslice0SeriesEq
          _ = formalRecenteredVectorSolutionSeries Qslice := hQsliceSeriesEq
      have hownerEqCoeff :
          (fun m ↦
            weightedParameterEvalCLM ρu u (hVr'norm u hu)
              ((formalSeriesSolutionSeries QB).coeff m)) =
            fun m ↦ PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice) := by
        funext m
        simpa using
          congrArg (fun p : PowerSeries (Fin k → ℂ) ↦ PowerSeries.coeff m p) hownerEq
      rw [hseriesEq] at hΨownerAt
      simpa [Ψ, weightedParameterComparisonFamily_slice_eq_eval (hVr'norm u hu), hownerEqCoeff]
        using hΨownerAt
    -- The frozen weighted slice now shares the canonical scalar owner with the actual slice.
    exact translatedSliceSolutionOn_of_sharedCanonicalOwner
      (hBxPreconnected := hB0Preconnected)
      (hsolBx := fun t ht ↦
        (hsolBx t ht).restrict hB0 h0B0 hB0subBx (fun x hx ↦
          (hsolBx t ht).mapsTo (hB0subBx hx)))
      (r := r) (hVr'map := hVr'map) hu hφownerCanonical hψanalytic hΨownerCanonical
  have hψanalytic :
      AnalyticOnNhd ℂ
        (weightedParameterComparisonFamily ρu Ψ)
        (B0 ×ˢ Vr') := by
    -- Once the `x`-domain is fixed to `B0`, joint analyticity follows from the frozen-slice
    -- analyticity together with the explicit weighted parameter dependence.
    refine weightedParameterComparisonFamily_analyticOnNhd_of_sliceAnalytic
      (k := k) hρupos hB0 hVr' ?_ ?_
    · intro u hu
      simpa [Metric.mem_ball, dist_eq_norm] using hVr'norm u hu
    · intro u hu
      exact (hψsol u hu).analytic
  exact ⟨B0, hB0, hB0Preconnected, h0B0, hB0subBx, Ψ, hψanalytic, hψsol⟩

/-- Helper for Cartan section28 0001_Theorem_2: the weighted comparison-family construction
already yields a concrete translated `x`-domain on which the actual translated slice is jointly
analytic at parameter increment `0`. -/
theorem existsTranslatedCoordinateSliceAnalyticAtZeroDomain
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hBx : IsOpen Bx) (hBxPreconnected : IsPreconnected Bx)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr' : Set ℂ}
    (hVr' : IsOpen Vr')
    (h0Vr' : (0 : ℂ) ∈ Vr')
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    {ρu : NNReal}
    (hρupos : 0 < ρu)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu)
    {QB :
      FormalMultilinearSeries
        ℂ
        (ℂ × lp (fun _ : ℕ => Fin k → ℂ) 1)
        (lp (fun _ : ℕ => Fin k → ℂ) 1)}
    (hQBrad : 0 < QB.radius)
    (hQBanachEval :
      ∀ u, ∀ hu : u ∈ Vr',
        ∃ Qslice0 : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update t0 r (t0 r + u)))
            Qslice0
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          let L := weightedParameterEvalCLM ρu u (hVr'norm u hu)
          PowerSeries.mk (fun m ↦ L ((formalSeriesSolutionSeries QB).coeff m)) =
            formalRecenteredVectorSolutionSeries Qslice0)
    (hQsliceCanonical :
      ∀ u ∈ Vr',
        ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update t0 r (t0 r + u)))
            Qslice
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          HasFPowerSeriesAt
            (fun x ↦ φ (x, Function.update t0 r (t0 r + u)))
            (vectorOfScalarsSeries fun m ↦
              PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
            0) :
    ∃ B0 : Set ℂ,
      IsOpen B0 ∧
      IsPreconnected B0 ∧
      (0 : ℂ) ∈ B0 ∧
      B0 ⊆ Bx ∧
      ∀ x0 ∈ B0,
        AnalyticAt ℂ
          (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
          (x0, 0) := by
  rcases translatedWeightedComparisonFamilyOnShrunkBall
      (hBx := hBx) (_hBxPreconnected := hBxPreconnected) (hsolBx := hsolBx)
      (r := r) (hVr' := hVr') h0Vr' hVr'map hρupos hVr'norm hQBrad hQBanachEval
      hQsliceCanonical with
    ⟨B0, hB0, hB0Preconnected, h0B0, hB0subBx, Ψ, hΨanalytic, hΨsol⟩
  refine ⟨B0, hB0, hB0Preconnected, h0B0, hB0subBx, ?_⟩
  intro x0 hx0
  have hsolB0 :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          B0
          (fun x ↦ φ (x, t)) := by
    intro t ht
    -- Restrict the original slice solution family to the produced local `x`-domain.
    refine (hsolBx t ht).restrict hB0 h0B0 hB0subBx ?_
    intro x hx
    exact (hsolBx t ht).mapsTo (hB0subBx hx)
  have hanalytic :
      AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (B0 ×ˢ Vr') :=
    analyticOnNhd_translatedCoordinateSlice_of_weightedComparisonFamily
      (hF := hF)
      (hBx := hB0) (hBxPreconnected := hB0Preconnected) (hsolBx := hsolB0)
      (r := r) (hVr' := hVr') (hVr'map := hVr'map) hρupos hVr'norm
      (Ψ := Ψ) hΨsol
  -- Evaluating the jointly analytic translated family at `(x0, 0)` gives the required
  -- parameter-coordinate germ on the produced domain.
  exact hanalytic (x0, 0) ⟨hx0, h0Vr'⟩
