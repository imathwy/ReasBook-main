import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2»
import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».TranslatedParameterOwners
import Mathlib

open Filter
open Set

open scoped Topology

/-- Helper for Cartan section28 0001_Theorem_2: package the witness-free weighted parameter
evaluation family attached to a Banach-valued coefficient curve. -/
noncomputable def weightedParameterComparisonFamily
    {k : ℕ} (ρ : NNReal)
    (Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1) :
    ℂ × ℂ → Fin k → ℂ :=
  fun p ↦ ∑' n : ℕ, ((p.2 / (ρ : ℂ)) ^ n) • Ψ p.1 n

/-- Helper for Cartan section28 0001_Theorem_2: fixing the scalar parameter inside the weighted
radius rewrites the witness-free family to the verified weighted evaluation operator. -/
theorem weightedParameterComparisonFamily_slice_eq_eval
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ)
    (Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1) :
    (fun x : ℂ ↦ weightedParameterComparisonFamily ρ Ψ (x, u)) =
      fun x ↦ weightedParameterEvalCLM ρ u hu (Ψ x) := by
  -- The witness-free slice is just the defining summation formula for the weighted evaluator.
  funext x
  simp [weightedParameterComparisonFamily, weightedParameterEvalCLM, LinearMap.mkContinuous_apply]

/-- Helper for Cartan section28 0001_Theorem_2: once a Banach-valued coefficient curve is realized
on an `x`-ball, every frozen weighted-parameter slice is analytic in `x`. -/
theorem weightedParameterComparisonFamily_sliceAnalyticOnNhd
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ)
    {Rx : ℝ}
    {P : FormalMultilinearSeries ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)}
    (hPball : HasFPowerSeriesOnBall P.sum P 0 (ENNReal.ofReal Rx)) :
    AnalyticOnNhd ℂ
      (fun x : ℂ ↦ weightedParameterComparisonFamily ρ P.sum (x, u))
      (Metric.ball (0 : ℂ) Rx) := by
  -- Replace the witness-free slice by weighted evaluation of the realized Banach curve.
  have hPanalytic :
      AnalyticOnNhd ℂ P.sum (Metric.ball (0 : ℂ) Rx) := by
    simpa [Metric.eball_ofReal] using hPball.analyticOnNhd
  have hcurve :
      AnalyticOnNhd ℂ
        (fun x ↦ weightedParameterEvalCLM ρ u hu (P.sum x))
        (Metric.ball (0 : ℂ) Rx) :=
    analyticOnNhd_weightedParameterEvalCLM_of_curve hu hPanalytic
  simpa [weightedParameterComparisonFamily_slice_eq_eval hu P.sum] using hcurve

/-- Helper for Cartan section28 0001_Theorem_2: once a frozen weighted slice is analytic on its
full convergence ball, it remains analytic on any smaller `x`-domain inside that ball. -/
theorem weightedParameterComparisonFamily_sliceAnalyticOnNhd_mono
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ)
    {Rx : ℝ}
    {P : FormalMultilinearSeries ℂ ℂ (lp (fun _ : ℕ => Fin k → ℂ) 1)}
    (hPball : HasFPowerSeriesOnBall P.sum P 0 (ENNReal.ofReal Rx))
    {B0 : Set ℂ}
    (hB0sub : B0 ⊆ Metric.ball (0 : ℂ) Rx) :
    AnalyticOnNhd ℂ
      (fun x : ℂ ↦ weightedParameterComparisonFamily ρ P.sum (x, u))
      B0 := by
  -- Restrict the analyticity obtained on the full convergence ball to the chosen smaller domain.
  exact (weightedParameterComparisonFamily_sliceAnalyticOnNhd hu hPball).mono hB0sub

/-- Helper for Cartan section28 0001_Theorem_2: for a fixed Banach-valued coefficient row, the
witness-free weighted parameter series is analytic throughout the radius-`ρ` scalar ball. -/
theorem weightedParameterComparisonFamily_parameterAnalyticAt
    {k : ℕ} {ρ : NNReal}
    (hρ : 0 < ρ)
    (f : lp (fun _ : ℕ => Fin k → ℂ) 1)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) ρ) :
    AnalyticAt ℂ
      (fun w : ℂ ↦ weightedParameterComparisonFamily ρ (fun _ : ℂ ↦ f) (0, w))
      u := by
  -- The weighted series has an explicit one-variable power-series owner on the full radius ball.
  have hseries :
      HasFPowerSeriesOnBall
        (fun w : ℂ ↦ weightedParameterComparisonFamily ρ (fun _ : ℂ ↦ f) (0, w))
        (oneVariableSeriesOfCoefficients fun n ↦ ((ρ : ℂ)⁻¹ ^ n) • f n)
        0
        ρ := by
    simpa [weightedParameterComparisonFamily] using
      weightedParameterEvalSeries_hasFPowerSeriesOnBall hρ f
  have hanalytic :
      AnalyticOnNhd ℂ
        (fun w : ℂ ↦ weightedParameterComparisonFamily ρ (fun _ : ℂ ↦ f) (0, w))
        (Metric.ball (0 : ℂ) ρ) := by
    simpa [Metric.eball_ofReal] using hseries.analyticOnNhd
  exact hanalytic u hu

/-- Helper for Cartan section28 0001_Theorem_2: the real missing source-faithful step is the
construction of an analytic comparison family for the translated scalar system on a product
neighborhood. -/
theorem translatedSliceAnalyticOnSmallBall
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx B0 : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ ψtr : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    (hB0 : IsOpen B0) (hB0Preconnected : IsPreconnected B0)
    (h0B0 : (0 : ℂ) ∈ B0) (hB0sub : B0 ⊆ Bx)
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr : Set ℂ}
    (hVr : IsOpen Vr)
    (hVrmap : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr Vx)
    (hψanalytic :
      AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ ↦ ψtr (p.1, Function.update t0 r (t0 r + p.2)))
        (B0 ×ˢ Vr))
    (hψsol :
      ∀ u ∈ Vr,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          B0
          (fun x ↦ ψtr (x, Function.update t0 r (t0 r + u)))) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (B0 ×ˢ Vr) := by
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
    have hbase := hsolBx t ht
    -- Restrict the original slice solutions from `Bx` to the smaller preconnected `x`-ball `B0`.
    refine hbase.restrict hB0 h0B0 hB0sub ?_
    intro x hx
    exact hbase.mapsTo (hB0sub hx)
  -- Once both families solve the same translated scalar systems on `B0`, uniqueness transfers
  -- joint analyticity from the comparison family back to the original translated slice.
  exact analyticOnNhd_translatedCoordinateSlice_of_comparisonFamily
    (hF := hF) (hBx := hB0) (hBxPreconnected := hB0Preconnected) (hsol := hsolB0)
    (r := r) hVr hVrmap hψanalytic hψsol

/-- Helper for Cartan section28 0001_Theorem_2: once a translated comparison family is jointly
analytic on a chosen product neighborhood, evaluating that neighborhood at `(x0, 0)` gives the
required translated parameter-coordinate germ. -/
theorem analyticAt_translatedCoordinateSlice_of_comparisonFamily
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx B0 : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ ψtr : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)))
    (hB0 : IsOpen B0) (hB0Preconnected : IsPreconnected B0)
    (h0B0 : (0 : ℂ) ∈ B0) (hB0sub : B0 ⊆ Bx)
    {t0 : Fin j → ℂ} (r : Fin j)
    {Vr : Set ℂ}
    (hVr : IsOpen Vr) (h0Vr : (0 : ℂ) ∈ Vr)
    (hVrmap : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr Vx)
    (hψanalytic :
      AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ ↦ ψtr (p.1, Function.update t0 r (t0 r + p.2)))
        (B0 ×ˢ Vr))
    (hψsol :
      ∀ u ∈ Vr,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          B0
          (fun x ↦ ψtr (x, Function.update t0 r (t0 r + u))))
    {x0 : ℂ} (hx0 : x0 ∈ B0) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (x0, 0) := by
  -- First identify the actual translated slice with the analytic comparison family on the chosen
  -- product neighborhood.
  have hφanalytic :
      AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (B0 ×ˢ Vr) :=
    translatedSliceAnalyticOnSmallBall
      (hF := hF) (hsolBx := hsolBx) hB0 hB0Preconnected h0B0 hB0sub
      (r := r) hVr hVrmap hψanalytic hψsol
  -- Then evaluate the joint analyticity on that neighborhood at the prescribed point.
  exact hφanalytic (x0, 0) ⟨hx0, h0Vr⟩

/-- Helper for Cartan section28 0001_Theorem_2: if the translated scalar-parameter neighborhood
contains `0`, then the source slice data recover that the working `x`-domain contains `0`. -/
theorem zero_mem_xDomain_of_translatedNeighborhood
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
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
    (h0Vr' : (0 : ℂ) ∈ Vr')
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx) :
    (0 : ℂ) ∈ Bx := by
  -- Evaluate the translated slice data at the zero parameter increment to recover the base slice.
  have ht0 : t0 ∈ Vx := by
    simpa [Function.update] using hVr'map h0Vr'
  exact (hsolBx t0 ht0).mem

/-- Helper for Cartan section28 0001_Theorem_2: once a positive convergence radius is known,
choose one fixed preconnected `x`-ball around `0` that lies inside both the original `x`-domain
and that convergence ball. -/
theorem choosePreconnectedSubballInsideXDomain
    {Bx : Set ℂ}
    (hBx : IsOpen Bx) (h0Bx : (0 : ℂ) ∈ Bx)
    {Rx : ℝ} (hRx : 0 < Rx) :
    ∃ B0 : Set ℂ,
      IsOpen B0 ∧
      IsPreconnected B0 ∧
      (0 : ℂ) ∈ B0 ∧
      B0 ⊆ Bx ∧
      B0 ⊆ Metric.ball (0 : ℂ) Rx := by
  -- First intersect the source `x`-domain with the convergence ball, then choose a smaller ball
  -- inside that open neighborhood of `0`.
  have hinter : IsOpen (Bx ∩ Metric.ball (0 : ℂ) Rx) := hBx.inter Metric.isOpen_ball
  have h0inter : (0 : ℂ) ∈ Bx ∩ Metric.ball (0 : ℂ) Rx := ⟨h0Bx, Metric.mem_ball_self hRx⟩
  rcases choosePreconnectedXNeighborhood hinter h0inter with
    ⟨B0, hB0, hB0Preconnected, h0B0, hB0sub⟩
  refine ⟨B0, hB0, hB0Preconnected, h0B0, ?_, ?_⟩
  · intro x hx
    exact (hB0sub hx).1
  · intro x hx
    exact (hB0sub hx).2

/-- Helper for Cartan section28 0001_Theorem_2: any point of a positive-radius ball around `0`
lies in a smaller open preconnected subball that still contains `0`. -/
theorem choosePreconnectedSubballInsideBall_mem
    {Rx : ℝ} (hRx : 0 < Rx) {x0 : ℂ}
    (hx : x0 ∈ Metric.ball (0 : ℂ) Rx) :
    ∃ B0 : Set ℂ,
      IsOpen B0 ∧
      IsPreconnected B0 ∧
      (0 : ℂ) ∈ B0 ∧
      x0 ∈ B0 ∧
      B0 ⊆ Metric.ball (0 : ℂ) Rx := by
  let r0 : ℝ := (‖x0‖ + Rx) / 2
  have hxnorm : ‖x0‖ < Rx := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hr0pos : 0 < r0 := by
    -- The midpoint radius stays positive because the ambient ball radius is positive.
    dsimp [r0]
    linarith [norm_nonneg x0, hRx]
  have hxmem : x0 ∈ Metric.ball (0 : ℂ) r0 := by
    -- The midpoint radius still exceeds the norm of the chosen point.
    have hxlt : ‖x0‖ < r0 := by
      dsimp [r0]
      linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hxlt
  have hr0lt : r0 < Rx := by
    -- The midpoint radius remains strictly smaller than the original ambient radius.
    dsimp [r0]
    linarith
  refine ⟨Metric.ball (0 : ℂ) r0, Metric.isOpen_ball, ?_, Metric.mem_ball_self hr0pos,
    hxmem, ?_⟩
  · -- Any complex ball is convex, hence preconnected.
    exact (convex_ball (0 : ℂ) r0).isPreconnected
  · intro z hz
    -- Membership in the smaller midpoint ball implies membership in the original ambient ball.
    exact Metric.mem_ball'.2 <| lt_trans (Metric.mem_ball'.1 hz) hr0lt

/-- Helper for Cartan section28 0001_Theorem_2: the real missing source-faithful step is the
construction of an analytic comparison family for the translated scalar system on a product
neighborhood. -/
theorem translatedComparisonFamilyOnProductNeighborhood_ofPullbackFamily
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {t0 : Fin j → ℂ} (r : Fin j) {Vr' : Set ℂ}
    {ψpull : ℂ × ℂ → Fin k → ℂ}
    (hψanalytic : AnalyticOnNhd ℂ ψpull (Bx ×ˢ Vr'))
    (hψsol :
      ∀ u ∈ Vr',
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          Bx
          (fun x ↦ ψpull (x, u))) :
    ∃ ψtr : ℂ × (Fin j → ℂ) → Fin k → ℂ,
      AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ ↦ ψtr (p.1, Function.update t0 r (t0 r + p.2)))
        (Bx ×ˢ Vr') ∧
      (∀ u ∈ Vr',
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          Bx
          (fun x ↦ ψtr (x, Function.update t0 r (t0 r + u)))) := by
  let ψtr : ℂ × (Fin j → ℂ) → Fin k → ℂ := fun p ↦ ψpull (p.1, p.2 r - t0 r)
  refine ⟨ψtr, ?_, ?_⟩
  · -- The translated-coordinate pullback is exactly the analytic two-variable family `ψpull`.
    simpa [ψtr, Function.update] using hψanalytic
  · intro u hu
    -- On the translated parameter slice, `ψtr` restricts back to the original pullback family.
    simpa [ψtr, Function.update] using hψsol u hu

/-- Helper for Cartan section28 0001_Theorem_2: the real missing source-faithful step is the
construction of an analytic comparison family for the translated scalar system on a product
neighborhood. -/
theorem analyticOnNhd_pullbackFamily_of_separateAnalytic
    {k : ℕ} {Bx Vr' : Set ℂ} {ψpull : ℂ × ℂ → Fin k → ℂ}
    (hBx : IsOpen Bx) (hVr' : IsOpen Vr')
    (hx :
      ∀ u ∈ Vr',
        AnalyticOnNhd ℂ (fun x ↦ ψpull (x, u)) Bx)
    (hu :
      ∀ x ∈ Bx, ∀ u ∈ Vr',
        AnalyticAt ℂ (fun w ↦ ψpull (x, w)) u) :
    AnalyticOnNhd ℂ ψpull (Bx ×ˢ Vr') := by
  -- Joint analyticity is proved coordinatewise by Hartogs after transporting the product domain
  -- to the standard `Fin 2 → ℂ` coordinate model.
  refine (analyticOnNhd_pi_iff : AnalyticOnNhd ℂ ψpull (Bx ×ˢ Vr') ↔ _).2 ?_
  intro i
  let G : (Fin 2 → ℂ) → ℂ := fun z ↦ ψpull (z 0, z 1) i
  let D : Set (Fin 2 → ℂ) := {z | (z 0, z 1) ∈ Bx ×ˢ Vr'}
  have hD : IsOpen D := by
    -- The transported product domain stays open because the two coordinate projections are
    -- continuous.
    have hpair :
        Continuous fun z : Fin 2 → ℂ ↦ (z 0, z 1) := by
      exact
        (ContinuousLinearMap.continuous
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0)).prodMk
          (ContinuousLinearMap.continuous
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1))
    simpa [D] using (hBx.prod hVr').preimage hpair
  have hsep :
      ∀ z ∈ D, ∀ r : Fin 2,
        AnalyticAt ℂ (fun w ↦ G (Function.update z r w)) (z r) := by
    intro z hz r
    have hzProd : (z 0, z 1) ∈ Bx ×ˢ Vr' := hz
    fin_cases r
    · -- Freezing the parameter leaves the analytic `x`-slice supplied by the solution family.
      have hslice :
          AnalyticAt ℂ (fun x ↦ ψpull (x, z 1) i) (z 0) :=
        analyticAt_pi_iff.mp (hx (z 1) hzProd.2 (z 0) hzProd.1) i
      simpa [G, Function.update] using hslice
    · -- Freezing `x` leaves the explicit parameter slice.
      have hslice :
          AnalyticAt ℂ (fun w ↦ ψpull (z 0, w) i) (z 1) :=
        analyticAt_pi_iff.mp (hu (z 0) hzProd.1 (z 1) hzProd.2) i
      simpa [G, Function.update] using hslice
  have hG : AnalyticOnNhd ℂ G D := separately_holomorphic_analyticOnNhd hD hsep
  let φ : ℂ × ℂ → Fin 2 → ℂ := fun p ↦ ![p.1, p.2]
  have hφ : AnalyticOnNhd ℂ φ (Bx ×ˢ Vr') := by
    -- The coordinate transport map is analytic because both coordinate projections are.
    refine (analyticOnNhd_pi_iff :
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ fun r : Fin 2 ↦ φ p r) (Bx ×ˢ Vr') ↔
        ∀ r : Fin 2, AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ φ p r) (Bx ×ˢ Vr')).2 ?_
    intro r
    fin_cases r
    · simpa [φ] using
        (analyticOnNhd_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ) (t := Bx ×ˢ Vr'))
    · simpa [φ] using
        (analyticOnNhd_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ) (t := Bx ×ˢ Vr'))
  have hφmap : Set.MapsTo φ (Bx ×ˢ Vr') D := by
    intro p hp
    simpa [φ, D]
  -- Compose the Hartogs conclusion back with the product-coordinate map `(x, u) ↦ ![x, u]`.
  simpa [G, φ, Function.comp] using hG.comp hφ hφmap

/-- Helper for Cartan section28 0001_Theorem_2: once the Banach-valued comparison curve `Ψ` is
analytic in `x`, the witness-free weighted comparison family is jointly analytic on the product
of the `x`-domain and the working parameter ball. -/
theorem weightedParameterComparisonFamily_analyticOnNhd
    {k : ℕ} {ρ : NNReal}
    (hρ : 0 < ρ)
    {Bx : Set ℂ} (hBx : IsOpen Bx)
    {Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1}
    (hΨ : AnalyticOnNhd ℂ Ψ Bx) :
    AnalyticOnNhd ℂ
      (weightedParameterComparisonFamily ρ Ψ)
      (Bx ×ˢ Metric.ball (0 : ℂ) ρ) := by
  refine analyticOnNhd_pullbackFamily_of_separateAnalytic
    (k := k) (Bx := Bx) (Vr' := Metric.ball (0 : ℂ) ρ) hBx Metric.isOpen_ball ?_ ?_
  · intro u hu
    -- Freeze the parameter and rewrite the witness-free family to the verified weighted
    -- evaluation operator on the analytic Banach curve.
    have huρ : ‖u‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hslice :
        AnalyticOnNhd ℂ
          (fun x ↦ weightedParameterEvalCLM ρ u huρ (Ψ x))
          Bx :=
      analyticOnNhd_weightedParameterEvalCLM_of_curve huρ hΨ
    simpa [weightedParameterComparisonFamily_slice_eq_eval huρ Ψ] using hslice
  · intro x hx u hu
    -- For fixed `x`, the weighted parameter series depends analytically on `u` throughout the
    -- working radius ball.
    have hparam :
        AnalyticAt ℂ
          (fun w : ℂ ↦ weightedParameterComparisonFamily ρ (fun _ : ℂ ↦ Ψ x) (0, w))
          u :=
      weightedParameterComparisonFamily_parameterAnalyticAt (k := k) hρ (Ψ x) hu
    have hrewrite :
        (fun w : ℂ ↦ weightedParameterComparisonFamily ρ Ψ (x, w)) =
          fun w : ℂ ↦ weightedParameterComparisonFamily ρ (fun _ : ℂ ↦ Ψ x) (0, w) := by
      funext w
      simp [weightedParameterComparisonFamily]
    rw [hrewrite]
    exact hparam

/-- Helper for Cartan section28 0001_Theorem_2: joint analyticity of the witness-free weighted
comparison family only needs analyticity of each frozen weighted slice on `Bx`, because the
parameter direction is already explicit in the weighted power series. -/
theorem weightedParameterComparisonFamily_analyticOnNhd_of_sliceAnalytic
    {k : ℕ} {ρ : NNReal}
    (hρ : 0 < ρ)
    {Bx Vr' : Set ℂ} (hBx : IsOpen Bx) (hVr' : IsOpen Vr')
    (hVr'ball : Vr' ⊆ Metric.ball (0 : ℂ) ρ)
    {Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1}
    (hslice :
      ∀ u ∈ Vr',
        AnalyticOnNhd ℂ
          (fun x ↦ weightedParameterComparisonFamily ρ Ψ (x, u))
          Bx) :
    AnalyticOnNhd ℂ
      (weightedParameterComparisonFamily ρ Ψ)
      (Bx ×ˢ Vr') := by
  refine analyticOnNhd_pullbackFamily_of_separateAnalytic
    (k := k) (Bx := Bx) (Vr' := Vr') hBx hVr' ?_ ?_
  · intro u hu
    exact hslice u hu
  · intro x hx u hu
    -- For fixed `x`, the weighted parameter series remains explicit and analytic in `u`.
    have hparam :
        AnalyticAt ℂ
          (fun w : ℂ ↦ weightedParameterComparisonFamily ρ (fun _ : ℂ ↦ Ψ x) (0, w))
          u :=
      weightedParameterComparisonFamily_parameterAnalyticAt (k := k) hρ (Ψ x) (hVr'ball hu)
    have hrewrite :
        (fun w : ℂ ↦ weightedParameterComparisonFamily ρ Ψ (x, w)) =
          fun w : ℂ ↦ weightedParameterComparisonFamily ρ (fun _ : ℂ ↦ Ψ x) (0, w) := by
      funext w
      simp [weightedParameterComparisonFamily]
    rw [hrewrite]
    exact hparam

/-- Helper for Cartan section28 0001_Theorem_2: once the Banach-valued comparison curve `Ψ` is
analytic in `x` and every frozen weighted slice solves the translated scalar system on `Bx`, the
weighted comparison family already transfers joint analyticity back to the actual translated
slice. -/
theorem analyticOnNhd_translatedCoordinateSlice_of_weightedComparisonFamily
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
    (hVr'map : Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr' Vx)
    {ρu : NNReal}
    (hρupos : 0 < ρu)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu)
    {Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1}
    (hψsol :
      ∀ u ∈ Vr',
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
          (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
          0
          0
          Bx
          (fun x ↦ weightedParameterComparisonFamily ρu Ψ (x, u))) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (Bx ×ˢ Vr') := by
  have hVr'ball : Vr' ⊆ Metric.ball (0 : ℂ) ρu := by
    -- The working scalar neighborhood sits inside the weighted-evaluation radius ball.
    intro u hu
    simpa [Metric.mem_ball, dist_eq_norm] using hVr'norm u hu
  have hψanalytic :
      AnalyticOnNhd ℂ
        (weightedParameterComparisonFamily ρu Ψ)
        (Bx ×ˢ Vr') :=
    weightedParameterComparisonFamily_analyticOnNhd_of_sliceAnalytic
      (k := k) hρupos hBx hVr' hVr'ball
      (fun u hu ↦ (hψsol u hu).analytic)
  rcases translatedComparisonFamilyOnProductNeighborhood_ofPullbackFamily
      (F := F) (Ω := Ω) (Bx := Bx) (t0 := t0) (r := r) (Vr' := Vr')
      (ψpull := weightedParameterComparisonFamily ρu Ψ) hψanalytic hψsol with
    ⟨ψtr, hψtranalytic, hψtrsol⟩
  -- The translated full-parameter family is now in the exact form required by the uniqueness
  -- transfer lemma for the actual translated slice.
  exact analyticOnNhd_translatedCoordinateSlice_of_comparisonFamily
    (hF := hF) (hBx := hBx) (hBxPreconnected := hBxPreconnected) (hsol := hsolBx)
    (r := r) hVr' hVr'map hψtranalytic hψtrsol
