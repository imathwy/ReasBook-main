import DifferentialForms_Cartan_1970.cartan.VII.section27.«0001_Theorem_I»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2»
import DifferentialForms_Cartan_1970.cartan.VII.section28.«0001_Theorem_2».Index
import Mathlib

open Filter
open Set

open scoped Topology unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: section 27 already introduces the canonical source-facing owner
-- `IsHolomorphicSystemSolutionOn` for local holomorphic first-order systems. The parameter
-- dependence theorem is stated as a bridge from that slice-wise local solution data, together
-- with an actual neighborhood in `(x, t)`-space, to joint analyticity near the origin.

/-- Helper for Cartan section28 0001_Theorem_2: the remaining continuation step should recenter the
system at a nearby seed point, reuse the zero-origin comparison-family package there, and transport
the resulting analytic germ back to the original coordinates. -/
private theorem translatedCoordinateSliceContinuationFromSeedRecentered
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ}
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
    (hVr' : IsOpen Vr') (h0Vr' : (0 : ℂ) ∈ Vr')
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
    {ρu : NNReal} (hρupos : 0 < ρu) (hρuR : (ρu : ENNReal) < R)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu)
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
            0)
    {a x0 : ℂ}
    (ha : a ∈ Bx)
    (hx0 : x0 ∈ Bx)
    (hseed :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (a, 0)) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (x0, 0) := by
  let τ : ℂ → Fin j → ℂ := fun u ↦ Function.update t0 r (t0 r + u)
  let ba : ℂ → Fin k → ℂ := fun u ↦ φ (a, τ u)
  let Ba : Set ℂ := {ξ : ℂ | a + ξ ∈ Bx}
  -- Route correction: the missing premise is now isolated to one explicit seed-recentering step.
  rcases seedValueAnalyticOnNeighborhood (φ := φ) (Vr' := Vr') (t0 := t0) r hVr' h0Vr' hseed with
    ⟨Vr0, hVr0, h0Vr0, hVr0sub, hbaVr0⟩
  have hVr0map : Set.MapsTo τ Vr0 Vx := by
    intro u hu
    exact hVr'map (hVr0sub hu)
  have hVr0norm : ∀ u ∈ Vr0, ‖u‖ < ρu := by
    intro u hu
    exact hVr'norm u (hVr0sub hu)
  have ht0Vx : t0 ∈ Vx := by
    simpa [τ] using hVr0map h0Vr0
  have hTranslatedDomain :
      IsOpen Ba ∧
        IsPreconnected Ba ∧
        (0 : ℂ) ∈ Ba ∧
        (x0 - a : ℂ) ∈ Ba := by
    simpa [Ba] using
      translatedXDomainAroundSeed hBx hBxPreconnected ha hx0
  have hRecenteredSlice :
      ∀ u ∈ Vr0,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) |
            (a + p.1, ba u + p.2, τ u) ∈ Ω}
          (fun ξ y ↦
            F (a + ξ) (ba u + y) (τ u))
          0
          0
          Ba
          (fun ξ ↦ φ (a + ξ, τ u) - ba u) := by
    intro u hu
    -- The frozen recentered slices are already available; only the comparison-family continuation
    -- from `0` to `x₀ - a` remains.
    exact
      seedRecenteredSliceSolutionOnTranslatedDomain
        (hsolBx := hsolBx) (r := r) hVr0map ha hu
  let Ωa0 : Set (ℂ × (Fin k → ℂ) × ℂ) :=
    {p : ℂ × (Fin k → ℂ) × ℂ | p.2.2 ∈ Vr0 ∧ (a + p.1, ba p.2.2 + p.2.1, τ p.2.2) ∈ Ω}
  have hΩa0Analytic :
      AnalyticOnNhd ℂ
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦ F (a + p.1) (ba p.2.2 + p.2.1) (τ p.2.2))
        Ωa0 := by
    -- The recentered system is obtained from the original one by the affine `x`-shift and by
    -- adding the analytic seed-value curve in the dependent variable.
    simpa [Ωa0, ba, τ] using
      seedRecenteredRhsAnalyticOnDomain
        (hF := hF) (t0 := t0) (r := r) (a := a) (ba := ba) hbaVr0
  have hΩa0Origin : ((0 : ℂ), (0 : Fin k → ℂ), 0) ∈ Ωa0 := by
    refine ⟨h0Vr0, ?_⟩
    have hbase := hsolBx t0 ht0Vx
    have hgraph :
        ((a : ℂ), φ (a, t0)) ∈
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t0) ∈ Ω} :=
      hbase.mapsTo ha
    simpa [Ωa0, ba, τ, Function.update] using hgraph
  have hBaOpen : IsOpen Ba := hTranslatedDomain.1
  have h0Ba : (0 : ℂ) ∈ Ba := hTranslatedDomain.2.2.1
  have hRecenteredOrigin :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (a + p.1, τ p.2) - ba p.2)
        ((0 : ℂ), 0) := by
    -- The recentered origin germ is now a direct instance of the extracted seed-recentering
    -- helper.
    simpa [ba, τ] using
      seedRecenteredOriginAnalyticAt
        (φ := φ) (t0 := t0) r (a := a) hseed (hbaVr0 0 h0Vr0)
  have hLocalPatch :
      ∃ U0 Vr1 : Set ℂ,
        IsOpen U0 ∧
        IsOpen Vr1 ∧
        (0 : ℂ) ∈ U0 ∧
        (0 : ℂ) ∈ Vr1 ∧
        U0 ⊆ Ba ∧
        AnalyticOnNhd ℂ
          (fun p : ℂ × ℂ ↦ φ (a + p.1, τ p.2) - ba p.2)
          (U0 ×ˢ Vr1) := by
    -- The solved local step is exactly the generic product-patch lemma on the recentered germ.
    exact
      localProductPatchWithinOpenXDomain
        (ψ := fun p : ℂ × ℂ ↦ φ (a + p.1, τ p.2) - ba p.2)
        hBaOpen h0Ba hRecenteredOrigin
  let ψa : ℂ × ℂ → Fin k → ℂ := fun p ↦ φ (a + p.1, τ p.2) - ba p.2
  have hψaOrigin :
      AnalyticAt ℂ ψa ((0 : ℂ), 0) := by
    -- Repackage the origin germ in the stable local notation used by the continuation argument.
    simpa [ψa] using hRecenteredOrigin
  have hBaConnected : IsConnected Ba := ⟨⟨0, h0Ba⟩, hTranslatedDomain.2.1⟩
  have hBaPathConnected : IsPathConnected Ba :=
    (hBaOpen.isConnected_iff_isPathConnected).1 hBaConnected
  have hTargetBa : (x0 - a : ℂ) ∈ Ba := hTranslatedDomain.2.2.2
  let γ : Path 0 (x0 - a) := (hBaPathConnected.joinedIn 0 h0Ba (x0 - a) hTargetBa).somePath
  have hγBa : ∀ s : I, γ s ∈ Ba := by
    intro s
    exact (hBaPathConnected.joinedIn 0 h0Ba (x0 - a) hTargetBa).somePath_mem s
  let R : Set I := {s : I | AnalyticAt ℂ ψa (γ s, 0)}
  have h0R : (0 : I) ∈ R := by
    -- The reachable-time set starts at the translated origin because `γ` begins at `0`.
    simpa [R, ψa, γ, Path.source] using hψaOrigin
  have hContinue :
      ∀ {u v : I}, u ≤ v → u ∈ R → v ∈ R := by
    intro u v huv huR
    let Bu : Set ℂ := {ξ : ℂ | γ u + ξ ∈ Ba}
    have huR' : AnalyticAt ℂ ψa (γ u, 0) := by
      simpa [R] using huR
    have hBuData :
        IsOpen Bu ∧
          IsPreconnected Bu ∧
          (0 : ℂ) ∈ Bu ∧
          (γ v - γ u : ℂ) ∈ Bu := by
      -- Recenter the translated `x`-domain at the reachable seed time `u`.
      simpa [Bu] using
        translatedSubpathDomainBetweenReachableTimes
          hBaOpen hTranslatedDomain.2.1 γ hγBa
    have hSeedTranslated :
        AnalyticAt ℂ
          (fun p : ℂ × ℂ ↦ ψa (γ u + p.1, p.2) - ψa (γ u, p.2))
          ((0 : ℂ), 0) := by
      -- The reachable seed germ can be translated back to the origin and recentered there.
      simpa using
        recenteredSeedDifferenceAnalyticAt (ψa := ψa) (ξ := γ u) huR'
    -- TODO: recenter the already-recentered system at the reachable seed `γ u`, package the
    -- twice-recentered RHS and slice family on `Bu`, and rerun the owner/comparison-family
    -- pipeline to obtain analyticity at `(γ v - γ u, 0)`, hence at time `v`.
    -- Route correction: this replaces the failed first-bad-time shell by a direct reachable-seed
    -- continuation step.
    sorry
  have hReachTarget :
      AnalyticAt ℂ ψa (x0 - a, 0) := by
    have h1R : (1 : I) ∈ R := by
      -- Route correction: continue directly from the translated origin time `0` to the target
      -- time `1` instead of reentering the old first-bad-time contradiction.
      exact hContinue (show (0 : I) ≤ 1 by simp) h0R
    -- Once the reachable-time invariant reaches `1`, the path endpoint is exactly `x0 - a`.
    simpa [R, Path.target] using h1R
  have hTranslateTarget :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ ψa (p.1 - a, p.2))
        (x0, 0) := by
    have hshift :
        AnalyticAt ℂ (fun p : ℂ × ℂ ↦ (p.1 - a, p.2)) (x0, 0) := by
      -- Shift the recentered target `(x₀ - a, 0)` back to the original point `(x₀, 0)`.
      simpa [sub_eq_add_neg] using
        ((analyticAt_fst : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.1) (x0, 0)).sub
          analyticAt_const).prod
          (analyticAt_snd : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) (x0, 0))
    exact hReachTarget.comp_of_eq hshift (by simp)
  have hTranslateTargetEq :
      (fun p : ℂ × ℂ ↦ ψa (p.1 - a, p.2)) =
        fun p : ℂ × ℂ ↦ φ (p.1, τ p.2) - ba p.2 := by
    -- Undoing the affine `x`-shift recovers the original translated slice minus the seed curve.
    funext p
    simp [ψa, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hSeedCurveAt :
      AnalyticAt ℂ (fun p : ℂ × ℂ ↦ ba p.2) (x0, 0) := by
    have hu :
        AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2) (x0, 0) :=
      analyticAt_snd
    -- The seed-value curve only depends on the translated parameter variable.
    simpa using (hbaVr0 0 h0Vr0).comp_of_eq hu rfl
  have hSumEq :
      (fun p : ℂ × ℂ ↦ (φ (p.1, τ p.2) - ba p.2) + ba p.2) =
        fun p : ℂ × ℂ ↦ φ (p.1, τ p.2) := by
    -- Adding back the seed curve cancels the recentering subtraction pointwise.
    funext p
    abel
  -- Add back the analytic seed-value curve after undoing the `x`-translation.
  exact hSumEq ▸ ((hTranslateTargetEq ▸ hTranslateTarget).add hSeedCurveAt)

/-- Helper for Cartan section28 0001_Theorem_2: if a point of the chosen preconnected `x`-domain
lies in the closure of the translated analyticity locus, then the translated slice should continue
analytically to that point. -/
private theorem translatedCoordinateSliceClosureStep
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {B0 : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hB0 : IsOpen B0) (hB0Preconnected : IsPreconnected B0) (h0B0 : (0 : ℂ) ∈ B0)
    (hsolB0 :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          B0
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    (hVr' : IsOpen Vr') (h0Vr' : (0 : ℂ) ∈ Vr')
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
    {ρu : NNReal} (hρupos : 0 < ρu) (hρuR : (ρu : ENNReal) < R)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu)
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
            0)
    {x0 : ℂ}
    (hx0 : x0 ∈ B0)
    (hx0closure :
      x0 ∈ closure {x : ℂ |
        AnalyticAt ℂ
          (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
          (x, 0)}) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (x0, 0) := by
  let S : Set ℂ := {x : ℂ |
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (x, 0)}
  rcases (mem_closure_iff_nhds.1 hx0closure) B0 (hB0.mem_nhds hx0) with ⟨a, haB0, haS⟩
  -- The wrapper is now reduced to the single missing seed-continuation theorem on the original
  -- preconnected domain `B0`, which already contains the distinguished base point `0`.
  exact
    translatedCoordinateSliceContinuationFromSeedRecentered
      (hF := hF) (Bx := B0) (Vx := Vx) (Vr' := Vr') (φ := φ)
      hB0 hB0Preconnected hsolB0 (t0 := t0) r hVr' h0Vr' hVr'map
      hQtrBall hρupos hρuR hVr'norm hQsliceCanonical haB0 hx0 haS

/-- Helper for Cartan section28 0001_Theorem_2: the translated analyticity locus is relatively
closed inside the chosen preconnected `x`-domain once the closure-step continuation theorem is
available. -/
private theorem translatedCoordinateSliceAnalyticLocusClosedOnChosenDomain
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {B0 : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hB0 : IsOpen B0) (hB0Preconnected : IsPreconnected B0) (h0B0 : (0 : ℂ) ∈ B0)
    (hsolB0 :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          B0
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    (hVr' : IsOpen Vr') (h0Vr' : (0 : ℂ) ∈ Vr')
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
    {ρu : NNReal} (hρupos : 0 < ρu) (hρuR : (ρu : ENNReal) < R)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu)
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
    closure {x : ℂ |
        AnalyticAt ℂ
          (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
          (x, 0)} ∩ B0 ⊆
      {x : ℂ |
        AnalyticAt ℂ
          (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
          (x, 0)} := by
  intro x hx
  -- The relative-closedness claim is exactly the closure-step theorem specialized to `x`.
  exact
    translatedCoordinateSliceClosureStep
      (hF := hF) (B0 := B0) (Vx := Vx) (Vr' := Vr') (φ := φ)
      hB0 hB0Preconnected h0B0 hsolB0 (t0 := t0) r hVr' h0Vr' hVr'map
      hQtrBall hρupos hρuR hVr'norm hQsliceCanonical hx.2 hx.1

/-- Helper for Cartan section28 0001_Theorem_2: after all owner-level data on a chosen
preconnected `x`-domain `B0` have been assembled, the remaining task is the geometric
comparison-family step that upgrades those owners to joint analyticity at an arbitrary
`(x0, 0) ∈ B0 ×ˢ Vr'`. -/
private theorem analyticAt_translatedCoordinateSlice_fromChosenTaylorDomain
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {B0 : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hB0 : IsOpen B0) (hB0Preconnected : IsPreconnected B0) (h0B0 : (0 : ℂ) ∈ B0)
    (hsolB0 :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          B0
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (r : Fin j)
    (hVr' : IsOpen Vr') (h0Vr' : (0 : ℂ) ∈ Vr')
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
    {ρu : NNReal} (hρupos : 0 < ρu) (hρuR : (ρu : ENNReal) < R)
    (hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu)
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
            0)
    {x0 : ℂ} (hx0 : x0 ∈ B0) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (x0, 0) := by
  rcases
      translatedCoordinateSliceAnalyticOnProducedDomain
        (hF := hF) hB0 hB0Preconnected h0B0 hsolB0
        (r := r) hVr' h0Vr' hVr'map hQtrBall hρupos hρuR hVr'norm hQsliceCanonical with
    ⟨Bseed, _hBseed, _hBseedPreconnected, h0Bseed, hBseedSub, hseedAnalytic⟩
  let S : Set ℂ := {x : ℂ |
    AnalyticAt ℂ
      (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
      (x, 0)}
  have hSopen : IsOpen S := by
    -- The analytic locus in `(x, u)` is open, so its zero-parameter section is open in `x`.
    simpa [S] using translatedCoordinateSliceAnalyticPointsOpen (φ := φ) (t0 := t0) r
  have hseedSubS : Bseed ⊆ S := by
    intro x hx
    exact hseedAnalytic x hx
  have h0S : (0 : ℂ) ∈ S := hseedSubS h0Bseed
  -- Route correction: the proof has been reduced to a pure continuation problem inside `B0`.
  -- The produced seed domain `Bseed` already gives a nonempty subset of the open locus `S`.
  -- Once `S` is also known to be relatively closed in `B0`, preconnectedness forces `B0 ⊆ S`.
  have hSeedNonempty : (B0 ∩ S).Nonempty := by
    exact ⟨0, hBseedSub h0Bseed, h0S⟩
  have hSclosedOnB0 : closure S ∩ B0 ⊆ S := by
    -- Package the continuation step as the exact relative-closedness input needed below.
    simpa [S] using
      translatedCoordinateSliceAnalyticLocusClosedOnChosenDomain
        (hF := hF) (B0 := B0) (Vx := Vx) (Vr' := Vr') (φ := φ)
        hB0 hB0Preconnected h0B0 hsolB0 (t0 := t0) r hVr' h0Vr' hVr'map
        hQtrBall hρupos hρuR hVr'norm hQsliceCanonical
  have hB0SubS : B0 ⊆ S := by
    -- The open translated analyticity locus contains `0`, and relative closedness upgrades that
    -- seed to the whole preconnected domain `B0`.
    exact hB0Preconnected.subset_of_closure_inter_subset hSopen hSeedNonempty hSclosedOnB0
  exact hB0SubS hx0

/-- Helper for Cartan section28 0001_Theorem_2: on a fixed `x`-ball around `0`, the translated
scalar slice theorem gives the exact parameter-coordinate analyticity needed for the Hartogs
upgrade. -/
private theorem translatedCoordinateSliceProducedNeighborhoodData
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Rx : ℝ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hRx : 0 < Rx) (hVx : IsOpen Vx)
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          (Metric.ball (0 : ℂ) Rx)
          (fun x ↦ φ (x, t)))
    {z : ℂ × (Fin j → ℂ)} (hz : z ∈ Metric.ball (0 : ℂ) Rx ×ˢ Vx) (r : Fin j) :
    ∃ B0 Bx0 : Set ℂ,
      IsOpen B0 ∧
      IsPreconnected B0 ∧
      (0 : ℂ) ∈ B0 ∧
      z.1 ∈ B0 ∧
      B0 ⊆ Metric.ball (0 : ℂ) Rx ∧
      IsOpen Bx0 ∧
      IsPreconnected Bx0 ∧
      (0 : ℂ) ∈ Bx0 ∧
      Bx0 ⊆ B0 ∧
      ∀ x0 ∈ Bx0,
        AnalyticAt ℂ
          (fun p : ℂ × ℂ ↦ φ (p.1, Function.update z.2 r (z.2 r + p.2)))
          (x0, 0) := by
  rcases hz with ⟨hzx, hzt⟩
  rcases choosePreconnectedSubballInsideBall_mem hRx hzx with
    ⟨B0, hB0, hB0Preconnected, h0B0, hzB0, hB0subBall⟩
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
    have hbase := hsol t ht
    -- Restrict the original slice solution family to the inner preconnected `x`-ball.
    refine hbase.restrict hB0 h0B0 hB0subBall ?_
    intro x hx
    exact hbase.mapsTo (hB0subBall hx)
  rcases exists_coordinateUpdateNeighborhood hVx hzt r with
    ⟨Vr, hVr, h0Vr, hVrmap⟩
  rcases translatedCoordinateUpdate_rhsHasFPowerSeriesAtOrigin
      (hF := hF) (hsol := hsolB0) (t0 := z.2) hzt r with
    ⟨Qtr, hQtrAt, _hQtrrad⟩
  rcases hQtrAt with ⟨R, hQtrBall⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hQtrBall.r_pos with ⟨ρu, hρupos, hρuR⟩
  have hρupos' : 0 < ρu := by
    simpa [NNReal.coe_pos] using hρupos
  rcases exists_smallScalarBallInside hVr h0Vr hρupos' with
    ⟨Rv, hRvpos, hRvsubVr, hRvnorm⟩
  let Vr' : Set ℂ := Metric.ball (0 : ℂ) Rv
  have hVr' : IsOpen Vr' := Metric.isOpen_ball
  have h0Vr' : (0 : ℂ) ∈ Vr' := Metric.mem_ball_self hRvpos
  have hVr'map :
      Set.MapsTo (fun u ↦ Function.update z.2 r (z.2 r + u)) Vr' Vx := by
    intro u hu
    exact hVrmap (hRvsubVr hu)
  have hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu := by
    intro u hu
    exact hRvnorm u hu
  have hQsliceCanonical :
      ∀ u ∈ Vr',
        ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update z.2 r (z.2 r + u)))
            Qslice
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          HasFPowerSeriesAt
            (fun x ↦ φ (x, Function.update z.2 r (z.2 r + u)))
            (vectorOfScalarsSeries fun m ↦
              PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
            0 := by
    -- The translated Taylor owner already gives the canonical scalar owner for each frozen slice.
    exact
      translatedCoordinateSliceCanonicalOwnersOnBall
        (F := F) (Ω := Ω) (B0 := B0) (Vx := Vx) (Vr' := Vr') (φ := φ)
        (t0 := z.2) r hsolB0 hVr'map (Qtr := Qtr) (R := R) hQtrBall hρuR hVr'norm
  rcases
      translatedCoordinateSliceAnalyticOnProducedDomain
        (hF := hF) hB0 hB0Preconnected h0B0 hsolB0
        (r := r) hVr' h0Vr' hVr'map hQtrBall hρupos' hρuR hVr'norm hQsliceCanonical with
    ⟨Bx0, hBx0, hBx0Preconnected, h0Bx0, hBx0sub, htranslatedOnBx0⟩
  -- This helper isolates the completed source-faithful prefix: an inner preconnected `x`-ball
  -- containing the live point, plus a produced translated analyticity neighborhood around `0`.
  exact ⟨B0, Bx0, hB0, hB0Preconnected, h0B0, hzB0, hB0subBall, hBx0, hBx0Preconnected,
    h0Bx0, hBx0sub, htranslatedOnBx0⟩

/-- Helper for Cartan section28 0001_Theorem_2: on a fixed `x`-ball around `0`, the translated
scalar slice theorem gives the exact parameter-coordinate analyticity needed for the Hartogs
upgrade. -/
private theorem analyticAt_parameterCoordinateSliceOnBall
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Rx : ℝ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hRx : 0 < Rx) (hVx : IsOpen Vx)
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          (Metric.ball (0 : ℂ) Rx)
          (fun x ↦ φ (x, t)))
    {z : ℂ × (Fin j → ℂ)} (hz : z ∈ Metric.ball (0 : ℂ) Rx ×ˢ Vx) (r : Fin j) :
    AnalyticAt ℂ (fun w ↦ φ (z.1, Function.update z.2 r w)) (z.2 r) := by
  rcases hz with ⟨hzx, hzt⟩
  rcases choosePreconnectedSubballInsideBall_mem hRx hzx with
    ⟨B0, hB0, hB0Preconnected, h0B0, hzB0, hB0subBall⟩
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
    have hbase := hsol t ht
    -- Restrict the original slice solution family to the inner preconnected `x`-ball.
    refine hbase.restrict hB0 h0B0 hB0subBall ?_
    intro x hx
    exact hbase.mapsTo (hB0subBall hx)
  rcases exists_coordinateUpdateNeighborhood hVx hzt r with
    ⟨Vr, hVr, h0Vr, hVrmap⟩
  rcases translatedCoordinateUpdate_rhsHasFPowerSeriesAtOrigin
      (hF := hF) (hsol := hsolB0) (t0 := z.2) hzt r with
    ⟨Qtr, hQtrAt, _hQtrrad⟩
  rcases hQtrAt with ⟨R, hQtrBall⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hQtrBall.r_pos with ⟨ρu, hρupos, hρuR⟩
  have hρupos' : 0 < ρu := by
    simpa [NNReal.coe_pos] using hρupos
  rcases exists_smallScalarBallInside hVr h0Vr hρupos' with
    ⟨Rv, hRvpos, hRvsubVr, hRvnorm⟩
  let Vr' : Set ℂ := Metric.ball (0 : ℂ) Rv
  have hVr' : IsOpen Vr' := Metric.isOpen_ball
  have h0Vr' : (0 : ℂ) ∈ Vr' := Metric.mem_ball_self hRvpos
  have hVr'map :
      Set.MapsTo (fun u ↦ Function.update z.2 r (z.2 r + u)) Vr' Vx := by
    intro u hu
    exact hVrmap (hRvsubVr hu)
  have hVr'norm : ∀ u ∈ Vr', ‖u‖ < ρu := by
    intro u hu
    exact hRvnorm u hu
  have hQsliceCanonical :
      ∀ u ∈ Vr',
        ∃ Qslice : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ),
          HasFPowerSeriesAt
            (fun p : ℂ × (Fin k → ℂ) ↦
              F p.1 p.2 (Function.update z.2 r (z.2 r + u)))
            Qslice
            ((0 : ℂ), (0 : Fin k → ℂ)) ∧
          HasFPowerSeriesAt
            (fun x ↦ φ (x, Function.update z.2 r (z.2 r + u)))
            (vectorOfScalarsSeries fun m ↦
              PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Qslice))
            0 :=
    translatedCoordinateSliceCanonicalOwnersOnBall
      (F := F) (Ω := Ω) (B0 := B0) (Vx := Vx) (Vr' := Vr') (φ := φ)
      (t0 := z.2) r hsolB0 hVr'map (Qtr := Qtr) (R := R) hQtrBall hρuR hVr'norm
  have htranslated :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update z.2 r (z.2 r + p.2)))
        (z.1, 0) := by
    -- Route correction: the owner-level setup is complete on the chosen `x`-ball `B0`.
    -- The unresolved step is now isolated to the comparison family on `B0 ×ˢ Vr'`.
    exact
      analyticAt_translatedCoordinateSlice_fromChosenTaylorDomain
        (hF := hF) (B0 := B0) (Vx := Vx) (Vr' := Vr') (φ := φ)
        hB0 hB0Preconnected h0B0 hsolB0 (t0 := z.2) r hVr' h0Vr' hVr'map
        hQtrBall hρupos' hρuR hVr'norm hQsliceCanonical hzB0
  -- The translated analytic germ pulls back to the original active coordinate by the affine
  -- parameter update `w = z.2 r + u`.
  simpa using
    analyticAt_parameterUpdate_of_translated (φ := φ) (t0 := z.2) r htranslated

/-- Helper for Cartan section28 0001_Theorem_2: the final theorem only needs a local Hartogs
upgrade on one fixed product neighborhood around the origin, so we may shrink the `x`-domain to a
concrete ball before invoking the parameter-coordinate branch. -/
private theorem analyticAt_origin_of_holomorphic_ode_solution_family_local
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Bx : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hBx : IsOpen Bx) (_hBxPreconnected : IsPreconnected Bx) (hVx : IsOpen Vx)
    (h0Bx : (0 : ℂ) ∈ Bx) (h0Vx : (0 : Fin j → ℂ) ∈ Vx)
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t))) :
    AnalyticAt ℂ φ ((0 : ℂ), 0) := by
  -- Route correction: the old proof asked for parameter analyticity on an arbitrary preconnected
  -- `x`-domain. The local theorem only needs a fixed ball around `0`, so shrink once inside `Bx`
  -- and run Hartogs on that smaller product neighborhood.
  rcases Metric.mem_nhds_iff.mp (hBx.mem_nhds h0Bx) with ⟨Rx, hRx, hRxsub⟩
  let Bx0 : Set ℂ := Metric.ball (0 : ℂ) Rx
  have hBx0 : IsOpen Bx0 := Metric.isOpen_ball
  have h0Bx0 : (0 : ℂ) ∈ Bx0 := Metric.mem_ball_self hRx
  have hBx0sub : Bx0 ⊆ Bx := by
    simpa [Bx0] using hRxsub
  have hsolBx0 :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx0
          (fun x ↦ φ (x, t)) := by
    intro t ht
    have hbase := hsol t ht
    -- Restrict the original slice solution family to the fixed ball used in the local Hartogs
    -- argument.
    refine hbase.restrict hBx0 h0Bx0 hBx0sub ?_
    intro x hx
    exact hbase.mapsTo (hBx0sub hx)
  -- Transport the local product neighborhood to `Fin (j + 1) → ℂ` with the last coordinate
  -- reserved for `x`.
  refine analyticAt_pi_iff.mpr ?_
  intro i
  let unpack : (Fin (j + 1) → ℂ) → ℂ × (Fin j → ℂ) := fun z ↦
    (z (Fin.last j), fun r ↦ z (Fin.castAdd 1 r))
  let pack : ℂ × (Fin j → ℂ) → Fin (j + 1) → ℂ := fun p ↦
    Fin.lastCases p.1 p.2
  let g : (Fin (j + 1) → ℂ) → ℂ := fun z ↦ φ (unpack z) i
  let D : Set (Fin (j + 1) → ℂ) := unpack ⁻¹' (Bx0 ×ˢ Vx)
  have hUnpackLast :
      Continuous fun z : Fin (j + 1) → ℂ ↦ z (Fin.last j) := by
    exact ContinuousLinearMap.continuous
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (j + 1) ↦ ℂ) (Fin.last j))
  have hUnpackBlock :
      Continuous fun z : Fin (j + 1) → ℂ ↦ fun r : Fin j ↦ z (Fin.castAdd 1 r) := by
    exact continuous_pi fun r ↦
      ContinuousLinearMap.continuous
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (j + 1) ↦ ℂ) (Fin.castAdd 1 r))
  have hD : IsOpen D := by
    -- The transported local product domain stays open because the unpacking map is continuous.
    simpa [D, unpack] using (hBx0.prod hVx).preimage (hUnpackLast.prodMk hUnpackBlock)
  have h0D : (0 : Fin (j + 1) → ℂ) ∈ D := by
    simpa [D, unpack] using show ((0 : ℂ), (0 : Fin j → ℂ)) ∈ Bx0 ×ˢ Vx from ⟨h0Bx0, h0Vx⟩
  have hsep :
      ∀ z ∈ D, ∀ r : Fin (j + 1),
        AnalyticAt ℂ (fun w ↦ g (Function.update z r w)) (z r) := by
    intro z hz r
    have hzProd : unpack z ∈ Bx0 ×ˢ Vx := hz
    refine Fin.lastCases ?_ ?_ r
    · have hslice :
          AnalyticOnNhd ℂ (fun x ↦ φ (x, (unpack z).2)) Bx0 :=
        solutionSliceAnalyticOnNhd hsolBx0 (unpack z).2 hzProd.2
      have hAt :
          AnalyticAt ℂ (fun x ↦ φ (x, (unpack z).2)) (unpack z).1 :=
        hslice (unpack z).1 hzProd.1
      have hAti :
          AnalyticAt ℂ (fun x ↦ φ (x, (unpack z).2) i) (unpack z).1 :=
        analyticAt_pi_iff.mp hAt i
      have hlast :
          (fun w ↦ g (Function.update z (Fin.last j) w)) =
            fun w ↦ φ (w, (unpack z).2) i := by
        funext w
        have hparam :
            (fun r : Fin j ↦ Function.update z (Fin.last j) w (Fin.castAdd 1 r)) =
              (unpack z).2 := by
          funext r
          have hne : Fin.castAdd 1 r ≠ Fin.last j := by
            intro h
            exact Nat.ne_of_lt r.is_lt
              (by simpa [Fin.val_castAdd, Fin.val_last] using congrArg Fin.val h)
          simp [unpack, Function.update, hne]
        simp [g, unpack, hparam]
      rw [hlast]
      simpa [unpack] using hAti
    · intro s
      have hAt :
          AnalyticAt ℂ
            (fun w ↦ φ ((unpack z).1, Function.update (unpack z).2 s w))
            ((unpack z).2 s) :=
        analyticAt_parameterCoordinateSliceOnBall
          (hF := hF) (Rx := Rx) (Vx := Vx) (φ := φ)
          hRx hVx (hsol := hsolBx0) (z := unpack z) hzProd s
      have hAti :
          AnalyticAt ℂ
            (fun w ↦ φ ((unpack z).1, Function.update (unpack z).2 s w) i)
            ((unpack z).2 s) :=
        analyticAt_pi_iff.mp hAt i
      have hblock :
          (fun w ↦ g (Function.update z s.castSucc w)) =
            fun w ↦ φ ((unpack z).1, Function.update (unpack z).2 s w) i := by
        funext w
        have hunpack :
            unpack (Function.update z s.castSucc w) =
              ((unpack z).1, Function.update (unpack z).2 s w) := by
          refine Prod.ext ?_ ?_
          · have hne : Fin.last j ≠ s.castSucc := by
              intro h
              exact Nat.ne_of_lt s.is_lt
                (by simpa [Fin.val_last] using congrArg Fin.val h.symm)
            simp [unpack, Function.update, hne]
          · ext r
            by_cases hrs : r = s
            · subst r
              have hcast : Fin.castAdd 1 s = s.castSucc := rfl
              simp [unpack, Function.update, hcast]
            · have hne : Fin.castAdd 1 r ≠ s.castSucc := by
                intro h
                apply hrs
                exact Fin.ext <| by simpa [Fin.val_castAdd] using congrArg Fin.val h
              simp [unpack, Function.update, hrs, hne]
        simp [g, hunpack]
      rw [hblock]
      simpa [unpack] using hAti
  have hg : AnalyticOnNhd ℂ g D := separately_holomorphic_analyticOnNhd hD hsep
  have hgAt : AnalyticAt ℂ g (0 : Fin (j + 1) → ℂ) := hg 0 h0D
  have hPack : AnalyticAt ℂ pack ((0 : ℂ), (0 : Fin j → ℂ)) := by
    -- The inverse transport back to `Fin (j + 1) → ℂ` is coordinatewise linear.
    refine AnalyticAt.pi fun r ↦ ?_
    refine Fin.lastCases ?_ ?_ r
    · simpa [pack] using
        (analyticAt_fst : AnalyticAt ℂ (fun p : ℂ × (Fin j → ℂ) ↦ p.1) ((0 : ℂ), 0))
    · intro s
      simpa [pack] using
        (analyticAt_pi_iff.mp
          (analyticAt_snd : AnalyticAt ℂ (fun p : ℂ × (Fin j → ℂ) ↦ p.2) ((0 : ℂ), 0)) s)
  have hunpackPack : ∀ p : ℂ × (Fin j → ℂ), unpack (pack p) = p := by
    intro p
    refine Prod.ext ?_ ?_
    · simp [unpack, pack]
    · funext r
      have hcast : Fin.castAdd 1 r = r.castSucc := rfl
      simp [unpack, pack, hcast]
  have hcomp :
      AnalyticAt ℂ (fun p : ℂ × (Fin j → ℂ) ↦ g (pack p)) ((0 : ℂ), 0) :=
    hgAt.comp_of_eq hPack (by
      funext r
      refine Fin.lastCases ?_ ?_ r <;> simp [pack])
  have hEq :
      (fun p : ℂ × (Fin j → ℂ) ↦ g (pack p)) = fun p ↦ φ p i := by
    funext p
    simpa [g] using congrArg (fun q : ℂ × (Fin j → ℂ) ↦ φ q i) (hunpackPack p)
  rw [hEq] at hcomp
  exact hcomp

/-- Theorem 2: let `F (x, y, t)` be holomorphic on a coefficient domain `Ω` in the sense of
`AnalyticOnNhd`, and let `φ (x, t)` be a family of local solutions with zero initial value such
that, on an open neighborhood `W` of `((0 : ℂ), 0)` in `(x, t)`-space and for each parameter
`t` near `0`, the slice `x ↦ φ (x, t)` is a local holomorphic solution of
`dφ/dx = F (x, φ, t)` in the sense of `IsHolomorphicSystemSolutionOn`. Then the solution
components `φᵢ (x, t₁, ..., tⱼ)` are analytic in the `j + 1` variables `(x, t₁, ..., tⱼ)` near
the origin. -/
theorem analyticAt_origin_of_holomorphic_ode_solution_family
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {V : Set (Fin j → ℂ)} {W : Set (ℂ × (Fin j → ℂ))}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hV : IsOpen V) (h0V : (0 : Fin j → ℂ) ∈ V)
    (hW : IsOpen W) (h0W : ((0 : ℂ), 0) ∈ W)
    (hsol :
      ∀ t ∈ V,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          {x : ℂ | (x, t) ∈ W}
          (fun x ↦ φ (x, t))) :
    AnalyticAt ℂ φ ((0 : ℂ), 0) := by
  -- Route correction: the global comparison-family wrapper is stronger than the theorem needs.
  -- Shrink once to a preconnected `x`-ball and prove joint analyticity only on that local product
  -- neighborhood around `((0 : ℂ), 0)`, then evaluate at the origin.
  rcases exists_product_neighborhood_subordinate_to_W hW h0W with
    ⟨Ux0, Vw, hUx0, hVw, h0Ux0, h0Vw, hprodW⟩
  rcases choosePreconnectedXNeighborhood hUx0 h0Ux0 with
    ⟨Bx, hBx, hBxPreconnected, h0Bx, hBxsub⟩
  let Vx : Set (Fin j → ℂ) := V ∩ Vw
  have hVx : IsOpen Vx := hV.inter hVw
  have h0Vx : (0 : Fin j → ℂ) ∈ Vx := ⟨h0V, h0Vw⟩
  have hVxsub : Vx ⊆ V := fun t ht ↦ ht.1
  have hWsub : Bx ×ˢ Vx ⊆ W := by
    intro z hz
    exact hprodW ⟨hBxsub hz.1, hz.2.2⟩
  have hsolBx :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Bx
          (fun x ↦ φ (x, t)) := by
    intro t ht
    have hbase := hsol t ht.1
    refine hbase.restrict hBx h0Bx ?_ ?_
    · intro x hx
      exact hWsub ⟨hx, ht⟩
    · intro x hx
      exact hbase.mapsTo (hWsub ⟨hx, ht⟩)
  -- The remaining proof burden is exactly the local Hartogs step on the fixed ball `Bx ×ˢ Vx`.
  exact analyticAt_origin_of_holomorphic_ode_solution_family_local
    (hF := hF) (Bx := Bx) (Vx := Vx) (φ := φ)
    hBx hBxPreconnected hVx h0Bx h0Vx hsolBx
