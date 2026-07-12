import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».TranslatedCanonicalOwners
import Mathlib

open Filter
open Set

open scoped Topology

/-- Helper for Cartan section28 0001_Theorem_2: an analytic germ in the translated scalar
parameter `u` pulls back to the original active parameter coordinate by the affine change
`u = w - t₀ r`. -/
theorem analyticAt_parameterUpdate_of_translated
    {k j : ℕ} {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j) {x0 u0 : ℂ}
    (h :
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (x0, u0)) :
    AnalyticAt ℂ (fun w ↦ φ (x0, Function.update t0 r w)) (t0 r + u0) := by
  -- Compose the translated germ with the affine map `w ↦ (x0, w - t₀ r)`.
  have hmap :
      AnalyticAt ℂ (fun w : ℂ ↦ (x0, w - t0 r)) (t0 r + u0) := by
    simpa [sub_eq_add_neg] using
      (analyticAt_const.prod
        ((analyticAt_id : AnalyticAt ℂ (fun w : ℂ ↦ w) (t0 r + u0)).sub analyticAt_const))
  have hcomp := h.comp_of_eq hmap (by simp)
  -- After the affine substitution, the translated parameter coordinate is the original one.
  convert hcomp using 1
  funext w
  simp [Function.comp]

/-- Helper for Cartan section28 0001_Theorem_2: an open scalar neighborhood of `0` contains a
smaller ball on which every point satisfies the required strict norm bound. -/
theorem exists_smallScalarBallInside
    {Vr : Set ℂ} (hVr : IsOpen Vr) (h0Vr : (0 : ℂ) ∈ Vr)
    {ρu : NNReal} (hρupos : 0 < ρu) :
    ∃ Rv : ℝ,
      0 < Rv ∧
      Metric.ball (0 : ℂ) Rv ⊆ Vr ∧
      ∀ u ∈ Metric.ball (0 : ℂ) Rv, ‖u‖ < ρu := by
  -- First shrink the open neighborhood to a concrete metric ball around `0`.
  rcases Metric.mem_nhds_iff.mp (hVr.mem_nhds h0Vr) with ⟨rv, hrvpos, hrvsub⟩
  refine ⟨min rv ρu, lt_min hrvpos hρupos, ?_, ?_⟩
  · intro u hu
    have hlt : ‖u‖ < min rv ρu := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    exact hrvsub <| by
      simpa [Metric.mem_ball, dist_eq_norm] using lt_of_lt_of_le hlt (min_le_left _ _)
  · intro u hu
    have hlt : ‖u‖ < min rv ρu := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    exact lt_of_lt_of_le hlt (min_le_right _ _)

/-- Helper for Cartan section28 0001_Theorem_2: an open neighborhood of a point in `(x,u)`-space
contains a smaller product neighborhood around that same point. -/
theorem exists_product_neighborhood_subordinate_to_point
    {W : Set (ℂ × ℂ)} {x0 u0 : ℂ}
    (hW : IsOpen W) (hzW : (x0, u0) ∈ W) :
    ∃ Ux : Set ℂ, ∃ Vu : Set ℂ,
      IsOpen Ux ∧ IsOpen Vu ∧
      x0 ∈ Ux ∧ u0 ∈ Vu ∧
      Ux ×ˢ Vu ⊆ W := by
  -- First pass from the open neighborhood in the product space to neighborhood filters.
  have hW_nhds : W ∈ 𝓝 (x0, u0) :=
    hW.mem_nhds hzW
  rcases mem_nhds_prod_iff.mp hW_nhds with ⟨Ux, hUx, Vu, hVu, hsub⟩
  -- Then replace the filter neighborhoods by open neighborhoods of each coordinate.
  rcases _root_.mem_nhds_iff.mp hUx with ⟨Ux', hUx'sub, hUx'open, hx0Ux'⟩
  rcases _root_.mem_nhds_iff.mp hVu with ⟨Vu', hVu'sub, hVu'open, hu0Vu'⟩
  refine ⟨Ux', Vu', hUx'open, hVu'open, hx0Ux', hu0Vu', ?_⟩
  exact Set.Subset.trans (Set.prod_mono hUx'sub hVu'sub) hsub

/-- Helper for Cartan section28 0001_Theorem_2: an analytic germ at `(0,0)` inside an open
`x`-domain yields a genuine jointly analytic product patch still contained in that `x`-domain. -/
theorem localProductPatchWithinOpenXDomain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {ψ : ℂ × ℂ → E} {Bx : Set ℂ}
    (hBx : IsOpen Bx) (h0Bx : (0 : ℂ) ∈ Bx)
    (hψ0 : AnalyticAt ℂ ψ ((0 : ℂ), 0)) :
    ∃ U0 Vr0 : Set ℂ,
      IsOpen U0 ∧
      IsOpen Vr0 ∧
      (0 : ℂ) ∈ U0 ∧
      (0 : ℂ) ∈ Vr0 ∧
      U0 ⊆ Bx ∧
      AnalyticOnNhd ℂ ψ (U0 ×ˢ Vr0) := by
  -- First shrink the analytic germ to an honest open neighborhood in `(x,u)`-space.
  rcases hψ0.exists_mem_nhds_analyticOnNhd with ⟨W, hW0, hWanalytic⟩
  rcases _root_.mem_nhds_iff.mp hW0 with ⟨W0, hW0sub, hW0open, h0W0⟩
  have hW0analytic : AnalyticOnNhd ℂ ψ W0 :=
    hWanalytic.mono hW0sub
  -- Then extract a product neighborhood and intersect the `x`-factor with the ambient domain.
  rcases exists_product_neighborhood_subordinate_to_point hW0open h0W0 with
    ⟨Ux, Vu, hUx, hVu, h0Ux, h0Vu, hUxVu⟩
  let U0 : Set ℂ := Ux ∩ Bx
  refine ⟨U0, Vu, hUx.inter hBx, hVu, ⟨h0Ux, h0Bx⟩, h0Vu, ?_, ?_⟩
  · intro x hx
    exact hx.2
  · intro p hp
    exact hW0analytic p (hUxVu ⟨hp.1.1, hp.2⟩)

/-- Helper for Cartan section28 0001_Theorem_2: once the translated scalar system has been lifted
to one common Banach owner, the existing support API already produces the local `x`-domain on
which every translated slice is analytic at parameter increment `0`. -/
theorem translatedCoordinateSliceNeighborhoodFromCommonBanachOwner
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
  -- The heavy lifting is already packaged in the support theorem; this helper only exposes the
  -- produced local `x`-domain at the theorem-file boundary.
  exact
    existsTranslatedCoordinateSliceAnalyticAtZeroDomain
      (hF := hF) (hBx := hBx) (hBxPreconnected := hBxPreconnected) (hsolBx := hsolBx)
      (r := r) (hVr' := hVr') h0Vr' hVr'map hρupos hVr'norm hQBrad hQBanachEval
      hQsliceCanonical

/-- Helper for Cartan section28 0001_Theorem_2: the translated scalar-slice support API produces
one smaller `x`-domain around `0` on which every translated slice is analytic at parameter
increment `0`. -/
theorem translatedCoordinateSliceAnalyticOnProducedDomain
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
    :
    ∃ Bx0 : Set ℂ,
      IsOpen Bx0 ∧
      IsPreconnected Bx0 ∧
      (0 : ℂ) ∈ Bx0 ∧
      Bx0 ⊆ B0 ∧
      ∀ x0 ∈ Bx0,
        AnalyticAt ℂ
          (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
          (x0, 0) := by
  -- Route correction: the previous helper statement was too strong. The imported support API only
  -- yields analyticity on a produced neighborhood of `0`, so we expose exactly that frontier.
  rcases
      translatedCommonBanachOwnerPackageFromQtr
        (F := F) (t0 := t0) (r := r) (Vr' := Vr') (Qtr := Qtr) (R := R) (ρu := ρu)
        hQtrBall hρuR hVr'norm with
    ⟨QB, hQBrad, hQBanachEval⟩
  exact
    translatedCoordinateSliceNeighborhoodFromCommonBanachOwner
      (hF := hF) (hBx := hB0) (hBxPreconnected := hB0Preconnected) (hsolBx := hsolB0)
      (r := r) (hVr' := hVr') h0Vr' hVr'map hρupos hVr'norm
      (QB := QB) hQBrad hQBanachEval hQsliceCanonical

/-- Helper for Cartan section28 0001_Theorem_2: once the translated Taylor owner is fixed on a
chosen `x`-domain `B0`, the canonical scalar owner of each frozen translated slice is already
determined by the section-27 formal solution package. -/
theorem translatedCoordinateSliceCanonicalOwnersOnBall
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {B0 : Set ℂ} {Vx : Set (Fin j → ℂ)} {Vr' : Set ℂ}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j)
    (hsolB0 :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          B0
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
  -- The translated Taylor owner already packages the canonical scalar owner for each frozen
  -- parameter slice once the `x`-domain is fixed.
  exact
    translatedSliceCanonicalFormalOwner_fromTaylorBall
      (F := F) (Ω := Ω) (Bx := B0) (Vx := Vx) (Vr' := Vr') (φ := φ)
      (t0 := t0) r hsolB0 hVr'map hQtrBall hρuR hVr'norm

/-- Helper for Cartan section28 0001_Theorem_2: the `x`-points where the translated slice is
jointly analytic at parameter increment `0` form an open subset of the `x`-plane. -/
theorem translatedCoordinateSliceAnalyticPointsOpen
    {k j : ℕ} {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    {t0 : Fin j → ℂ} (r : Fin j) :
    IsOpen {x : ℂ |
      AnalyticAt ℂ
        (fun p : ℂ × ℂ ↦ φ (p.1, Function.update t0 r (t0 r + p.2)))
        (x, 0)} := by
  let e : ℂ → ℂ × ℂ := fun x ↦ (x, 0)
  have he : Continuous e := continuous_id.prodMk continuous_const
  have hopen :
      IsOpen {p : ℂ × ℂ |
        AnalyticAt ℂ
          (fun q : ℂ × ℂ ↦ φ (q.1, Function.update t0 r (t0 r + q.2)))
          p} :=
    isOpen_analyticAt ℂ _
  -- Pull the open analytic locus in `(x, u)`-space back along the zero-parameter section.
  simpa [e] using hopen.preimage he
