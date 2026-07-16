import DifferentialForms_Cartan_1970.cartan.IV.section14.«0002_Definition_IV_2_extra_2»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0001_Definition_IV_5_extra_1»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».DimensionTransport
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».TransportedSlices
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».WeightedTransport
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».TransportedCauchyTransform
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».BoundaryCauchySeries
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».ParametricPowerSeries
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».LocalSeriesBounds
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».ProductBoundaryCauchy
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».Fin2Hartogs

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the stable transported-separate,
`Fin 2`, coefficient-uniformization, and parametric-series frontiers are supplied explicitly, the
remaining higher-dimensional Hartogs reconstruction closes in theorem-local support. -/
lemma separatelyHolomorphicAtLeastTwo_analyticOnNhd_ofIH_fromFrontier_local
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    (transportedProductSeparate :
      let e := Fin.succFunEquiv ℂ (m + 1)
      let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
      ∀ p ∈ {p : (Fin (m + 1) → ℂ) × ℂ | e.symm p ∈ D},
        AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ g (x, p.2)) p.1 ∧
          AnalyticAt ℂ (fun w : ℂ ↦ g (p.1, w)) p.2)
    (fin2Hartogs :
      ∀ {D2 : Set (Fin 2 → ℂ)} {F : (Fin 2 → ℂ) → ℂ},
        IsOpen D2 →
        (∀ z ∈ D2, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i)) →
        AnalyticOnNhd ℂ F D2)
    (parametricUniform :
      ∀ {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
        {r R C : ℝ},
        0 < r →
        0 < R →
        (∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) →
        (∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) →
        AnalyticAt ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n)
          (x0, u0))
    (boundaryCoeffUniform :
      ∀ {z : Fin (m + 2) → ℂ} {ρ : ℝ},
        0 < ρ →
        let e := Fin.succFunEquiv ℂ (m + 1)
        let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
        let w0 : ℂ := (e z).2
        let r0 : ℝ := ρ / 8
        let r1 : ℝ := r0 / 2
        let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
          (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) w0 (ρ / 2)).coeff n
        Metric.ball (e z).1 (ρ / 2) ×ˢ Metric.closedBall (e z).2 (ρ / 2) ⊆
          {p : (Fin (m + 1) → ℂ) × ℂ | e.symm p ∈ D} →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ x ∈ Metric.closedBall (e z).1 r1, ∀ n : ℕ, ‖A n x‖ ≤ C / (ρ / 2 : ℝ) ^ n) :
    AnalyticOnNhd ℂ f D := by
  intro z hz
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  have hsymmCont : Continuous e.symm := by
    simpa [e] using (continuous_succFunEquiv_symm (m := m))
  have hlast : AnalyticAt ℂ (fun w ↦ g ((e z).1, w)) (e z).2 := by
    simpa [e, g] using transportedLastSlice_analyticAt (m := m) (f := f) hsep hz
  have hblockSlices :
      ∀ w : ℂ, AnalyticOnNhd ℂ (fun x ↦ g (x, w)) {x | e.symm (x, w) ∈ D} := by
    intro w
    simpa [e, g] using
      transportedFixedLastSlice_analyticOnNhd (m := m) (D := D) (f := f) ih hD hsep w
  have hcenterBlock : AnalyticAt ℂ (fun x ↦ g (x, (e z).2)) (e z).1 := by
    have hzBlock : (e z).1 ∈ {x | e.symm (x, (e z).2) ∈ D} := by
      change e.symm (e z) ∈ D
      simpa using hz
    exact hblockSlices (e z).2 (e z).1 hzBlock
  obtain ⟨ρ, hρpos, hcylTransport⟩ :=
    exists_transportCylinder_subset_of_isOpen (m := m) (D := D) hD hz
  let U : Set (Fin (m + 1) → ℂ) := Metric.ball (e z).1 (ρ / 2)
  have hρhalf_pos : 0 < ρ / 2 := by positivity
  have hcyl :
      U ×ˢ Metric.closedBall (e z).2 (ρ / 2) ⊆ {p | e.symm p ∈ D} := by
    simpa [U, e] using hcylTransport
  have hboundary :
      ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2), AnalyticOnNhd ℂ (fun x ↦ g (x, ζ)) U := by
    simpa [U] using
      transportedBoundaryBlockSlices_analyticOnNhd_ball
        (m := m) (D := D) (f := f) ih hD hsep hcyl
  have hEq :
      ∀ x ∈ U,
        Set.EqOn (fun w ↦ g (x, w))
          (fun w ↦
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
              ∮ ζ in C((e z).2, ρ / 2), (ζ - w)⁻¹ • g (x, ζ)))
          (Metric.ball (e z).2 (ρ / 2)) := by
    simpa [U] using
      transportedLastCauchyTransform_eqOn_ball
        (m := m) (D := D) (f := f) hsep hcyl
  have hGlast :
      ∀ x ∈ U,
        AnalyticOnNhd ℂ
          (fun w ↦
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
              ∮ ζ in C((e z).2, ρ / 2), (ζ - w)⁻¹ • g (x, ζ)))
          (Metric.ball (e z).2 (ρ / 2)) := by
    simpa [U] using
      transportedLastCauchyTransform_lastSlice_analyticOnNhd_ball
        (m := m) (D := D) (f := f) hsep hcyl
  have hGblock :
      ∀ w ∈ Metric.ball (e z).2 (ρ / 2),
        AnalyticOnNhd ℂ
          (fun x ↦
            ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
              ∮ ζ in C((e z).2, ρ / 2), (ζ - w)⁻¹ • g (x, ζ)))
          U := by
    simpa [U] using
      transportedLastCauchyTransform_blockSlice_analyticOnNhd_ball
        (m := m) (D := D) (f := f) ih hD hsep hcyl
  have hBoundaryIntegrand :
      ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2),
        AnalyticOnNhd ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
          (U ×ˢ Metric.ball (e z).2 (ρ / 4)) := by
    simpa [U] using
      transportedLastCauchyBoundaryIntegrand_analyticOnNhd_smallCylinder
        (m := m) (f := f) (z := z) (r := ρ / 2) (ρ := ρ) hboundary hρpos
  have hBoundaryCircleIntegrable :
      ∀ p ∈ Metric.closedBall (e z) (ρ / 8),
        CircleIntegrable (fun ζ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ)) (e z).2 (ρ / 2) := by
    simpa [e, g] using
      transportedBoundaryIntegrand_circleIntegrable_closedBall
        (m := m) (D := D) (f := f) hsep (z := z) (ρ := ρ) hρpos hcyl
  have hGAt :
      AnalyticAt ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ)))
        (e z) := by
    let r0 : ℝ := ρ / 8
    have hBoundaryCommonBall :
        ∀ ζ ∈ Metric.sphere (e z).2 (ρ / 2),
          AnalyticOnNhd ℂ
            (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
            (Metric.ball (e z) r0) := by
      simpa [U, e, g, r0] using
        transportedBoundaryIntegrand_analyticOnNhd_commonBall
          (m := m) (f := f) (z := z) (ρ := ρ) hρpos hBoundaryIntegrand
    have hCircleIntegrable :
        ∀ p ∈ Metric.closedBall (e z) r0,
          CircleIntegrable (fun ζ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ)) (e z).2 (ρ / 2) := by
      simpa [r0] using hBoundaryCircleIntegrable
    have hSeriesEq :
        ∀ p ∈ Metric.ball (e z) r0,
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ)) =
          (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum (p.2 - (e z).2) := by
      simpa [e, g, r0] using
        transportedLastCauchySeries_eq_on_smallBall
          (m := m) (D := D) (f := f) hsep (z := z) (ρ := ρ) hρpos hcyl
    have hNormalizedEq :
        ∀ p ∈ Metric.ball (e z) r0,
          (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum (p.2 - (e z).2) =
            g p := by
      intro p hp
      have hpdist : dist p (e z) < r0 := by
        simpa [Metric.mem_ball] using hp
      have hprod : max (dist p.1 (e z).1) (dist p.2 (e z).2) < r0 := by
        simpa [Prod.dist_eq] using hpdist
      have hpBlock_r0 : dist p.1 (e z).1 < r0 := (max_lt_iff.mp hprod).1
      have hpLast_r0 : dist p.2 (e z).2 < r0 := (max_lt_iff.mp hprod).2
      have hr0_lt_half : r0 < ρ / 2 := by
        dsimp [r0]
        linarith
      have hpBlock : p.1 ∈ U := by
        simpa [U, Metric.mem_ball] using lt_trans hpBlock_r0 hr0_lt_half
      have hpLast : p.2 ∈ Metric.ball (e z).2 (ρ / 2) := by
        simpa [Metric.mem_ball] using lt_trans hpLast_r0 hr0_lt_half
      calc
        (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum (p.2 - (e z).2)
            = ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
                ∮ ζ in C((e z).2, ρ / 2), (ζ - p.2)⁻¹ • g (p.1, ζ)) := by
                  symm
                  exact hSeriesEq p hp
        _ = g p := by
              simpa using (hEq p.1 hpBlock hpLast).symm
    have hSeriesAt :
        AnalyticAt ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
            (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) (e z).2 (ρ / 2)).sum
              (p.2 - (e z).2))
          (e z) := by
      let w0 : ℂ := (e z).2
      let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
        (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) w0 (ρ / 2)).coeff n
      have hr0pos : 0 < r0 := by
        dsimp [r0]
        positivity
      have hzBlock : (e z).1 ∈ Metric.ball (e z).1 r0 := by
        simpa [Metric.mem_ball] using hr0pos
      have hw0Ball : (e z).2 ∈ Metric.ball (e z).2 r0 := by
        simpa [Metric.mem_ball] using hr0pos
      have hpair_mem_commonBall :
          ∀ {x : Fin (m + 1) → ℂ},
            x ∈ Metric.ball (e z).1 r0 → (x, w0) ∈ Metric.ball (e z) r0 := by
        intro x hx
        have hdist : dist (x, w0) (e z) < r0 := by
          rw [Prod.dist_eq]
          exact max_lt_iff.mpr ⟨hx, by simpa [w0, Metric.mem_ball] using hr0pos⟩
        simpa [Metric.mem_ball] using hdist
      have boundaryCommonBallBlockInsert_analyticAt :
          ∀ (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2))
            (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0) (i : Fin (m + 1)),
            AnalyticAt ℂ (fun u ↦ (ζ - w0)⁻¹ * g (Function.update x i u, ζ)) (x i) := by
        intro ζ hζ x hx i
        have hBoundaryAt :
            AnalyticAt ℂ
              (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
              (x, w0) := by
          exact hBoundaryCommonBall ζ hζ (x, w0) (hpair_mem_commonBall hx)
        have hInsertAnalytic :
            AnalyticAt ℂ (fun u : ℂ ↦ (Function.update x i u, w0)) (x i) := by
          simpa [w0] using analyticAt_update_coordinate_prod_const x i w0
        have hInsertCenter : (fun u : ℂ ↦ (Function.update x i u, w0)) (x i) = (x, w0) := by
          simp [w0]
        simpa [w0] using hBoundaryAt.comp_of_eq
          (f := fun u : ℂ ↦ (Function.update x i u, w0))
          (x := x i) hInsertAnalytic hInsertCenter
      have weightedBoundaryCommonBallBlockInsert_analyticAt :
          ∀ (n : ℕ) (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2))
            (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0) (i : Fin (m + 1)),
            AnalyticAt ℂ
              (fun u ↦
                ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
              (x i) := by
        intro n ζ hζ x hx i
        simpa [mul_assoc] using
          (analyticAt_const.mul (boundaryCommonBallBlockInsert_analyticAt ζ hζ x hx i))
      have updateCoordinate_prod_const_mapsTo_commonBall_nhd :
          ∀ {x : Fin (m + 1) → ℂ},
            x ∈ Metric.ball (e z).1 r0 → ∀ i : Fin (m + 1),
              ∃ s > 0,
                Set.MapsTo (fun u : ℂ ↦ (Function.update x i u, w0))
                  (Metric.ball (x i) s) (Metric.ball (e z) r0) := by
        intro x hx i
        let ins : ℂ → (Fin (m + 1) → ℂ) × ℂ := fun u ↦ (Function.update x i u, w0)
        have hinsCont : ContinuousAt ins (x i) := by
          simpa [ins, w0] using (analyticAt_update_coordinate_prod_const x i w0).continuousAt
        have hins_mem : ins (x i) ∈ Metric.ball (e z) r0 := by
          simpa [ins, w0] using hpair_mem_commonBall hx
        have hpre :
            ins ⁻¹' Metric.ball (e z) r0 ∈ nhds (x i) := by
          exact hinsCont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hins_mem)
        rcases Metric.mem_nhds_iff.mp hpre with ⟨s, hspos, hsMaps⟩
        refine ⟨s, hspos, ?_⟩
        intro u hu
        exact hsMaps hu
      have weightedBoundaryBlockInsert_analyticOnNhd_local :
          ∀ (n : ℕ) (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2))
            (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0) (i : Fin (m + 1)),
            ∃ s > 0,
              AnalyticOnNhd ℂ
                (fun u ↦ ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                (Metric.ball (x i) s) := by
        intro n ζ hζ x hx i
        rcases updateCoordinate_prod_const_mapsTo_commonBall_nhd hx i with ⟨s, hspos, hsMaps⟩
        refine ⟨s, hspos, ?_⟩
        intro u hu
        have hBoundaryAt :
            AnalyticAt ℂ
              (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - p.2)⁻¹ * g (p.1, ζ))
              (Function.update x i u, w0) := by
          exact hBoundaryCommonBall ζ hζ _ (hsMaps hu)
        have hInsertAnalytic :
            AnalyticAt ℂ (fun v : ℂ ↦ (Function.update x i v, w0)) u := by
          simpa [w0, Function.update] using
            (analyticAt_update_coordinate_prod_const (Function.update x i u) i w0)
        have hInsertCenter :
            (fun v : ℂ ↦ (Function.update x i v, w0)) u = (Function.update x i u, w0) := by
          simp [w0]
        have hSliceAt :
            AnalyticAt ℂ (fun v ↦ (ζ - w0)⁻¹ * g (Function.update x i v, ζ)) u := by
          simpa [w0] using hBoundaryAt.comp_of_eq
            (f := fun v : ℂ ↦ (Function.update x i v, w0))
            (x := u) hInsertAnalytic hInsertCenter
        simpa [mul_assoc] using (analyticAt_const.mul hSliceAt)
      have weightedBoundaryBlockInsert_differentiableOn_local :
          ∀ (n : ℕ) (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2))
            (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0) (i : Fin (m + 1)),
            ∃ s > 0,
              DifferentiableOn ℂ
                (fun u ↦ ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                (Metric.ball (x i) s) := by
        intro n ζ hζ x hx i
        rcases weightedBoundaryBlockInsert_analyticOnNhd_local n ζ hζ x hx i with
          ⟨s, hspos, hsAnalytic⟩
        refine ⟨s, hspos, ?_⟩
        exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mp hsAnalytic
      have updateCoordinate_prod_const_mapsTo_commonBall_closedBall :
          ∀ {x : Fin (m + 1) → ℂ},
            x ∈ Metric.ball (e z).1 r0 → ∀ i : Fin (m + 1),
              ∃ s > 0,
                Set.MapsTo (fun u : ℂ ↦ (Function.update x i u, w0))
                  (Metric.closedBall (x i) (s / 2)) (Metric.ball (e z) r0) := by
        intro x hx i
        rcases updateCoordinate_prod_const_mapsTo_commonBall_nhd hx i with ⟨s, hspos, hsMaps⟩
        refine ⟨s, hspos, ?_⟩
        exact updateCoordinateProdConst_mapsTo_ball_closedBall_half hspos hsMaps
      have weightedBoundaryBlockInsert_continuousOn_closedBall_local :
          ∀ (n : ℕ) (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2))
            (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0) (i : Fin (m + 1)),
            ∃ s > 0,
              ContinuousOn
                (fun u ↦ ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                (Metric.closedBall (x i) (s / 2)) := by
        intro n ζ hζ x hx i
        rcases weightedBoundaryBlockInsert_analyticOnNhd_local n ζ hζ x hx i with
          ⟨s, hspos, hsAnalytic⟩
        refine ⟨s, hspos, ?_⟩
        intro u hu
        have hu_ball : u ∈ Metric.ball (x i) s := by
          exact Metric.closedBall_subset_ball (by linarith) hu
        exact (hsAnalytic u hu_ball).continuousAt.continuousWithinAt
      have weightedBoundaryBlockInsert_hasFPowerSeriesAt_local :
          ∀ (n : ℕ) (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2))
            (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0) (i : Fin (m + 1)),
            HasFPowerSeriesAt
              (fun u ↦
                ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
              (FormalMultilinearSeries.ofScalars ℂ
                (fun q ↦
                  iteratedDeriv q
                    (fun u ↦
                      ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                    (x i) / q.factorial))
              (x i) := by
        intro n ζ hζ x hx i
        exact (weightedBoundaryCommonBallBlockInsert_analyticAt n ζ hζ x hx i).hasFPowerSeriesAt
      have transportedLastCauchyCoeffSlice_eq_centeredIntegral_local :
          ∀ (n : ℕ) (x : Fin (m + 1) → ℂ) (i : Fin (m + 1)) (u : ℂ),
            A n (Function.update x i u) =
              ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
                ∮ ζ in C(w0, ρ / 2),
                  ((ζ - w0)⁻¹) ^ n •
                    (ζ - w0)⁻¹ • g (Function.update x i u, ζ)) := by
        intro n x i u
        simpa [A, w0, smul_eq_mul, mul_assoc] using
          transportedLastCauchyCoeff_eq_centeredIntegral
            (m := m) (f := f) (z := z) (ρ := ρ) n (Function.update x i u)
      have transportedLastCauchyCoeffSlice_eq_intervalIntegral_local :
          ∀ (n : ℕ) (x : Fin (m + 1) → ℂ) (i : Fin (m + 1)) (u : ℂ),
            A n (Function.update x i u) =
              ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
                ∫ θ in Set.Icc 0 (2 * Real.pi),
                  deriv (circleMap w0 (ρ / 2)) θ *
                    (((circleMap w0 (ρ / 2) θ - w0)⁻¹) ^ n *
                      ((circleMap w0 (ρ / 2) θ - w0)⁻¹ *
                        g (Function.update x i u, circleMap w0 (ρ / 2) θ)))) := by
        intro n x i u
        simpa [A] using
          cauchyPowerSeries_coeff_eq_intervalIntegral
            (φ := fun ζ ↦ g (Function.update x i u, ζ)) (w0 := w0) (R := ρ / 2) n
      have weightedBoundarySlice_hasFPowerSeriesOnBall_common_local :
          ∀ (n : ℕ) (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0)
            (i : Fin (m + 1)),
            ∃ R : NNReal, 0 < R ∧
              Set.MapsTo (fun u : ℂ ↦ (Function.update x i u, w0))
                (Metric.closedBall (x i) (R : ℝ)) (Metric.ball (e z) r0) ∧
              ∀ (ζ : ℂ) (_hζ : ζ ∈ Metric.sphere w0 (ρ / 2)),
                HasFPowerSeriesOnBall
                  (fun u ↦
                    ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                  (cauchyPowerSeries
                    (fun u ↦
                      ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                    (x i) R)
                  (x i) R ∧
                ContinuousOn
                  (fun u ↦
                    ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                  (Metric.closedBall (x i) (R : ℝ)) := by
        intro n x hx i
        -- Reuse the support-level common-ball slice package instead of reproving the same
        -- one-variable Cauchy preparation inline.
        simpa [w0] using
          weightedBoundarySlice_hasFPowerSeriesOnBall_of_commonBall
            (g := g) (center := e z) (r0 := r0) (outerR := ρ / 2)
            hBoundaryCommonBall n x hx i
      have transportedLastCauchyCoeffSlice_analyticAt_local :
          ∀ (n : ℕ) (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball (e z).1 r0)
            (i : Fin (m + 1)),
            AnalyticAt ℂ (fun u ↦ A n (Function.update x i u)) (x i) := by
        intro n x hx i
        rcases weightedBoundarySlice_hasFPowerSeriesOnBall_common_local n x hx i with
          ⟨R, hRpos, hInsertMaps, hBoundarySlicePackage⟩
        have hRrealPos : 0 < (R : ℝ) := by
          exact_mod_cast hRpos
        have hHalfRPos : 0 < (R : ℝ) / 2 := by
          positivity
        let b : ℕ → ℂ → ℂ := fun q ζ ↦
          (cauchyPowerSeries
            (fun u ↦
              ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
            (x i) R).coeff q
        have hBoundarySeriesOnBall :
            ∀ ζ ∈ Metric.sphere w0 (ρ / 2),
              HasFPowerSeriesOnBall
                (fun u ↦
                  ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                (cauchyPowerSeries
                  (fun u ↦
                    ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                  (x i) R)
                (x i) R := by
          intro ζ hζ
          exact (hBoundarySlicePackage ζ hζ).1
        have hBoundaryContClosedBall :
            ∀ ζ ∈ Metric.sphere w0 (ρ / 2),
              ContinuousOn
                (fun u ↦
                  ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                (Metric.closedBall (x i) (R : ℝ)) := by
          intro ζ hζ
          exact (hBoundarySlicePackage ζ hζ).2
        have weightedBoundaryPoint_continuousOn_outerSphere :
            ∀ u ∈ Metric.closedBall (x i) (R : ℝ),
              ContinuousOn
                (fun ζ ↦
                  ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                (Metric.sphere w0 (ρ / 2)) := by
          intro u hu
          have hpBall : (Function.update x i u, w0) ∈ Metric.ball (e z) r0 := hInsertMaps hu
          have hpClosedBall : (Function.update x i u, w0) ∈ Metric.closedBall (e z) r0 :=
            Metric.ball_subset_closedBall hpBall
          have hbase :
              ContinuousOn
                (fun ζ ↦ (ζ - w0)⁻¹ * g (Function.update x i u, ζ))
                (Metric.sphere w0 (ρ / 2)) := by
            simpa [w0] using
              transportedBoundaryIntegrand_continuousOn_sphere_closedBall
                (m := m) (D := D) (f := f) hsep (z := z) (ρ := ρ) hρpos hcyl
                (Function.update x i u, w0) hpClosedBall
          have hkernel_ne :
              ∀ ζ ∈ Metric.sphere w0 (ρ / 2), ζ - w0 ≠ 0 := by
            intro ζ hζ
            intro hzero
            have hdist : dist ζ w0 = ρ / 2 := by
              simpa [Metric.mem_sphere, dist_eq_norm] using hζ
            have hzero' : dist ζ w0 = 0 := by
              simp [dist_eq_norm, hzero]
            linarith
          have hkernelCont :
              ContinuousOn (fun ζ : ℂ ↦ (ζ - w0)⁻¹) (Metric.sphere w0 (ρ / 2)) :=
            (continuousOn_id.sub continuousOn_const).inv₀ hkernel_ne
          exact (hkernelCont.pow n).mul hbase
        have hPointwiseCoeffBound :
            ∀ ζ ∈ Metric.sphere w0 (ρ / 2),
              ∃ Mζ : ℝ, 0 ≤ Mζ ∧
                ∀ q : ℕ, ‖b q ζ‖ ≤ Mζ / (R : ℝ) ^ q := by
          intro ζ hζ
          let Fζ : ℂ → ℂ := fun u ↦
            ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ))
          have hFζcont : ContinuousOn Fζ (Metric.closedBall (x i) (R : ℝ)) := by
            simpa [Fζ] using hBoundaryContClosedBall ζ hζ
          obtain ⟨Mζ, hMζbound⟩ :=
            (isCompact_sphere (x i) (R : ℝ)).exists_bound_of_continuousOn
              (f := Fζ) (hFζcont.mono Metric.sphere_subset_closedBall)
          have hMζnonneg : 0 ≤ Mζ := by
            have hpoint : x i + (R : ℂ) ∈ Metric.sphere (x i) (R : ℝ) := by
              simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRrealPos]
            exact le_trans (norm_nonneg _) (hMζbound _ hpoint)
          refine ⟨Mζ, hMζnonneg, ?_⟩
          intro q
          simpa [b, Fζ] using
            cauchyPowerSeries_coeff_norm_le_div_pow_of_bound_on_circle
              (u0 := x i) (R := (R : ℝ)) (M := Mζ) (F := Fζ) hRrealPos
              (fun u hu ↦ hMζbound u hu) q
        have hCoeffPackage :
            ∃ M : ℝ, 0 ≤ M ∧
              ∀ q : ℕ,
                ContinuousOn (b q) (Metric.sphere w0 (ρ / 2)) ∧
                  ∀ ζ ∈ Metric.sphere w0 (ρ / 2), ‖b q ζ‖ ≤ M / (R : ℝ) ^ q := by
          let outerR : NNReal := ⟨ρ / 2, by positivity⟩
          have hJointTorus :
              ContinuousOn
                (Function.uncurry fun ζ u ↦
                  ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
                (Metric.sphere w0 (outerR : ℝ) ×ˢ Metric.closedBall (x i) (R : ℝ)) := by
            refine continuousOn_of_forall_analyticAt ?_
            intro p hp
            rcases hp with ⟨hpSphere, hpClosed⟩
            have hpInsert : (Function.update x i p.2, w0) ∈ Metric.ball (e z) r0 :=
              hInsertMaps hpClosed
            have hpBlock : Function.update x i p.2 ∈ Metric.ball (e z).1 r0 := by
              rw [Metric.mem_ball, Prod.dist_eq] at hpInsert
              exact (max_lt_iff.mp hpInsert).1
            have hpBlockU : Function.update x i p.2 ∈ U := by
              have hr0_le : r0 ≤ ρ / 2 := by
                dsimp [r0]
                linarith
              exact Metric.ball_subset_ball hr0_le hpBlock
            have hpD : e.symm (Function.update x i p.2, p.1) ∈ D := by
              exact hcyl ⟨hpBlockU, Metric.sphere_subset_closedBall hpSphere⟩
            have hpNe : p.1 ≠ w0 := by
              intro hpEq
              have hpDist : dist p.1 w0 = ρ / 2 := by
                simpa [Metric.mem_sphere, dist_eq_norm] using hpSphere
              have : dist p.1 w0 = 0 := by
                simp [hpEq]
              linarith
            by_cases hm : m = 0
            · subst hm
              fin_cases i
              let Daux : Set (Fin 2 → ℂ) :=
                {y | e.symm ((fun _ : Fin 1 => y 0), y 1) ∈ D ∧ y 1 ≠ w0}
              let Haux : (Fin 2 → ℂ) → ℂ := fun y ↦
                ((y 1 - w0)⁻¹) ^ n * ((y 1 - w0)⁻¹ * g ((fun _ : Fin 1 => y 0), y 1))
              have hDauxOpen : IsOpen Daux := by
                have hpackCont :
                    Continuous (fun y : Fin 2 → ℂ ↦ ((fun _ : Fin 1 => y 0), y 1)) := by
                  refine (continuous_pi fun _ ↦ continuous_apply 0).prodMk (continuous_apply 1)
                have hmemOpen :
                    IsOpen {y : Fin 2 → ℂ | e.symm ((fun _ : Fin 1 => y 0), y 1) ∈ D} :=
                  hD.preimage (hsymmCont.comp hpackCont)
                have hneOpen : IsOpen {y : Fin 2 → ℂ | y 1 ≠ w0} := by
                  change IsOpen ((fun y : Fin 2 → ℂ ↦ y 1) ⁻¹' ({w0}ᶜ))
                  exact (isClosed_singleton.preimage (continuous_apply 1)).isOpen_compl
                simpa [Daux, Set.setOf_and] using hmemOpen.inter hneOpen
              have hHauxSep :
                  ∀ y ∈ Daux, ∀ k : Fin 2,
                    AnalyticAt ℂ (fun w ↦ Haux (Function.update y k w)) (y k) := by
                intro y hy k
                rcases hy with ⟨hyD, hyNe⟩
                fin_cases k
                · change
                    AnalyticAt ℂ
                      (fun w ↦
                        ((y 1 - w0)⁻¹) ^ n *
                          ((y 1 - w0)⁻¹ * f (e.symm ((fun _ : Fin 1 => w), y 1))))
                      (y 0)
                  have hArgEq :
                      ∀ w : ℂ,
                        e.symm (Function.update (fun _ : Fin 1 => y 0) 0 w, y 1) =
                          e.symm ((fun _ : Fin 1 => w), y 1) := by
                    intro w
                    apply congrArg e.symm
                    apply Prod.ext
                    · funext j
                      fin_cases j
                      simp [Function.update]
                    · rfl
                  have hEventually :
                      (fun w ↦
                        ((y 1 - w0)⁻¹) ^ n *
                          ((y 1 - w0)⁻¹ *
                            f (e.symm (Function.update (fun _ : Fin 1 => y 0) 0 w, y 1)))) =ᶠ[nhds (y 0)]
                      (fun w ↦
                        ((y 1 - w0)⁻¹) ^ n *
                          ((y 1 - w0)⁻¹ * f (e.symm ((fun _ : Fin 1 => w), y 1)))) := by
                    filter_upwards with w
                    rw [hArgEq w]
                  exact
                    (analyticAt_weightedTransportedBlockSlice
                      (m := 0) (D := D) (f := f) hsep
                      (x := fun _ : Fin 1 => y 0) (ζ := y 1) (w0 := w0) (i := 0) hyD n).congr
                      hEventually
                · -- Freeze the unique block coordinate and vary the last coordinate away from the pole.
                  simpa [g, Haux, Function.update] using
                    (analyticAt_weightedTransportedLastSlice
                      (m := 0) (D := D) (f := f) hsep
                      (x := fun _ : Fin 1 => y 0) (ζ := y 1) (w0 := w0) hyD hyNe n)
              let φ : ℂ × ℂ → Fin 2 → ℂ := fun q ↦ ![q.2, q.1]
              have hφAt : AnalyticAt ℂ φ p := by
                exact (analyticOnNhd_fin2Swap (s := Set.univ)) p (by simp)
              have hUpdateConst' (u : ℂ) :
                  Function.update x 0 u = (fun _ : Fin 1 => u) := by
                funext j
                fin_cases j
                simp [Function.update]
              have hφp : φ p ∈ Daux := by
                refine ⟨?_, ?_⟩
                · -- Packing the torus point in `Fin 2` order recovers the same domain condition
                  change e.symm ((fun _ : Fin 1 => p.2), p.1) ∈ D
                  rw [← hUpdateConst' p.2]
                  exact hpD
                · -- The packed last coordinate is exactly the boundary parameter `p.1`, so the
                  simpa [φ] using hpNe
              have hKernel :
                  (fun q : ℂ × ℂ ↦ Haux (φ q)) =
                    Function.uncurry
                      (fun ζ u ↦
                        ((ζ - w0)⁻¹) ^ n *
                          ((ζ - w0)⁻¹ * g (Function.update x 0 u, ζ))) := by
                funext q
                rw [Function.uncurry, hUpdateConst' q.2]
                rfl
              have hHauxOn : AnalyticOnNhd ℂ Haux Daux := by
                exact fin2Hartogs hDauxOpen hHauxSep
              have hHauxAt : AnalyticAt ℂ Haux (φ p) := hHauxOn (φ p) hφp
              exact hKernel.symm ▸ (hHauxAt.comp hφAt)
            · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
              let i0 : Fin (m' + 2) := i
              let j : Fin (m' + 2) := Fin.succAbove i0 (Fin.last m')
              let Daux : Set (Fin (m' + 2) → ℂ) :=
                {y | e.symm (Function.update x i0 (y i0), y j) ∈ D ∧ y j ≠ w0}
              let Haux : (Fin (m' + 2) → ℂ) → ℂ := fun y ↦
                ((y j - w0)⁻¹) ^ n * ((y j - w0)⁻¹ * g (Function.update x i0 (y i0), y j))
              let pack : ℂ × ℂ → Fin (m' + 2) → ℂ := fun q ↦
                Function.update (Function.update x j q.1) i0 q.2
              have hij : i0 ≠ j := Fin.ne_succAbove i0 (Fin.last m')
              have hDauxOpen : IsOpen Daux := by
                have hblockCont :
                    Continuous (fun y : Fin (m' + 2) → ℂ ↦ Function.update x i0 (y i0)) := by
                  refine continuous_pi fun k ↦ ?_
                  by_cases hk : k = i0
                  · simpa [Function.update, hk] using
                      (continuous_apply i0 : Continuous fun y : Fin (m' + 2) → ℂ ↦ y i0)
                  · simpa [Function.update, hk] using
                      (continuous_const : Continuous fun _ : Fin (m' + 2) → ℂ ↦ x k)
                have hpairCont :
                    Continuous (fun y : Fin (m' + 2) → ℂ ↦
                      (Function.update x i0 (y i0), y j)) := by
                  exact hblockCont.prodMk (continuous_apply j)
                have hmemOpen :
                    IsOpen {y : Fin (m' + 2) → ℂ | e.symm (Function.update x i0 (y i0), y j) ∈ D} :=
                  hD.preimage (hsymmCont.comp hpairCont)
                have hneOpen : IsOpen {y : Fin (m' + 2) → ℂ | y j ≠ w0} := by
                  change IsOpen ((fun y : Fin (m' + 2) → ℂ ↦ y j) ⁻¹' ({w0}ᶜ))
                  exact (isClosed_singleton.preimage (continuous_apply j)).isOpen_compl
                simpa [Daux, Set.setOf_and] using hmemOpen.inter hneOpen
              have hHauxOn : AnalyticOnNhd ℂ Haux Daux := by
                refine ih hDauxOpen ?_
                intro y hy k
                rcases hy with ⟨hyD, hyNe⟩
                by_cases hk_i : k = i0
                · subst hk_i
                  have hji : j ≠ i0 := hij.symm
                  have hSliceEq :
                      (fun w : ℂ ↦ Haux (Function.update y i0 w)) =
                        (fun w ↦
                          ((y j - w0)⁻¹) ^ n *
                            ((y j - w0)⁻¹ * g (Function.update x i0 w, y j))) := by
                    funext w
                    simp [Haux, Function.update, hij, hji]
                  rw [hSliceEq]
                  simpa [Function.update] using
                    (analyticAt_weightedTransportedBlockSlice
                      (m := m' + 1) (D := D) (f := f) hsep
                      (x := Function.update x i0 (y i0)) (ζ := y j) (w0 := w0) (i := i0) hyD n)
                by_cases hk_j : k = j
                · subst hk_j
                  have hji : j ≠ i0 := hij.symm
                  have hSliceEq :
                      (fun w : ℂ ↦ Haux (Function.update y j w)) =
                        (fun w ↦
                          ((w - w0)⁻¹) ^ n *
                            ((w - w0)⁻¹ * g (Function.update x i0 (y i0), w))) := by
                    funext w
                    simp [Haux, Function.update, hij, hji]
                  rw [hSliceEq]
                  simpa [Function.update, hij] using
                    (analyticAt_weightedTransportedLastSlice
                      (m := m' + 1) (D := D) (f := f) hsep
                      (x := Function.update x i0 (y i0)) (ζ := y j) (w0 := w0) hyD hyNe n)
                · -- All remaining coordinates are dummy parameters of `Haux`, so the slice is
                  have hik : i0 ≠ k := by
                    intro h
                    exact hk_i h.symm
                  have hjk : j ≠ k := by
                    intro h
                    exact hk_j h.symm
                  have hSliceEq :
                      (fun w : ℂ ↦ Haux (Function.update y k w)) =
                        (fun _ : ℂ ↦
                          ((y j - w0)⁻¹) ^ n *
                            ((y j - w0)⁻¹ * g (Function.update x i0 (y i0), y j))) := by
                    funext w
                    simp [Haux, Function.update, hk_i, hk_j, hik, hjk]
                  rw [hSliceEq]
                  exact analyticAt_const
              have hpPack : pack p ∈ Daux := by
                have hji : j ≠ i0 := hij.symm
                have hpack_i : pack p i0 = p.2 := by
                  simp [pack, Function.update, hij, hji]
                have hpack_j : pack p j = p.1 := by
                  simp [pack, Function.update, hij, hji]
                refine ⟨?_, ?_⟩
                · -- Evaluating the packed point recovers the original transported parameter point.
                  rw [hpack_i, hpack_j]
                  simpa [i0] using hpD
                · -- The packed last coordinate is the boundary parameter `p.1`, so the pole is
                  rw [hpack_j]
                  exact hpNe
              have hPackAnalytic : AnalyticAt ℂ pack p :=
                analyticAt_update_twoCoordinates hij p
              have hHauxAt : AnalyticAt ℂ Haux (pack p) := hHauxOn (pack p) hpPack
              have hji : j ≠ i0 := hij.symm
              have hPackKernel :
                  (fun q : ℂ × ℂ ↦ Haux (pack q)) =
                    Function.uncurry
                      (fun ζ u ↦
                        ((ζ - w0)⁻¹) ^ n *
                          ((ζ - w0)⁻¹ * g (Function.update x i u, ζ))) := by
                funext q
                simp [Function.uncurry, Haux, pack, Function.update, hij, hji, i0]
              rw [← hPackKernel]
              exact hHauxAt.comp hPackAnalytic
          simpa [b, outerR] using
            weightedBoundarySliceCoeffRow_package_of_jointTorusContinuous_local
              (u0 := x i) (c := w0) (innerR := R) (outerR := outerR) (n := n)
              (g := fun u ζ ↦ g (Function.update x i u, ζ)) hRpos hJointTorus
        rcases hCoeffPackage with ⟨M, hMnonneg, hrowB⟩
        have hcontB (q : ℕ) : ContinuousOn (b q) (Metric.sphere w0 (ρ / 2)) := (hrowB q).1
        have hboundB (q : ℕ) (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2)) :
            ‖b q ζ‖ ≤ M / (R : ℝ) ^ q := (hrowB q).2 ζ hζ
        have hIntegralAt :
            AnalyticAt ℂ
              (fun u ↦
                ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
                  ∮ ζ in C(w0, ρ / 2),
                    ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ))))
              (x i) := by
          exact
            analyticAt_centeredCircleIntegral_of_hasFPowerSeriesOnBall_coeffRow_local
              (u0 := x i) (c := w0) (outerR := ρ / 2) (innerR := R) (M := M)
              (by positivity) hRrealPos hMnonneg
              (F := fun ζ u ↦
                ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))
              (hseries := hBoundarySeriesOnBall) hcontB hboundB
        have hEqSlice :
            (fun u ↦ A n (Function.update x i u)) =
              (fun u ↦
                ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
                  ∮ ζ in C(w0, ρ / 2),
                    ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * g (Function.update x i u, ζ)))) := by
          funext u
          exact transportedLastCauchyCoeffSlice_eq_centeredIntegral_local n x i u
        simpa [hEqSlice] using hIntegralAt
      have hCoeffOn :
          ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball (e z).1 r0) := by
        intro n
        refine ih Metric.isOpen_ball ?_
        intro x hx i
        exact transportedLastCauchyCoeffSlice_analyticAt_local n x hx i
      have hCoeffJoint :
          ∀ n : ℕ, AnalyticAt ℂ (A n) (e z).1 := by
        intro n
        exact hCoeffOn n (e z).1 hzBlock
      have hCoeffSeries :
          ∀ n : ℕ,
            ∃ Pn : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ,
              HasFPowerSeriesAt (A n) Pn (e z).1 := by
        intro n
        exact hCoeffJoint n
      choose Pn hPn using hCoeffSeries
      have hTermSeries :
          ∀ n : ℕ,
            ∃ Qn : FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ,
              HasFPowerSeriesAt
                (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ A n p.1 * (p.2 - w0) ^ n)
                Qn (e z) := by
        intro n
        have hpow :
            HasFPowerSeriesAt
              (fun w : ℂ ↦ (w - w0) ^ n)
              (FormalMultilinearSeries.ofScalars ℂ
                (fun q ↦ iteratedDeriv q (fun w : ℂ ↦ (w - w0) ^ n) w0 / q.factorial))
              w0 := by
          exact (((analyticAt_id.sub analyticAt_const).pow n)).hasFPowerSeriesAt
        exact ⟨_, by simpa [w0] using hasFPowerSeriesAt_mul_comp_fst_snd (hPn n) hpow⟩
      have hTermOn :
          ∀ n : ℕ,
            AnalyticOnNhd ℂ
              (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ A n p.1 * (p.2 - w0) ^ n)
              (Metric.ball (e z).1 r0 ×ˢ Metric.ball w0 (ρ / 4)) := by
        intro n
        have hBlockOn :
            AnalyticOnNhd ℂ (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ A n p.1)
              (Metric.ball (e z).1 r0 ×ˢ Metric.ball w0 (ρ / 4)) := by
          refine (hCoeffOn n).comp (analyticOnNhd_fst (𝕜 := ℂ)
            (t := Metric.ball (e z).1 r0 ×ˢ Metric.ball w0 (ρ / 4))) ?_
          intro p hp
          exact hp.1
        have hPowOn :
            AnalyticOnNhd ℂ
              (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (p.2 - w0) ^ n)
              (Metric.ball (e z).1 r0 ×ˢ Metric.ball w0 (ρ / 4)) := by
          exact
            (((analyticOnNhd_snd (𝕜 := ℂ)
              (t := Metric.ball (e z).1 r0 ×ˢ Metric.ball w0 (ρ / 4))).sub
                analyticOnNhd_const).pow n)
        exact hBlockOn.mul hPowOn
      have transportedLastCauchyCoeff_pointwiseBound_local :
          ∀ x ∈ Metric.ball (e z).1 r0,
            ∃ Cx : ℝ, 0 ≤ Cx ∧
              ∀ n : ℕ, ‖A n x‖ ≤ Cx / (ρ / 2 : ℝ) ^ n := by
        intro x hx
        have hr0_lt_half : r0 < ρ / 2 := by
          dsimp [r0]
          linarith
        have hcylSmall :
            Metric.ball (e z).1 r0 ×ˢ Metric.closedBall w0 (ρ / 2) ⊆ {p | e.symm p ∈ D} := by
          intro p hp
          exact hcyl ⟨Metric.ball_subset_ball (le_of_lt hr0_lt_half) hp.1, hp.2⟩
        have hSliceOn :
            AnalyticOnNhd ℂ (fun w ↦ g (x, w)) (Metric.closedBall w0 (ρ / 2)) := by
          simpa [e, g, w0] using
            transportedLastSlices_analyticOnNhd_closedBall
              (m := m) (D := D) (f := f) hsep (z := z)
              (r := r0) (R := ρ / 2) hcylSmall x hx
        let Rlast : NNReal := ⟨ρ / 2, by linarith [hρpos]⟩
        have hRlastPos : 0 < Rlast := by
          exact_mod_cast hρhalf_pos
        obtain ⟨Cx, hCxnonneg, hCx⟩ :=
          cauchyPowerSeries_coeff_norm_le_div_pow_of_continuousOn_closedBall
            (u0 := w0) (R := Rlast)
            (F := fun w ↦ g (x, w)) hRlastPos hSliceOn.continuousOn
        refine ⟨Cx, hCxnonneg, ?_⟩
        intro n
        simpa [A, w0, Rlast] using hCx n
      let r1 : ℝ := r0 / 2
      have hr1pos : 0 < r1 := by
        dsimp [r1]
        positivity
      have hr1lt : r1 < r0 := by
        dsimp [r1]
        linarith
      have hCoeffClosedSmallPackage :
          (∀ n : ℕ, ContinuousOn (A n) (Metric.closedBall (e z).1 r1)) ∧
            ∀ x ∈ Metric.closedBall (e z).1 r1,
              ∃ Cx : ℝ, 0 ≤ Cx ∧
                ∀ n : ℕ, ‖A n x‖ ≤ Cx / (ρ / 2 : ℝ) ^ n := by
        have hpackage :=
          transportedCoeff_packageOnClosedSmallBall_local
            (x0 := (e z).1) (r0 := r0) (R := ρ / 2) hr0pos hCoeffOn
            transportedLastCauchyCoeff_pointwiseBound_local
        simpa [r1] using hpackage
      have hCoeffContClosedSmall :
          ∀ n : ℕ, ContinuousOn (A n) (Metric.closedBall (e z).1 r1) :=
        hCoeffClosedSmallPackage.1
      have transportedLastCauchyCoeff_pointwiseBound_closedSmallBall_local :
          ∀ x ∈ Metric.closedBall (e z).1 r1,
            ∃ Cx : ℝ, 0 ≤ Cx ∧
              ∀ n : ℕ, ‖A n x‖ ≤ Cx / (ρ / 2 : ℝ) ^ n :=
        hCoeffClosedSmallPackage.2
      have normalizedTerm_geometricMajorant_of_coeffBound :
          ∀ {C : ℝ},
            0 ≤ C →
            (∀ n : ℕ, ∀ x ∈ Metric.ball (e z).1 r0,
              ‖A n x‖ ≤ C / (ρ / 2 : ℝ) ^ n) →
            ∀ n : ℕ, ∀ p ∈ Metric.ball (e z).1 r0 ×ˢ Metric.ball w0 (ρ / 4),
              ‖A n p.1 * (p.2 - w0) ^ n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
        intro C hCnonneg hCoeff n p hp
        exact
          norm_weightedCauchyTerm_le_geometric_of_coeffBound
            (A := A) (w0 := w0) (ρ := ρ) (C := C) hρpos hp.2 hCnonneg
            (fun k ↦ hCoeff k p.1 hp.1) n
      have hNormalizedSeriesEqTsum :
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
            (cauchyPowerSeries (fun ζ ↦ g (p.1, ζ)) w0 (ρ / 2)).sum (p.2 - w0)) =
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
            ∑' n : ℕ, A n p.1 * (p.2 - w0) ^ n) := by
        funext p
        simpa [A] using
          (cauchyPowerSeries_sum_eq_tsum_coeff
            (F := fun ζ ↦ g (p.1, ζ)) (w0 := w0) (δ := p.2 - w0) (R := ρ / 2))
      have transportedCauchyCoeff_uniformBoundOnClosedSmallBall_local :
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ x ∈ Metric.closedBall (e z).1 r1, ∀ n : ℕ, ‖A n x‖ ≤ C / (ρ / 2 : ℝ) ^ n := by
        have hTransportedProdSep :
            ∀ p ∈ {p : (Fin (m + 1) → ℂ) × ℂ | e.symm p ∈ D},
              AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ g (x, p.2)) p.1 ∧
                AnalyticAt ℂ (fun w : ℂ ↦ g (p.1, w)) p.2 := by
          -- Consume the standalone transported-separate-analyticity bridge instead of rebuilding
          -- the block and last slices inline.
          simpa [e, g] using transportedProductSeparate
        -- Route correction: use the noncircular product-boundary coefficient package directly on
        -- the transported cylinder instead of rebuilding joint torus continuity via the product
        -- Hartogs theorem.
        obtain ⟨C, hCnonneg, hCBound⟩ := by
          simpa [e, g, w0, r0, r1, A] using
            (boundaryCoeffUniform (z := z) (ρ := ρ) hρpos (by simpa [U] using hcyl))
        refine ⟨C, hCnonneg, ?_⟩
        intro x hx n
        simpa [A, w0, r0, r1] using hCBound x hx n
      rw [hNormalizedSeriesEqTsum]
      rcases transportedCauchyCoeff_uniformBoundOnClosedSmallBall_local with ⟨C, hCnonneg, hCBound⟩
      exact
        parametricUniform
          (A := A) (x0 := (e z).1) (u0 := w0) (r := r0) (R := ρ / 2) (C := C)
          hr0pos hρhalf_pos hCoeffOn hCBound
    simpa [e, g, r0] using
      transportedLastCauchyTransform_jointAnalyticAt_center_ofCommonBall
        (m := m) (f := f) (z := z) (ρ := ρ) hρpos hSeriesAt hSeriesEq
  have hgAt : AnalyticAt ℂ g (e z) := by
    simpa [U] using
      transportedLastCauchyTransform_eqAt_center
        (m := m) (f := f) (z := z) (ρ := ρ) hρpos hEq hGAt
  have heBlock :
      AnalyticAt ℂ (fun x : Fin (m + 2) → ℂ ↦ fun i : Fin (m + 1) ↦ x (Fin.castAdd 1 i)) z := by
    exact AnalyticAt.pi fun i ↦ by
      simpa using (ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 2) ↦ ℂ) (Fin.castAdd 1 i)) z)
  have heLast : AnalyticAt ℂ (fun x : Fin (m + 2) → ℂ ↦ x (Fin.last (m + 1))) z := by
    simpa using (ContinuousLinearMap.analyticAt
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 2) ↦ ℂ) (Fin.last (m + 1))) z)
  have heAnalytic : AnalyticAt ℂ e z := by
    simpa [e, Fin.succFunEquiv_apply] using heBlock.prod heLast
  have hcomp : (fun x : Fin (m + 2) → ℂ ↦ g (e x)) = f := by
    funext x
    simpa [e, g] using congrArg f (e.symm_apply_apply x)
  rw [← hcomp]
  exact hgAt.comp (f := e) (x := z) heAnalytic
