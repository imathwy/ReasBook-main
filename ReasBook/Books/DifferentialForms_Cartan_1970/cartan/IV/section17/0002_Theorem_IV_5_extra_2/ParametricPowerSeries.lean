import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».BoundaryCauchySeries

/-- Helper for Theorem IV.5-extra-2: combining a block-variable power-series witness with a
last-variable power-series witness yields the expected joint witness for their pointwise product on
the product space. -/
lemma hasFPowerSeriesAt_mul_comp_fst_snd
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → ℂ} {g : F → ℂ}
    {pf : FormalMultilinearSeries ℂ E ℂ}
    {pg : FormalMultilinearSeries ℂ F ℂ}
    {x : E} {y : F}
    (hf : HasFPowerSeriesAt f pf x)
    (hg : HasFPowerSeriesAt g pg y) :
    HasFPowerSeriesAt (fun p : E × F ↦ f p.1 * g p.2)
      (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (f x, g y)).comp
        ((pf.compContinuousLinearMap (ContinuousLinearMap.fst ℂ E F)).prod
          (pg.compContinuousLinearMap (ContinuousLinearMap.snd ℂ E F))))
      (x, y) := by
  have hfst :
      HasFPowerSeriesAt (fun p : E × F ↦ f p.1)
        (pf.compContinuousLinearMap (ContinuousLinearMap.fst ℂ E F)) (x, y) := by
    -- Pull the block-variable power series back along the analytic first projection once.
    simpa [Function.comp] using
      (hf.compContinuousLinearMap (u := ContinuousLinearMap.fst ℂ E F))
  have hsnd :
      HasFPowerSeriesAt (fun p : E × F ↦ g p.2)
        (pg.compContinuousLinearMap (ContinuousLinearMap.snd ℂ E F)) (x, y) := by
    -- Pull the last-variable power series back along the analytic second projection.
    simpa [Function.comp] using
      (hg.compContinuousLinearMap (u := ContinuousLinearMap.snd ℂ E F))
  have hpair :
      HasFPowerSeriesAt (fun p : E × F ↦ (f p.1, g p.2))
        ((pf.compContinuousLinearMap (ContinuousLinearMap.fst ℂ E F)).prod
          (pg.compContinuousLinearMap (ContinuousLinearMap.snd ℂ E F)))
        (x, y) :=
    hfst.prod hsnd
  have hmul :
      HasFPowerSeriesAt (fun q : ℂ × ℂ ↦ q.1 * q.2)
        ((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (f x, g y)) (f x, g y) := by
    -- The scalar multiplication map itself has its standard bilinear formal series at the true
    -- center `(f x, g y)`.
    simpa using (ContinuousLinearMap.mul ℂ ℂ).hasFPowerSeriesAt_bilinear (f x, g y)
  -- Compose the bilinear multiplication series with the paired block/last-variable witnesses.
  simpa [Function.comp] using
    (HasFPowerSeriesAt.comp (g := fun q : ℂ × ℂ ↦ q.1 * q.2)
      (f := fun p : E × F ↦ (f p.1, g p.2)) (x := (x, y)) hmul hpair)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: a block-variable power-series germ and
the centered scalar monomial germ together produce the expected joint power-series germ for one
parametric series term on the product space. -/
lemma parametricPowerSeriesTerm_hasFPowerSeriesAt_local
    {m : ℕ} {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {n : ℕ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hA : HasFPowerSeriesAt A P x0) :
    ∃ Q : FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ,
      HasFPowerSeriesAt
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ A p.1 * (p.2 - u0) ^ n)
        Q
        (x0, u0) := by
  have hPow :
      HasFPowerSeriesAt
        (fun u : ℂ ↦ (u - u0) ^ n)
        (FormalMultilinearSeries.ofScalars ℂ
          (fun q ↦ iteratedDeriv q (fun w : ℂ ↦ (w - u0) ^ n) u0 / q.factorial))
        u0 := by
    exact (((analyticAt_id.sub analyticAt_const).pow n)).hasFPowerSeriesAt
  exact ⟨_, by simpa using hasFPowerSeriesAt_mul_comp_fst_snd hA hPow⟩

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: one analytic coefficient germ already
gives joint analyticity of the corresponding centered parametric series term on the product
space. -/
lemma parametricPowerSeriesTerm_analyticAt_local
    {m : ℕ} {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {n : ℕ}
    (hA : AnalyticAt ℂ A x0) :
    AnalyticAt ℂ
      (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ A p.1 * (p.2 - u0) ^ n)
      (x0, u0) := by
  rcases hA with ⟨P, hP⟩
  rcases parametricPowerSeriesTerm_hasFPowerSeriesAt_local
      (m := m) (A := A) (x0 := x0) (u0 := u0) (n := n) hP with ⟨Q, hQ⟩
  exact ⟨Q, hQ⟩

/-- Helper for Theorem IV.5-extra-2: a scalar function that agrees on a disc with a convergent
scalar owner series already has the corresponding power-series expansion at the center. -/
lemma hasFPowerSeriesAtZeroOfEqTsumOnBall_local
    {g : ℂ → ℂ} {a : ℕ → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hs : Summable (fun n : ℕ ↦ ‖a n‖ * r ^ n))
    (hEq : Set.EqOn g (fun z : ℂ ↦ ∑' n : ℕ, a n * z ^ n) (Metric.ball (0 : ℂ) r)) :
    HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
  let rnn : NNReal := ⟨r, hr.le⟩
  have hradius : ENNReal.ofReal r ≤ p.radius := by
    -- Weighted norm summability on the concrete disc gives the standard lower radius bound.
    have howner : Summable (fun n : ℕ ↦ ‖p n‖ * (rnn : ℝ) ^ n) := by
      simpa [p, rnn, FormalMultilinearSeries.ofScalars_norm] using hs
    simpa [rnn, ENNReal.ofReal_eq_coe_nnreal hr.le] using
      (p.le_radius_of_summable_norm (r := rnn) howner)
  have hp_radius_pos : 0 < p.radius := by
    -- Record the owner's positive radius once before restricting back to the concrete ball.
    exact lt_of_lt_of_le (by simpa using ENNReal.ofReal_pos.mpr hr) hradius
  have hseries_full :
      HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum a) p 0 p.radius := by
    -- The canonical scalar owner realizes its own expansion on its full convergence ball.
    simpa [p] using p.hasFPowerSeriesOnBall hp_radius_pos
  have hseries_r :
      HasFPowerSeriesOnBall
        (FormalMultilinearSeries.ofScalarsSum a) p 0 (ENNReal.ofReal r) := by
    -- Restrict the full owner expansion to the concrete real disc used in the hypothesis.
    exact hseries_full.mono (by simpa using ENNReal.ofReal_pos.mpr hr) hradius
  have hEqOn :
      Set.EqOn
        (FormalMultilinearSeries.ofScalarsSum a) g
        (Metric.eball (0 : ℂ) (ENNReal.ofReal r)) := by
    intro z hz
    symm
    calc
      g z = ∑' n : ℕ, a n * z ^ n := hEq (by
        simpa [Metric.mem_ball, Metric.mem_eball, edist_dist, hr] using hz)
      _ = FormalMultilinearSeries.ofScalarsSum a z := by
        rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
        exact tsum_congr fun n ↦ by simp [smul_eq_mul]
  -- Transfer the owner expansion across the local equality on the whole disc.
  exact (hseries_r.congr hEqOn).hasFPowerSeriesAt

/-- Helper for Theorem IV.5-extra-2: a centered scalar `tsum` identity on a disc yields the
corresponding power-series expansion at the actual center. -/
lemma hasFPowerSeriesAtOfEqTsumOnBall_centered_local
    {g : ℂ → ℂ} {a : ℕ → ℂ} {u0 : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hs : Summable (fun n : ℕ ↦ ‖a n‖ * r ^ n))
    (hEq :
      Set.EqOn g (fun u : ℂ ↦ ∑' n : ℕ, a n * (u - u0) ^ n) (Metric.ball u0 r)) :
    HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ a) u0 := by
  let g0 : ℂ → ℂ := fun z ↦ g (z + u0)
  have hEq0 :
      Set.EqOn g0 (fun z : ℂ ↦ ∑' n : ℕ, a n * z ^ n) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hz' : z + u0 ∈ Metric.ball u0 r := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
        using hz
    calc
      g0 z = g (z + u0) := rfl
      _ = ∑' n : ℕ, a n * ((z + u0) - u0) ^ n := hEq hz'
      _ = ∑' n : ℕ, a n * z ^ n := by
        refine tsum_congr fun n ↦ ?_
        simp [sub_eq_add_neg, add_assoc]
  have h0 : HasFPowerSeriesAt g0 (FormalMultilinearSeries.ofScalars ℂ a) 0 :=
    hasFPowerSeriesAtZeroOfEqTsumOnBall_local hr hs hEq0
  -- Translate the zero-centered owner back to the true center `u0`.
  simpa [g0, sub_eq_add_neg, add_assoc] using (h0.comp_sub u0)

/-- Helper for Theorem IV.5-extra-2: a single uniform bound on a boundary circle gives the usual
geometric bound on the coefficients of the corresponding scalar `cauchyPowerSeries`. -/
lemma cauchyPowerSeries_coeff_norm_le_div_pow_of_bound_on_circle
    {u0 : ℂ} {R M : ℝ} {F : ℂ → ℂ}
    (hR : 0 < R)
    (hbound : ∀ u, u ∈ Metric.sphere u0 R → ‖F u‖ ≤ M) :
    ∀ q : ℕ, ‖(cauchyPowerSeries F u0 R).coeff q‖ ≤ M / R ^ q := by
  intro q
  have hcoeffEq :
      (cauchyPowerSeries F u0 R).coeff q =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ u in C(u0, R), (u - u0)⁻¹ ^ q * ((u - u0)⁻¹ * F u)) := by
    -- Normalize the `q`th coefficient into its centered Cauchy-integral form once.
    rw [FormalMultilinearSeries.coeff]
    change (cauchyPowerSeries F u0 R q) (fun _ ↦ (1 : ℂ)) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ u in C(u0, R), (u - u0)⁻¹ ^ q * ((u - u0)⁻¹ * F u))
    rw [cauchyPowerSeries_apply]
    simp [smul_eq_mul, one_div, mul_assoc, mul_left_comm, mul_comm]
  calc
    ‖(cauchyPowerSeries F u0 R).coeff q‖
        =
          ‖((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ u in C(u0, R), (u - u0)⁻¹ ^ q * ((u - u0)⁻¹ * F u))‖ := by
              rw [hcoeffEq]
    _ ≤ R * (M / R ^ (q + 1)) := by
          apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
          intro u hu
          have hu_norm : ‖u - u0‖ = R := by
            simpa [Metric.mem_sphere, dist_eq_norm] using hu
          calc
            ‖(u - u0)⁻¹ ^ q * ((u - u0)⁻¹ * F u)‖
                = ‖(u - u0)⁻¹‖ ^ q * (‖(u - u0)⁻¹‖ * ‖F u‖) := by
                    simp [norm_pow]
            _ = R⁻¹ ^ q * (R⁻¹ * ‖F u‖) := by
                  simp [norm_inv, hu_norm]
            _ = R⁻¹ ^ (q + 1) * ‖F u‖ := by
                  rw [← mul_assoc, ← pow_succ]
            _ ≤ R⁻¹ ^ (q + 1) * M := by
                  gcongr
                  exact hbound u hu
            _ = M / R ^ (q + 1) := by
                  rw [div_eq_mul_inv, mul_comm, inv_pow]
    _ = M / R ^ q := by
          have hRne : R ≠ 0 := ne_of_gt hR
          rw [pow_succ, div_eq_mul_inv]
          field_simp [hRne]

/-- Helper for Theorem IV.5-extra-2: continuity on the closed disc gives a single boundary-circle
bound, so the corresponding scalar `cauchyPowerSeries` coefficients satisfy the usual geometric
estimate. -/
lemma cauchyPowerSeries_coeff_norm_le_div_pow_of_continuousOn_closedBall
    {u0 : ℂ} {R : NNReal} {F : ℂ → ℂ}
    (hR : 0 < R)
    (hcont : ContinuousOn F (Metric.closedBall u0 (R : ℝ))) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ q : ℕ, ‖(cauchyPowerSeries F u0 (R : ℝ)).coeff q‖ ≤ M / (R : ℝ) ^ q := by
  have hRreal : 0 < (R : ℝ) := hR
  have hcontSphere : ContinuousOn F (Metric.sphere u0 (R : ℝ)) := by
    exact hcont.mono Metric.sphere_subset_closedBall
  obtain ⟨M, hMbound⟩ :=
    (isCompact_sphere u0 (R : ℝ)).exists_bound_of_continuousOn (f := F) hcontSphere
  have hMnonneg : 0 ≤ M := by
    have hpoint : u0 + (R : ℂ) ∈ Metric.sphere u0 (R : ℝ) := by
      simp [Metric.mem_sphere, dist_eq_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRreal]
    exact le_trans (norm_nonneg _) (hMbound _ hpoint)
  refine ⟨M, hMnonneg, ?_⟩
  intro q
  exact
    cauchyPowerSeries_coeff_norm_le_div_pow_of_bound_on_circle
      (u0 := u0) (R := (R : ℝ)) (M := M) (F := F) hRreal
      (fun u hu ↦ hMbound u hu) q

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: fixing a transported block point on
the common block ball already gives one scalar geometric bound for the corresponding centered
last-variable Cauchy coefficients. -/
lemma transportedLastCauchyCoeff_pointwiseBound_ball_local
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 8) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let w0 : ℂ := (e z).2
    let r0 : ℝ := ρ / 8
    let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
      (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) w0 (ρ / 2)).coeff n
    ∀ x ∈ Metric.ball (e z).1 r0,
      ∃ Cx : ℝ, 0 ≤ Cx ∧
        ∀ n : ℕ, ‖A n x‖ ≤ Cx / (ρ / 2 : ℝ) ^ n := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
  let w0 : ℂ := (e z).2
  let r0 : ℝ := ρ / 8
  let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
    (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) w0 (ρ / 2)).coeff n
  dsimp [e, g, w0, r0, A]
  intro x hx
  have hρhalf_pos : 0 < ρ / 2 := by
    positivity
  have hSliceOn :
      AnalyticOnNhd ℂ (fun w ↦ g (x, w)) (Metric.closedBall w0 (ρ / 2)) := by
    -- Freeze the block point and reuse the transported last-slice analyticity on the whole closed
    -- disc supplied by the cylinder containment.
    simpa [w0] using
      transportedLastSlices_analyticOnNhd_closedBall
        (m := m) (D := D) (f := f) hsep (z := z) (r := r0) (R := ρ / 2) hcyl x hx
  let Rlast : NNReal := ⟨ρ / 2, hρhalf_pos.le⟩
  have hRlastPos : 0 < Rlast := by
    exact_mod_cast hρhalf_pos
  obtain ⟨Cx, hCxnonneg, hCx⟩ :=
    cauchyPowerSeries_coeff_norm_le_div_pow_of_continuousOn_closedBall
      (u0 := w0) (R := Rlast) (F := fun w ↦ g (x, w)) hRlastPos hSliceOn.continuousOn
  refine ⟨Cx, hCxnonneg, ?_⟩
  intro n
  -- Re-express the scalar Cauchy estimate in the local coefficient spelling used downstream.
  simpa [A, w0, Rlast, e, g, r0] using hCx n

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: a jointly continuous boundary family on
a compact parameter set and a fixed boundary circle yields one uniform geometric bound for all
centered Cauchy coefficients. -/
lemma cauchyPowerSeries_coeff_uniformBound_of_continuousOn_compact
    {E : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) {u0 : ℂ} {R : ℝ} (hR : 0 < R) {F : E → ℂ → ℂ}
    (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ Metric.sphere u0 R)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ K, ∀ q : ℕ, ‖(cauchyPowerSeries (F x) u0 R).coeff q‖ ≤ M / R ^ q := by
  obtain ⟨B, hB⟩ :=
    (hK.prod (isCompact_sphere u0 R)).exists_bound_of_continuousOn
      (f := Function.uncurry F) hcont
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx q
  have hbound : ∀ u, u ∈ Metric.sphere u0 R → ‖F x u‖ ≤ max B 0 := by
    intro u hu
    -- Restrict the compact product bound to the chosen parameter point before invoking the
    -- scalar Cauchy coefficient estimate.
    exact le_trans (hB (x, u) ⟨hx, hu⟩) (le_max_left _ _)
  -- Feed the compact torus bound into the scalar Cauchy estimate for the fixed parameter `x`.
  exact
    cauchyPowerSeries_coeff_norm_le_div_pow_of_bound_on_circle
      (u0 := u0) (R := R) (M := max B 0) (F := F x) hR hbound q

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on a compact closed parameter ball,
joint continuity of the boundary values yields one uniform geometric bound for all centered
Cauchy coefficients. -/
lemma cauchyPowerSeries_coeff_uniformBound_of_continuousOn_closedBall
    {E : Type*} [PseudoMetricSpace E] [ProperSpace E]
    {x0 : E} {r : ℝ} {u0 : ℂ} {R : ℝ} (hR : 0 < R) {F : E → ℂ → ℂ}
    (hcont :
      ContinuousOn (Function.uncurry F)
        (Metric.closedBall x0 r ×ˢ Metric.sphere u0 R)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Metric.closedBall x0 r, ∀ q : ℕ,
        ‖(cauchyPowerSeries (F x) u0 R).coeff q‖ ≤ M / R ^ q := by
  have hClosedCompact : IsCompact (Metric.closedBall x0 r) := isCompact_closedBall x0 r
  -- Reuse the compact-set coefficient estimate with the closed ball as the parameter compactum.
  exact
    cauchyPowerSeries_coeff_uniformBound_of_continuousOn_compact
      (hK := hClosedCompact) (u0 := u0) (R := R) hR hcont

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: a uniform geometric coefficient bound
at radius `R` makes the weighted norm series summable on the half-radius disc. -/
lemma summable_norm_mul_halfRadiusPow_of_geometricCoeffBound_local
    {a : ℕ → ℂ} {R C : ℝ} (hR : 0 < R) (_hC : 0 ≤ C)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C / R ^ n) :
    Summable (fun n : ℕ ↦ ‖a n‖ * (R / 2) ^ n) := by
  have hmajorant :
      ∀ n : ℕ, ‖a n‖ * (R / 2) ^ n ≤ C * ((1 / 2 : ℝ) ^ n) := by
    intro n
    have hpow_nonneg : 0 ≤ (R / 2) ^ n := by positivity
    have hRne : R ≠ 0 := ne_of_gt hR
    calc
      ‖a n‖ * (R / 2) ^ n ≤ (C / R ^ n) * (R / 2) ^ n := by
          exact mul_le_mul_of_nonneg_right (ha n) hpow_nonneg
      _ = C * ((1 / 2 : ℝ) ^ n) := by
            rw [show R / 2 = R * (1 / 2 : ℝ) by ring, mul_pow]
            field_simp [pow_ne_zero n hRne]
  -- Compare against the standard geometric series with ratio `1 / 2`.
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) hmajorant ?_
  simpa [mul_assoc] using (summable_geometric_two.mul_left C)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: a pointwise geometric coefficient bound
already gives the centered scalar power-series germ at the center. -/
lemma analyticAt_centeredScalarSeries_of_geometricCoeffBound_local
    {a : ℕ → ℂ} {u0 : ℂ} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C / R ^ n) :
    AnalyticAt ℂ (fun u : ℂ ↦ ∑' n : ℕ, a n * (u - u0) ^ n) u0 := by
  have hhalf_pos : 0 < R / 2 := by
    positivity
  have hsummable :
      Summable (fun n : ℕ ↦ ‖a n‖ * (R / 2 : ℝ) ^ n) :=
    summable_norm_mul_halfRadiusPow_of_geometricCoeffBound_local hR hC ha
  have hEq :
      Set.EqOn
        (fun u : ℂ ↦ ∑' n : ℕ, a n * (u - u0) ^ n)
        (fun u : ℂ ↦ ∑' n : ℕ, a n * (u - u0) ^ n)
        (Metric.ball u0 (R / 2)) := by
    -- The centered scalar series already has the required `tsum` presentation on the half-radius
    -- disc.
    intro u _hu
    rfl
  exact
    (hasFPowerSeriesAtOfEqTsumOnBall_centered_local
      (g := fun u : ℂ ↦ ∑' n : ℕ, a n * (u - u0) ^ n)
      (a := a) (u0 := u0) (r := R / 2) hhalf_pos hsummable hEq).analyticAt

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the same geometric coefficient bound
upgrades the centered scalar `tsum` to analyticity on the whole half-radius disc. -/
lemma analyticOnNhd_centeredScalarSeries_of_geometricCoeffBound_local
    {a : ℕ → ℂ} {u0 : ℂ} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C / R ^ n) :
    AnalyticOnNhd ℂ (fun u : ℂ ↦ ∑' n : ℕ, a n * (u - u0) ^ n) (Metric.ball u0 (R / 2)) := by
  let g : ℂ → ℂ := fun u : ℂ ↦ ∑' n : ℕ, a n * (u - u0) ^ n
  let g0 : ℂ → ℂ := fun z : ℂ ↦ g (z + u0)
  have hhalf_pos : 0 < R / 2 := by
    positivity
  have hsummable :
      Summable (fun n : ℕ ↦ ‖a n‖ * (R / 2 : ℝ) ^ n) :=
    summable_norm_mul_halfRadiusPow_of_geometricCoeffBound_local hR hC ha
  have hEq0 :
      Set.EqOn g0 (fun z : ℂ ↦ ∑' n : ℕ, a n * z ^ n) (Metric.ball (0 : ℂ) (R / 2)) := by
    intro z hz
    calc
      g0 z = g (z + u0) := rfl
      _ = ∑' n : ℕ, a n * ((z + u0) - u0) ^ n := by
            rfl
      _ = ∑' n : ℕ, a n * z ^ n := by
            refine tsum_congr fun n ↦ ?_
            simp [sub_eq_add_neg, add_assoc]
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
  let rnn : NNReal := ⟨R / 2, hhalf_pos.le⟩
  have hradius : ENNReal.ofReal (R / 2) ≤ p.radius := by
    have howner : Summable (fun n : ℕ ↦ ‖p n‖ * (rnn : ℝ) ^ n) := by
      simpa [p, rnn, FormalMultilinearSeries.ofScalars_norm] using hsummable
    simpa [rnn, ENNReal.ofReal_eq_coe_nnreal hhalf_pos.le] using
      (p.le_radius_of_summable_norm (r := rnn) howner)
  have hp_radius_pos : 0 < p.radius := by
    exact lt_of_lt_of_le (by simpa using ENNReal.ofReal_pos.mpr hhalf_pos) hradius
  have hseries_full :
      HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum a) p 0 p.radius := by
    -- Use the canonical scalar owner on its full radius before restricting back to the half-radius
    -- disc.
    simpa [p] using p.hasFPowerSeriesOnBall hp_radius_pos
  have hseries_half :
      HasFPowerSeriesOnBall
        (FormalMultilinearSeries.ofScalarsSum a) p 0 (ENNReal.ofReal (R / 2)) := by
    exact hseries_full.mono (by simpa using ENNReal.ofReal_pos.mpr hhalf_pos) hradius
  have hEqOn :
      Set.EqOn (FormalMultilinearSeries.ofScalarsSum a) g0
        (EMetric.ball (0 : ℂ) (ENNReal.ofReal (R / 2))) := by
    intro z hz
    have hzdist : ‖z‖ < R / 2 := by
      have hzenorm : ‖z‖ₑ < ENNReal.ofReal (R / 2) :=
        (mem_emetric_ball_zero_iff).1 hz
      exact (ENNReal.ofReal_lt_ofReal_iff hhalf_pos).1 (by
        simpa [ofReal_norm_eq_enorm] using hzenorm)
    have hz' : z ∈ Metric.ball (0 : ℂ) (R / 2) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzdist
    symm
    calc
      g0 z = ∑' n : ℕ, a n * z ^ n := hEq0 hz'
      _ = FormalMultilinearSeries.ofScalarsSum a z := by
            rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
            exact tsum_congr fun n ↦ by simp [smul_eq_mul]
  have hseriesTranslated :
      HasFPowerSeriesOnBall g0 p 0 (ENNReal.ofReal (R / 2)) := hseries_half.congr hEqOn
  have hseriesCentered :
      HasFPowerSeriesOnBall g p u0 (ENNReal.ofReal (R / 2)) := by
    -- Translate the zero-centered scalar owner back to the actual center `u0`.
    simpa [g, g0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hseriesTranslated.comp_sub u0)
  simpa [Metric.eball_ofReal, hhalf_pos, g] using hseriesCentered.analyticOnNhd

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: inside the half-radius disc, the
shifted monomial is controlled by the corresponding geometric half-radius factor. -/
lemma norm_sub_pow_le_halfRadius_geometric_local
    {u u0 : ℂ} {R : ℝ} (hR : 0 < R) (n : ℕ)
    (hu : u ∈ Metric.ball u0 (R / 2)) :
    ‖(u - u0) ^ n‖ ≤ R ^ n * (1 / 2 : ℝ) ^ n := by
  have hu_norm : ‖u - u0‖ < R / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hu
  have hhalf_nonneg : 0 ≤ R / 2 := by
    linarith
  -- First bound the shifted power by the half-radius norm budget coming from the chosen disc.
  calc
    ‖(u - u0) ^ n‖ = ‖u - u0‖ ^ n := by rw [norm_pow]
    _ ≤ (R / 2) ^ n := by
          exact pow_le_pow_left₀ (a := ‖u - u0‖) (b := R / 2) (by positivity) hu_norm.le n
    _ = R ^ n * (1 / 2 : ℝ) ^ n := by
          rw [show R / 2 = R * (1 / 2 : ℝ) by ring, mul_pow]

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: one closed-ball coefficient bound gives
uniform convergence of the centered parametric power-series terms on the corresponding half-radius
product neighborhood. -/
lemma hasSumUniformlyOn_parametricPowerSeries_terms_of_uniformCoeffBound_local
    {E : Type*} [PseudoMetricSpace E] {A : ℕ → E → ℂ}
    {x0 : E} {u0 : ℂ} {r R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hCoeffBound :
      ∀ x ∈ Metric.closedBall x0 r, ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    HasSumUniformlyOn
      (fun n : ℕ ↦ fun p : E × ℂ ↦ A n p.1 * (p.2 - u0) ^ n)
      (fun p : E × ℂ ↦ ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n)
      (Metric.closedBall x0 r ×ˢ Metric.ball u0 (R / 2)) := by
  have hmajorant : Summable (fun n : ℕ ↦ C * ((1 / 2 : ℝ) ^ n)) := by
    simpa [mul_assoc] using (summable_geometric_two.mul_left C)
  refine HasSumUniformlyOn.of_norm_le_summable hmajorant ?_
  intro n p hp
  have hcoeff : ‖A n p.1‖ ≤ C / R ^ n := hCoeffBound p.1 hp.1 n
  have hpow :
      ‖(p.2 - u0) ^ n‖ ≤ R ^ n * (1 / 2 : ℝ) ^ n :=
    norm_sub_pow_le_halfRadius_geometric_local hR n hp.2
  have hcoeffBudgetNonneg : 0 ≤ C / R ^ n := by
    positivity
  have hRne : R ≠ 0 := ne_of_gt hR
  -- Separate the coefficient norm from the shifted monomial, then feed in the uniform
  -- coefficient budget and the half-radius monomial budget in the natural order.
  calc
    ‖A n p.1 * (p.2 - u0) ^ n‖ = ‖A n p.1‖ * ‖(p.2 - u0) ^ n‖ := by
      rw [norm_mul]
    _ ≤ (C / R ^ n) * ‖(p.2 - u0) ^ n‖ := by
          exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ ≤ (C / R ^ n) * (R ^ n * (1 / 2 : ℝ) ^ n) := by
          exact mul_le_mul_of_nonneg_left hpow hcoeffBudgetNonneg
    _ = C * ((1 / 2 : ℝ) ^ n) := by
          field_simp [pow_ne_zero n hRne]

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: on a fixed closed product
neighborhood, a uniform geometric coefficient bound makes the parametric `tsum` continuous. -/
lemma continuousOn_parametricPowerSeries_of_uniformCoeffBound_local
    {E : Type*} [PseudoMetricSpace E] {A : ℕ → E → ℂ}
    {x0 : E} {u0 : ℂ} {r R C : ℝ} (hR : 0 < R)
    (hCoeffCont : ∀ n : ℕ, ContinuousOn (A n) (Metric.closedBall x0 r))
    (hCoeffBound :
      ∀ x ∈ Metric.closedBall x0 r, ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    ContinuousOn
      (fun p : E × ℂ ↦ ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n)
      (Metric.closedBall x0 r ×ˢ Metric.ball u0 (R / 2)) := by
  have hmajorant : Summable (fun n : ℕ ↦ C * ((1 / 2 : ℝ) ^ n)) := by
    simpa [mul_assoc] using (summable_geometric_two.mul_left C)
  refine
    continuousOn_tsum
      (f := fun n : ℕ ↦ fun p : E × ℂ ↦ A n p.1 * (p.2 - u0) ^ n)
      ?_ hmajorant ?_
  · intro n
    have hcoeff :
        ContinuousOn (fun p : E × ℂ ↦ A n p.1)
          (Metric.closedBall x0 r ×ˢ Metric.ball u0 (R / 2)) := by
      -- Compose the coefficient continuity with the first projection on the fixed product set.
      refine (hCoeffCont n).comp continuousOn_fst ?_
      intro p hp
      exact hp.1
    have hpow :
        ContinuousOn (fun p : E × ℂ ↦ (p.2 - u0) ^ n)
          (Metric.closedBall x0 r ×ˢ Metric.ball u0 (R / 2)) := by
      -- The shifted monomial depends only on the second coordinate and is continuous everywhere.
      exact (continuousOn_snd.sub continuousOn_const).pow n
    -- Each series term is the product of the continuous coefficient slice and the continuous
    -- centered monomial factor.
    exact hcoeff.mul hpow
  · intro n p hp
    have hCnonneg : 0 ≤ C := by
      have hzeroBound : ‖A 0 p.1‖ ≤ C := by
        simpa using hCoeffBound p.1 hp.1 0
      exact le_trans (norm_nonneg _) hzeroBound
    have hcoeff : ‖A n p.1‖ ≤ C / R ^ n := hCoeffBound p.1 hp.1 n
    have hpow :
        ‖(p.2 - u0) ^ n‖ ≤ R ^ n * (1 / 2 : ℝ) ^ n :=
      norm_sub_pow_le_halfRadius_geometric_local hR n hp.2
    have hcoeffBudgetNonneg : 0 ≤ C / R ^ n := by
      positivity
    have hRne : R ≠ 0 := ne_of_gt hR
    -- Separate the coefficient norm from the shifted monomial, then feed in the uniform
    -- coefficient budget and the half-radius monomial budget in the natural order.
    calc
      ‖A n p.1 * (p.2 - u0) ^ n‖ = ‖A n p.1‖ * ‖(p.2 - u0) ^ n‖ := by
        rw [norm_mul]
      _ ≤ (C / R ^ n) * ‖(p.2 - u0) ^ n‖ := by
            exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ ≤ (C / R ^ n) * (R ^ n * (1 / 2 : ℝ) ^ n) := by
            exact mul_le_mul_of_nonneg_left hpow hcoeffBudgetNonneg
      _ = C * ((1 / 2 : ℝ) ^ n) := by
            field_simp [pow_ne_zero n hRne]

/-- Helper for Theorem IV.5-extra-2: a boundary coefficient row with a single geometric majorant
can be integrated termwise, producing a centered scalar power series on the half-radius disc. -/
lemma centeredCircleIntegral_eq_tsum_onBall_of_geometricBound_local
    {u0 c : ℂ} {outerR innerR M : ℝ} (houter : 0 ≤ outerR) (hinner : 0 < innerR)
    (hM : 0 ≤ M) {b : ℕ → ℂ → ℂ}
    (hcont : ∀ q, ContinuousOn (b q) (Metric.sphere c outerR))
    (hbound : ∀ q ζ, ζ ∈ Metric.sphere c outerR → ‖b q ζ‖ ≤ M / innerR ^ q) :
    let a : ℕ → ℂ := fun q ↦
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, outerR), b q ζ)
    Summable (fun q ↦ ‖a q‖ * (innerR / 2) ^ q) ∧
      Set.EqOn
        (fun u : ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C(c, outerR), ∑' q : ℕ, b q ζ * (u - u0) ^ q))
        (fun u : ℂ ↦ ∑' q : ℕ, a q * (u - u0) ^ q)
        (Metric.ball u0 (innerR / 2)) := by
  let a : ℕ → ℂ := fun q ↦
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, outerR), b q ζ)
  have hhalf_pos : 0 < innerR / 2 := by
    positivity
  have ha_bound :
      ∀ q : ℕ, ‖a q‖ * (innerR / 2) ^ q ≤ outerR * M * ((1 / 2 : ℝ) ^ q) := by
    intro q
    have hcoeff :
        ‖a q‖ ≤ outerR * (M / innerR ^ q) := by
      -- Bound the integrated coefficient by the uniform circle majorant for the `q`th row.
      dsimp [a]
      exact
        circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const houter
          (fun ζ hζ ↦ hbound q ζ hζ)
    have hpow_nonneg : 0 ≤ (innerR / 2) ^ q := by positivity
    calc
      ‖a q‖ * (innerR / 2) ^ q
          ≤ (outerR * (M / innerR ^ q)) * (innerR / 2) ^ q := by
              exact mul_le_mul_of_nonneg_right hcoeff hpow_nonneg
      _ = outerR * ((M / innerR ^ q) * (innerR / 2) ^ q) := by ring
      _ = outerR * (M * ((1 / 2 : ℝ) ^ q)) := by
            rw [show innerR / 2 = innerR * (1 / 2 : ℝ) by ring, mul_pow]
            field_simp [hinner.ne']
      _ = outerR * M * ((1 / 2 : ℝ) ^ q) := by ring
  have hsum_a :
      Summable (fun q ↦ ‖a q‖ * (innerR / 2) ^ q) := by
    refine Summable.of_nonneg_of_le (fun q ↦ by positivity) ha_bound ?_
    simpa [mul_assoc] using (summable_geometric_two.mul_left (outerR * M))
  refine ⟨hsum_a, ?_⟩
  intro u hu
  have hu_norm : ‖u - u0‖ < innerR / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_sub_rev] using hu
  have hsum_u :
      SummableUniformlyOn
        (fun q : ℕ ↦ fun ζ : ℂ ↦ b q ζ * (u - u0) ^ q)
        (Metric.sphere c outerR) := by
    have hmajorant :
        Summable (fun q : ℕ ↦ M * ((1 / 2 : ℝ) ^ q)) := by
      simpa [mul_assoc] using (summable_geometric_two.mul_left M)
    refine
      (HasSumUniformlyOn.of_norm_le_summable hmajorant fun q ζ hζ ↦ ?_).summableUniformlyOn
    have hu_le : ‖u - u0‖ ≤ innerR / 2 := le_of_lt hu_norm
    calc
      ‖b q ζ * (u - u0) ^ q‖ = ‖b q ζ‖ * ‖u - u0‖ ^ q := by
        rw [norm_mul, norm_pow]
      _ ≤ (M / innerR ^ q) * ‖u - u0‖ ^ q := by
            gcongr
            exact hbound q ζ hζ
      _ ≤ (M / innerR ^ q) * (innerR / 2) ^ q := by
            gcongr
      _ = M * innerR ^ q * ((1 / 2 : ℝ) ^ q) / innerR ^ q := by
            rw [show innerR / 2 = innerR * (1 / 2 : ℝ) by ring, mul_pow]
            ring
      _ = M * ((1 / 2 : ℝ) ^ q) := by
            field_simp [hinner.ne']
  have hswap :
      (∮ ζ in C(c, outerR), ∑' q : ℕ, b q ζ * (u - u0) ^ q) =
        ∑' q : ℕ, ∮ ζ in C(c, outerR), b q ζ * (u - u0) ^ q := by
    exact
      circleIntegral_tsum_of_summableUniformlyOn_sphere_center_countable
        (c := c) (R := ⟨outerR, houter⟩)
        (fun q ↦ (hcont q).mul continuousOn_const) hsum_u
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(c, outerR), ∑' q : ℕ, b q ζ * (u - u0) ^ q)
        = ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
            ∑' q : ℕ, ∮ ζ in C(c, outerR), b q ζ * (u - u0) ^ q) := by
              simp [smul_eq_mul, hswap]
    _ = ∑' q : ℕ, ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∮ ζ in C(c, outerR), b q ζ * (u - u0) ^ q) := by
            symm
            exact tsum_mul_left
    _ = ∑' q : ℕ, a q * (u - u0) ^ q := by
          refine tsum_congr fun q ↦ ?_
          have hq :
              (∮ ζ in C(c, outerR), b q ζ * (u - u0) ^ q) =
                (u - u0) ^ q * ∮ ζ in C(c, outerR), b q ζ := by
            simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
              (circleIntegral.integral_smul ((u - u0) ^ q) (b q) c outerR)
          dsimp [a]
          rw [hq]
          ring

/-- Helper for Theorem IV.5-extra-2: once each boundary slice has a common-radius scalar power
series and the coefficient rows satisfy one geometric circle majorant, the integrated slice is
analytic at the center. -/
lemma analyticAt_centeredCircleIntegral_of_hasFPowerSeriesOnBall_coeffRow_local
    {u0 c : ℂ} {outerR M : ℝ} {innerR : NNReal} (houter : 0 ≤ outerR)
    (hinner : 0 < (innerR : ℝ))
    (hM : 0 ≤ M) {F : ℂ → ℂ → ℂ}
    (hseries :
      ∀ ζ ∈ Metric.sphere c outerR,
        HasFPowerSeriesOnBall (F ζ) (cauchyPowerSeries (F ζ) u0 innerR) u0 innerR)
    (hcont :
      ∀ q, ContinuousOn
        (fun ζ : ℂ ↦ (cauchyPowerSeries (F ζ) u0 innerR).coeff q)
        (Metric.sphere c outerR))
    (hbound :
      ∀ q ζ, ζ ∈ Metric.sphere c outerR →
        ‖(cauchyPowerSeries (F ζ) u0 innerR).coeff q‖ ≤ M / (innerR : ℝ) ^ q) :
    AnalyticAt ℂ
      (fun u : ℂ ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, outerR), F ζ u))
      u0 := by
  let a : ℕ → ℂ := fun q ↦
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ ζ in C(c, outerR), (cauchyPowerSeries (F ζ) u0 innerR).coeff q)
  have hhalf_pos : 0 < (innerR : ℝ) / 2 := by
    positivity
  have htermwise :=
    centeredCircleIntegral_eq_tsum_onBall_of_geometricBound_local
      (u0 := u0) (c := c) (outerR := outerR) (innerR := (innerR : ℝ)) (M := M)
      houter hinner hM hcont hbound
  rcases htermwise with ⟨hsum_a, hEq_tsum⟩
  have hEq_integrand :
      Set.EqOn
        (fun u : ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, outerR), F ζ u))
        (fun u : ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C(c, outerR),
              ∑' q : ℕ, (cauchyPowerSeries (F ζ) u0 innerR).coeff q * (u - u0) ^ q))
        (Metric.ball u0 ((innerR : ℝ) / 2)) := by
    intro u hu
    have hu_norm : ‖u - u0‖ < (innerR : ℝ) / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_sub_rev] using hu
    have hu_inner : ‖u - u0‖ < (innerR : ℝ) := by
      have hhalf_lt : (innerR : ℝ) / 2 < (innerR : ℝ) := by
        linarith
      exact lt_trans hu_norm hhalf_lt
    have hu' : u - u0 ∈ Metric.eball (0 : ℂ) innerR := by
      simpa [Metric.mem_eball, edist_dist, dist_eq_norm] using hu_inner
    have hInt :
        (∮ ζ in C(c, outerR), F ζ u) =
          ∮ ζ in C(c, outerR),
            ∑' q : ℕ, (cauchyPowerSeries (F ζ) u0 innerR).coeff q * (u - u0) ^ q := by
      apply circleIntegral.integral_congr houter
      intro ζ hζ
      have hsumζ := (hseries ζ hζ).sum hu'
      -- Evaluate each common-radius scalar owner at the displacement `u - u0`.
      calc
        F ζ u = ∑' q : ℕ, (u - u0) ^ q * (cauchyPowerSeries (F ζ) u0 innerR).coeff q := by
          simpa [FormalMultilinearSeries.sum, smul_eq_mul, add_sub_cancel] using hsumζ
        _ = ∑' q : ℕ, (cauchyPowerSeries (F ζ) u0 innerR).coeff q * (u - u0) ^ q := by
              refine tsum_congr fun q ↦ ?_
              ring
    simpa [smul_eq_mul] using congrArg (fun z : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹ * z)) hInt
  have hEq_total :
      Set.EqOn
        (fun u : ℂ ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, outerR), F ζ u))
        (fun u : ℂ ↦ ∑' q : ℕ, a q * (u - u0) ^ q)
        (Metric.ball u0 ((innerR : ℝ) / 2)) := by
    intro u hu
    calc
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, outerR), F ζ u)
          = ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
              ∮ ζ in C(c, outerR),
                ∑' q : ℕ, (cauchyPowerSeries (F ζ) u0 innerR).coeff q * (u - u0) ^ q) :=
            hEq_integrand hu
      _ = ∑' q : ℕ, a q * (u - u0) ^ q := hEq_tsum hu
  -- Convert the centered `tsum` identity on the half-radius disc into the target analyticity.
  exact hasFPowerSeriesAtOfEqTsumOnBall_centered_local
    (u0 := u0) (r := (innerR : ℝ) / 2) hhalf_pos hsum_a hEq_total |>.analyticAt

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: each centered parametric power-series
term is jointly analytic on a product set once its coefficient family is analytic on the first
factor. -/
lemma analyticOnNhd_parametricPowerSeriesTerm_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℕ → E → ℂ} {s : Set E} {t : Set ℂ} {u0 : ℂ} {n : ℕ}
    (hCoeffOn : AnalyticOnNhd ℂ (A n) s) :
    AnalyticOnNhd ℂ
      (fun p : E × ℂ ↦ A n p.1 * (p.2 - u0) ^ n)
      (s ×ˢ t) := by
  have hCoeffProd :
      AnalyticOnNhd ℂ (fun p : E × ℂ ↦ A n p.1) (s ×ˢ t) := by
    -- Pull the coefficient family back along the first projection on the chosen product set.
    exact hCoeffOn.comp
      (analyticOnNhd_fst (𝕜 := ℂ) (E := E) (F := ℂ) (t := s ×ˢ t))
      (fun p hp ↦ hp.1)
  have hPow :
      AnalyticOnNhd ℂ (fun p : E × ℂ ↦ (p.2 - u0) ^ n) (s ×ˢ t) := by
    -- The centered monomial depends only on the second coordinate and stays analytic everywhere.
    simpa using
      (((analyticOnNhd_snd (𝕜 := ℂ) (E := E) (F := ℂ) (t := s ×ˢ t)).sub
          analyticOnNhd_const).pow n)
  -- Multiply the coefficient germ by the centered monomial germ on the same product set.
  exact hCoeffProd.mul hPow

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: fixing the last variable in the centered
parametric series reduces the joint analyticity problem to the lower-dimensional induction
hypothesis on the block ball, once the coefficients have a uniform geometric bound there. -/
lemma analyticOnNhd_blockParametricPowerSeries_of_uniformCoeffBound_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    ∀ u ∈ Metric.ball u0 (R / 2),
      AnalyticOnNhd ℂ
        (fun x : Fin (m + 1) → ℂ ↦ ∑' n : ℕ, A n x * (u - u0) ^ n)
        (Metric.ball x0 (r / 2)) := by
  let r1 : ℝ := r / 2
  have hr1_le : r1 ≤ r := by
    dsimp [r1]
    linarith
  intro u hu
  have hsepBlock :
      ∀ x ∈ Metric.ball x0 r1, ∀ i : Fin (m + 1),
        AnalyticAt ℂ
          (fun w ↦ ∑' n : ℕ, A n (Function.update x i w) * (u - u0) ^ n)
          (x i) := by
    intro x hx i
    have hInsertCont :
        ContinuousAt (fun w : ℂ ↦ Function.update x i w) (x i) :=
      (analyticAt_update_coordinate x i).continuousAt
    have hInsertCenter :
        Function.update x i (x i) ∈ Metric.ball x0 r1 := by
      simpa using hx
    have hInsertNhds :
        (fun w : ℂ ↦ Function.update x i w) ⁻¹' Metric.ball x0 r1 ∈ nhds (x i) := by
      exact hInsertCont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hInsertCenter)
    rcases Metric.mem_nhds_iff.mp hInsertNhds with ⟨s, hspos, hsMaps⟩
    have htermDiff :
        ∀ n : ℕ,
          DifferentiableOn ℂ
            (fun w ↦ A n (Function.update x i w) * (u - u0) ^ n)
            (Metric.ball (x i) s) := by
      intro n w hw
      have hwSmall : Function.update x i w ∈ Metric.ball x0 r1 := hsMaps hw
      have hwOpen : Function.update x i w ∈ Metric.ball x0 r :=
        Metric.ball_subset_ball hr1_le hwSmall
      have hCoeffAt : AnalyticAt ℂ (A n) (Function.update x i w) := hCoeffOn n _ hwOpen
      have hUpdateAt : AnalyticAt ℂ (fun v : ℂ ↦ Function.update x i v) w := by
        simpa [Function.update] using
          (analyticAt_update_coordinate (Function.update x i w) i)
      -- Compose the coefficient germ with the coordinate insertion before multiplying by the fixed
      -- scalar factor `(u - u0)^n`.
      exact ((hCoeffAt.comp hUpdateAt).mul analyticAt_const).differentiableAt.differentiableWithinAt
    have htermBound :
        ∀ n : ℕ, ∀ w ∈ Metric.ball (x i) s,
          ‖A n (Function.update x i w) * (u - u0) ^ n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
      intro n w hw
      have hwSmall : Function.update x i w ∈ Metric.ball x0 r1 := hsMaps hw
      have hwClosed : Function.update x i w ∈ Metric.closedBall x0 r1 :=
        Metric.ball_subset_closedBall hwSmall
      have hCoeffBudget : ‖A n (Function.update x i w)‖ ≤ C / R ^ n :=
        hCoeffBound _ hwClosed n
      have hPowerBudget :
          ‖(u - u0) ^ n‖ ≤ R ^ n * (1 / 2 : ℝ) ^ n :=
        norm_sub_pow_le_halfRadius_geometric_local hR n hu
      have hCoeffBudgetNonneg : 0 ≤ C / R ^ n := by
        exact le_trans (norm_nonneg _) hCoeffBudget
      have hRne : R ≠ 0 := ne_of_gt hR
      -- Separate the coefficient norm from the fixed last-variable power before feeding the
      -- geometric coefficient budget into the standard half-radius majorant.
      calc
        ‖A n (Function.update x i w) * (u - u0) ^ n‖
            = ‖A n (Function.update x i w)‖ * ‖(u - u0) ^ n‖ := by
                rw [norm_mul]
        _ ≤ (C / R ^ n) * ‖(u - u0) ^ n‖ := by
              exact mul_le_mul_of_nonneg_right hCoeffBudget (norm_nonneg _)
        _ ≤ (C / R ^ n) * (R ^ n * (1 / 2 : ℝ) ^ n) := by
              exact mul_le_mul_of_nonneg_left hPowerBudget hCoeffBudgetNonneg
        _ = C * (1 / 2 : ℝ) ^ n := by
              field_simp [pow_ne_zero n hRne]
    have hsummable :
        Summable (fun n : ℕ ↦ C * (1 / 2 : ℝ) ^ n) := by
      simpa [mul_assoc] using (summable_geometric_two.mul_left C)
    have hDiffOn :
        DifferentiableOn ℂ
          (fun w ↦ ∑' n : ℕ, A n (Function.update x i w) * (u - u0) ^ n)
          (Metric.ball (x i) s) := by
      exact
        Complex.differentiableOn_tsum_of_summable_norm hsummable htermDiff Metric.isOpen_ball
          htermBound
    have hAnalyticOn :
        AnalyticOnNhd ℂ
          (fun w ↦ ∑' n : ℕ, A n (Function.update x i w) * (u - u0) ^ n)
          (Metric.ball (x i) s) := by
      -- Once the one-variable series is differentiable on the small ball, convert it back to the
      -- analytic owner needed by `ih`.
      exact hDiffOn.analyticOnNhd Metric.isOpen_ball
    have hxBall : x i ∈ Metric.ball (x i) s := by
      simpa [Metric.mem_ball] using hspos
    exact hAnalyticOn (x i) hxBall
  -- Feed the coordinatewise analyticity of the fixed-`u` slice into the lower-dimensional
  -- Hartogs induction hypothesis on the smaller block ball.
  exact ih Metric.isOpen_ball hsepBlock

-- TODO: upgrade the explicit product-ball partial sums and their locally uniform convergence to
-- analyticity of the centered parametric `tsum` at the center.
/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: every centered partial sum is analytic
at the center of the explicit product ball on which the theorem-local limit argument runs. -/
lemma centeredParametricPartialSums_analyticAt_center_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hPartialOn :
      ∀ N : ℕ,
        AnalyticOnNhd ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
            (Finset.range N).sum (fun n ↦ A n p.1 * (p.2 - u0) ^ n))
          (Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2))) :
    ∀ N : ℕ,
      AnalyticAt ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
          (Finset.range N).sum (fun n ↦ A n p.1 * (p.2 - u0) ^ n))
        (x0, u0) := by
  intro N
  have hx0 : x0 ∈ Metric.ball x0 r := by
    -- The block center belongs to every positive-radius ball around itself.
    simpa [Metric.mem_ball] using hr
  have hu0 : u0 ∈ Metric.ball u0 (R / 2) := by
    -- The last-coordinate center likewise belongs to the half-radius ball used in the limit step.
    have hhalf : 0 < R / 2 := by
      positivity
    simpa [Metric.mem_ball] using hhalf
  -- Read off the center germ directly from the open-set analytic owner for the partial sum.
  exact (hPartialOn N) (x0, u0) ⟨hx0, hu0⟩

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the same centered partial sums are
already smooth at the center, so the remaining direct-series blocker is only the infinite-sum
upgrade rather than any finite-stage regularity issue. -/
lemma centeredParametricPartialSums_contDiffAt_center_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hPartialOn :
      ∀ N : ℕ,
        AnalyticOnNhd ℂ
          (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
            (Finset.range N).sum (fun n ↦ A n p.1 * (p.2 - u0) ^ n))
          (Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2))) :
    ∀ N : ℕ,
      ContDiffAt ℂ ⊤
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
          (Finset.range N).sum (fun n ↦ A n p.1 * (p.2 - u0) ^ n))
        (x0, u0) := by
  intro N
  -- Convert the already-closed analytic center germ of the `N`th partial sum to smoothness once.
  exact
    (centeredParametricPartialSums_analyticAt_center_local
      (m := m) (A := A) (x0 := x0) (u0 := u0) (r := r) (R := R)
      hr hR hPartialOn N).contDiffAt

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the centered parametric-series closeout
should be stated directly in the coefficient-bound variables seen by the caller, not through an
unsupported generic locally-uniform-limit interface. -/
lemma analyticAt_centeredParametricSeries_of_uniformCoeffBound_local
    {m : ℕ}
    (prodHartogs :
      ∀ {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ},
        IsOpen D →
        (∀ p ∈ D,
          AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ G (w, p.2)) p.1 ∧
            AnalyticAt ℂ (fun w : ℂ ↦ G (p.1, w)) p.2) →
        AnalyticOnNhd ℂ G D)
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    AnalyticAt ℂ
      (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n)
      (x0, u0) := by
  let r1 : ℝ := r / 2
  have hr1_pos : 0 < r1 := by
    dsimp [r1]
    positivity
  have hx0 : x0 ∈ Metric.ball x0 r1 := by
    -- The center belongs to the smaller block ball used by the product-domain closeout.
    simpa [Metric.mem_ball, r1] using hr1_pos
  have hx0_closed : x0 ∈ Metric.closedBall x0 r1 := by
    -- Record once that the center also lies in the corresponding closed ball for the coefficient
    -- bounds.
    simpa [Metric.mem_closedBall, r1] using (show 0 ≤ r / 2 by positivity)
  have hCnonneg : 0 ≤ C := by
    -- Read nonnegativity of the geometric constant off the zeroth coefficient at the center.
    have hzero : ‖A 0 x0‖ ≤ C := by
      simpa [pow_zero] using hCoeffBound x0 hx0_closed 0
    exact le_trans (norm_nonneg _) hzero
  have hhalf_pos : 0 < R / 2 := by
    positivity
  have hLastSlices :
      ∀ x ∈ Metric.ball x0 r1,
        AnalyticOnNhd ℂ
          (fun u : ℂ ↦ ∑' n : ℕ, A n x * (u - u0) ^ n)
          (Metric.ball u0 (R / 2)) := by
    intro x hx
    have hxClosed : x ∈ Metric.closedBall x0 r1 := Metric.ball_subset_closedBall hx
    -- Freeze the block point and use the scalar geometric-series owner on the last-variable disc.
    simpa using
      analyticOnNhd_centeredScalarSeries_of_geometricCoeffBound_local
        (a := fun n : ℕ ↦ A n x) (u0 := u0) (R := R) (C := C)
        hR hCnonneg (hCoeffBound x hxClosed)
  have hu0 : u0 ∈ Metric.ball u0 (R / 2) := by
    -- The center of the last-variable disc belongs to every positive-radius ball around itself.
    simpa [Metric.mem_ball] using hhalf_pos
  have hBlockSlices :
      ∀ u ∈ Metric.ball u0 (R / 2),
        AnalyticOnNhd ℂ
          (fun x : Fin (m + 1) → ℂ ↦ ∑' n : ℕ, A n x * (u - u0) ^ n)
          (Metric.ball x0 r1) := by
    -- Route correction: the support-level closeout no longer tries to re-prove any product Hartogs
    -- owner here; it only packages the fixed-`u` block analyticity already available from `ih`.
    simpa [r1] using
      analyticOnNhd_blockParametricPowerSeries_of_uniformCoeffBound_local
        (m := m) ih (x0 := x0) (u0 := u0) (r := r) (R := R) (C := C)
        hr hR hCoeffOn hCoeffBound
  let Dprod : Set ((Fin (m + 1) → ℂ) × ℂ) := Metric.ball x0 r1 ×ˢ Metric.ball u0 (R / 2)
  let Gprod : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
    ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n
  have hDprod : IsOpen Dprod := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hSepProd :
      ∀ p ∈ Dprod,
        AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ Gprod (w, p.2)) p.1 ∧
          AnalyticAt ℂ (fun w : ℂ ↦ Gprod (p.1, w)) p.2 := by
    intro p hp
    constructor
    · -- Fix the last variable and reuse the lower-dimensional block owner on the smaller block
      -- ball.
      exact hBlockSlices p.2 hp.2 p.1 hp.1
    · -- Fix the block variable and use the scalar geometric-series owner on the last-variable disc.
      exact hLastSlices p.1 hp.1 p.2 hp.2
  have hProdOn : AnalyticOnNhd ℂ Gprod Dprod := prodHartogs hDprod hSepProd
  have hCenter : (x0, u0) ∈ Dprod := ⟨hx0, hu0⟩
  -- The center lies in the chosen product neighborhood, so the product Hartogs owner closes the
  -- desired analytic germ immediately.
  exact hProdOn (x0, u0) hCenter

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once a product-coordinate Hartogs owner
is available as an explicit premise, one uniform geometric coefficient bound on the smaller closed
block ball closes the centered parametric power-series analyticity step without any file-order
recursion. -/
lemma analyticAt_parametricPowerSeries_of_uniformCoeffBound_of_prodHartogs_local
    {m : ℕ}
    (prodHartogs :
      ∀ {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ},
        IsOpen D →
        (∀ p ∈ D,
          AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ G (w, p.2)) p.1 ∧
            AnalyticAt ℂ (fun w : ℂ ↦ G (p.1, w)) p.2) →
        AnalyticOnNhd ℂ G D)
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    AnalyticAt ℂ (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n)
      (x0, u0) := by
  let r1 : ℝ := r / 2
  have hr1_pos : 0 < r1 := by
    dsimp [r1]
    positivity
  have hx0 : x0 ∈ Metric.ball x0 r1 := by
    -- The center belongs to the smaller block ball used by the product-domain closeout.
    simpa [Metric.mem_ball, r1] using hr1_pos
  have hx0_closed : x0 ∈ Metric.closedBall x0 r1 := by
    -- Record once that the center also lies in the corresponding closed ball for the coefficient
    -- bounds.
    simpa [Metric.mem_closedBall, r1] using (show 0 ≤ r / 2 by positivity)
  have hCnonneg : 0 ≤ C := by
    -- Read nonnegativity of the geometric constant off the zeroth coefficient at the center.
    have hzero : ‖A 0 x0‖ ≤ C := by
      simpa [pow_zero] using hCoeffBound x0 hx0_closed 0
    exact le_trans (norm_nonneg _) hzero
  have hhalf_pos : 0 < R / 2 := by
    positivity
  have hLastSlices :
      ∀ x ∈ Metric.ball x0 r1,
        AnalyticOnNhd ℂ
          (fun u : ℂ ↦ ∑' n : ℕ, A n x * (u - u0) ^ n)
          (Metric.ball u0 (R / 2)) := by
    intro x hx
    have hxClosed : x ∈ Metric.closedBall x0 r1 := Metric.ball_subset_closedBall hx
    -- Freeze the block point and use the scalar geometric-series owner on the last-variable disc.
    simpa using
      analyticOnNhd_centeredScalarSeries_of_geometricCoeffBound_local
        (a := fun n : ℕ ↦ A n x) (u0 := u0) (R := R) (C := C)
        hR hCnonneg (hCoeffBound x hxClosed)
  have hu0 : u0 ∈ Metric.ball u0 (R / 2) := by
    -- The center of the last-variable disc belongs to every positive-radius ball around itself.
    simpa [Metric.mem_ball] using hhalf_pos
  have hBlockSlices :
      ∀ u ∈ Metric.ball u0 (R / 2),
        AnalyticOnNhd ℂ
          (fun x : Fin (m + 1) → ℂ ↦ ∑' n : ℕ, A n x * (u - u0) ^ n)
          (Metric.ball x0 r1) := by
    -- Route correction: the support-level closeout no longer tries to re-prove any product Hartogs
    -- owner here; it only packages the fixed-`u` block analyticity already available from `ih`.
    simpa [r1] using
      analyticOnNhd_blockParametricPowerSeries_of_uniformCoeffBound_local
        (m := m) ih (x0 := x0) (u0 := u0) (r := r) (R := R) (C := C)
        hr hR hCoeffOn hCoeffBound
  let Dprod : Set ((Fin (m + 1) → ℂ) × ℂ) := Metric.ball x0 r1 ×ˢ Metric.ball u0 (R / 2)
  let Gprod : (Fin (m + 1) → ℂ) × ℂ → ℂ := fun p ↦
    ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n
  have hDprod : IsOpen Dprod := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hSepProd :
      ∀ p ∈ Dprod,
        AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ Gprod (w, p.2)) p.1 ∧
          AnalyticAt ℂ (fun w : ℂ ↦ Gprod (p.1, w)) p.2 := by
    intro p hp
    constructor
    · -- Fix the last variable and reuse the lower-dimensional block owner on the smaller block
      -- ball.
      exact hBlockSlices p.2 hp.2 p.1 hp.1
    · -- Fix the block variable and use the scalar geometric-series owner on the last-variable disc.
      exact hLastSlices p.1 hp.1 p.2 hp.2
  have hProdOn : AnalyticOnNhd ℂ Gprod Dprod := prodHartogs hDprod hSepProd
  have hCenter : (x0, u0) ∈ Dprod := ⟨hx0, hu0⟩
  -- The center lies in the chosen product neighborhood, so the product Hartogs owner closes the
  -- desired analytic germ immediately.
  exact hProdOn (x0, u0) hCenter

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: a smaller closed ball sits inside a
strictly larger open ball with the same center. -/
lemma closedBall_subset_ball_of_lt
    {E : Type*} [PseudoMetricSpace E] {x0 : E} {r₁ r₂ : ℝ}
    (hr : r₁ < r₂) :
    Metric.closedBall x0 r₁ ⊆ Metric.ball x0 r₂ := by
  intro x hx
  have hxle : dist x x0 ≤ r₁ := by
    simpa [Metric.mem_closedBall] using hx
  have hxlt : dist x x0 < r₂ := lt_of_le_of_lt hxle hr
  simpa [Metric.mem_ball] using hxlt

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: analyticity on an open ball gives
continuity on every strictly smaller closed ball with the same center. -/
lemma continuousOn_closedBall_of_analyticOnNhd_ball
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {x0 : E} {r₁ r₂ : ℝ}
    (hr : r₁ < r₂)
    (hf : AnalyticOnNhd ℂ f (Metric.ball x0 r₂)) :
    ContinuousOn f (Metric.closedBall x0 r₁) := by
  -- Restrict the ambient continuity owner from the larger analytic ball to the smaller compact
  -- closed ball once, so later coefficient packages can work on a fixed compact neighborhood.
  exact hf.continuousOn.mono (closedBall_subset_ball_of_lt hr)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: a pointwise coefficient package on an
open ball restricts unchanged to every strictly smaller closed ball, while analyticity supplies the
matching closed-ball continuity owner. -/
lemma localCoeffPackageOnClosedBall_of_openBall
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℕ → E → ℂ} {x0 : E} {r₁ r₂ R : ℝ}
    (hr : r₁ < r₂)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r₂))
    (hCoeffBound :
      ∀ x ∈ Metric.ball x0 r₂, ∃ Cx : ℝ, 0 ≤ Cx ∧
        ∀ n : ℕ, ‖A n x‖ ≤ Cx / R ^ n) :
    (∀ n : ℕ, ContinuousOn (A n) (Metric.closedBall x0 r₁)) ∧
      ∀ x ∈ Metric.closedBall x0 r₁, ∃ Cx : ℝ, 0 ≤ Cx ∧
        ∀ n : ℕ, ‖A n x‖ ≤ Cx / R ^ n := by
  constructor
  · intro n
    -- Shrink each analytic coefficient owner once to the smaller compact closed ball.
    exact
      continuousOn_closedBall_of_analyticOnNhd_ball
        (x0 := x0) (r₁ := r₁) (r₂ := r₂) hr (hCoeffOn n)
  · intro x hx
    have hxBall : x ∈ Metric.ball x0 r₂ := closedBall_subset_ball_of_lt hr hx
    -- Reuse the original pointwise geometric budget at the same point after shrinking the set.
    exact hCoeffBound x hxBall
