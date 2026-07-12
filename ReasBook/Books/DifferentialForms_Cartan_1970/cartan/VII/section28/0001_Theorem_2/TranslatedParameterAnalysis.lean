import DifferentialForms_Cartan_1970.VII.section27.«0001_Theorem_I»
import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».BanachFormalSeries
import DifferentialForms_Cartan_1970.VII.section28.«0001_Theorem_2».LocalHolomorphicSystems
import Mathlib

open Filter
open Set

open scoped Topology

/-- Helper for Cartan section28 0001_Theorem_2: freezing all but one parameter coordinate and
translating the active coordinate preserves analyticity of the right-hand side. -/
theorem analyticOnNhd_coordinateUpdate_rhs
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (t0 : Fin j → ℂ) (r : Fin j) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
        F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
      {p : ℂ × (Fin k → ℂ) × ℂ |
        (p.1, p.2.1, Function.update t0 r (t0 r + p.2.2)) ∈ Ω} := by
  intro p hp
  have hbase :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F q.1 q.2.1 q.2.2)
        (p.1, p.2.1, Function.update t0 r (t0 r + p.2.2)) :=
    hF _ hp
  have hupdate :
      AnalyticAt ℂ (fun u : ℂ ↦ Function.update t0 r (t0 r + u)) p.2.2 := by
    -- Each frozen coordinate is constant, while the active coordinate is affine in `u`.
    refine AnalyticAt.pi fun i ↦ ?_
    by_cases hir : i = r
    · subst hir
      simpa [Function.update] using
        (analyticAt_const.add (analyticAt_id : AnalyticAt ℂ (fun u : ℂ ↦ u) p.2.2))
    · have hconst : (fun u : ℂ ↦ Function.update t0 r (t0 r + u) i) = fun _ ↦ t0 i := by
        funext u
        simp [Function.update, hir]
      rw [hconst]
      exact analyticAt_const
  have hy :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × ℂ ↦ q.2.1) p := by
    simpa using
      (analyticAt_fst.comp
        (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ((Fin k → ℂ) × ℂ) ↦ q.2) p))
  have hu :
      AnalyticAt ℂ (fun q : ℂ × (Fin k → ℂ) × ℂ ↦ q.2.2) p := by
    simpa using
      (analyticAt_snd.comp
        (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ((Fin k → ℂ) × ℂ) ↦ q.2) p))
  have hparam :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦ Function.update t0 r (t0 r + q.2.2))
        p := by
    simpa using hupdate.comp_of_eq hu rfl
  have hpair :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦
          (q.2.1, Function.update t0 r (t0 r + q.2.2)))
        p := by
    simpa using hy.prod hparam
  have hmap :
      AnalyticAt ℂ
        (fun q : ℂ × (Fin k → ℂ) × ℂ ↦
          (q.1, q.2.1, Function.update t0 r (t0 r + q.2.2)))
        p := by
    simpa using
      (analyticAt_fst : AnalyticAt ℂ (fun q : ℂ × ((Fin k → ℂ) × ℂ) ↦ q.1) p).prod hpair
  -- Compose the ambient analytic model with the coordinate-update embedding.
  simpa using hbase.comp_of_eq hmap rfl

/-- Helper for Cartan section28 0001_Theorem_2: each frozen-coordinate scalar-parameter slice of
the original family remains a zero-initial holomorphic solution on `Ux`. -/
theorem coordinateUpdateOneParamHypotheses
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Ux : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ φ (x, t)))
    {r : Fin j} {t0 : Fin j → ℂ} {u : ℂ}
    (hu : Function.update t0 r (t0 r + u) ∈ Vx) :
    IsHolomorphicSystemSolutionOn
      {p : ℂ × (Fin k → ℂ) |
        (p.1, p.2, Function.update t0 r (t0 r + u)) ∈ Ω}
      (fun x y ↦ F x y (Function.update t0 r (t0 r + u)))
      0
      0
      Ux
      (fun x ↦ φ (x, Function.update t0 r (t0 r + u))) := by
  -- The slice is exactly one of the given solution slices, with the updated parameter plugged in.
  simpa using hsol (Function.update t0 r (t0 r + u)) hu

/-- Helper for Cartan section28 0001_Theorem_2: the existing owner hypothesis already gives
analyticity of every fixed-parameter `x`-slice. -/
theorem solutionSliceAnalyticOnNhd
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Ux : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ φ (x, t))) :
    ∀ t ∈ Vx, AnalyticOnNhd ℂ (fun x ↦ φ (x, t)) Ux := by
  intro t ht
  -- Read analyticity directly from the source-facing slice owner.
  exact (hsol t ht).analytic

/-- Helper for Cartan section28 0001_Theorem_2: around any base parameter `t0 ∈ Vx`, one can
vary a single coordinate by a small scalar neighborhood while staying inside `Vx`. -/
theorem exists_coordinateUpdateNeighborhood
    {j : ℕ} {Vx : Set (Fin j → ℂ)}
    (hVx : IsOpen Vx) {t0 : Fin j → ℂ} (ht0 : t0 ∈ Vx) (r : Fin j) :
    ∃ Vr : Set ℂ,
      IsOpen Vr ∧
      (0 : ℂ) ∈ Vr ∧
      Set.MapsTo (fun u ↦ Function.update t0 r (t0 r + u)) Vr Vx := by
  -- The translated coordinate-update map is analytic, hence continuous, at the scalar origin.
  have hupdateAt :
      AnalyticAt ℂ (fun u : ℂ ↦ Function.update t0 r (t0 r + u)) 0 := by
    refine AnalyticAt.pi fun i ↦ ?_
    by_cases hir : i = r
    · subst hir
      simpa [Function.update] using
        (analyticAt_const.add (analyticAt_id : AnalyticAt ℂ (fun u : ℂ ↦ u) 0))
    · have hconst :
          (fun u : ℂ ↦ Function.update t0 r (t0 r + u) i) = fun _ ↦ t0 i := by
        funext u
        simp [Function.update, hir]
      rw [hconst]
      exact analyticAt_const
  have hpre :
      (fun u : ℂ ↦ Function.update t0 r (t0 r + u)) ⁻¹' Vx ∈ 𝓝 (0 : ℂ) := by
    have hbase :
        Function.update t0 r (t0 r + (0 : ℂ)) ∈ Vx := by
      simpa [Function.update] using ht0
    exact hupdateAt.continuousAt.preimage_mem_nhds (hVx.mem_nhds hbase)
  rcases _root_.mem_nhds_iff.mp hpre with ⟨Vr, hVrsub, hVr, h0Vr⟩
  refine ⟨Vr, hVr, h0Vr, ?_⟩
  intro u hu
  exact hVrsub hu

/-- Helper for Cartan section28 0001_Theorem_2: every open `x`-neighborhood of `0` contains a
smaller preconnected ball around `0`. -/
theorem choosePreconnectedXNeighborhood
    {Ux : Set ℂ}
    (hUx : IsOpen Ux) (h0Ux : (0 : ℂ) ∈ Ux) :
    ∃ Bx : Set ℂ,
      IsOpen Bx ∧
      IsPreconnected Bx ∧
      (0 : ℂ) ∈ Bx ∧
      Bx ⊆ Ux := by
  -- Replace the ambient open neighborhood by a metric ball so slice-wise uniqueness can use a
  -- canonical preconnected `x`-domain.
  rcases Metric.mem_nhds_iff.mp (hUx.mem_nhds h0Ux) with ⟨r, hrpos, hrsub⟩
  refine ⟨Metric.ball (0 : ℂ) r, Metric.isOpen_ball, ?_, Metric.mem_ball_self hrpos, ?_⟩
  · exact (convex_ball (0 : ℂ) r).isPreconnected
  · simpa using hrsub

/-- Helper for Cartan section28 0001_Theorem_2: after freezing all but one parameter coordinate
and translating the active one, the pulled-back scalar system still has a genuine Taylor model at
the scalar origin. -/
theorem translatedCoordinateUpdate_rhsHasFPowerSeriesAtOrigin
    {k j : ℕ} {Ω : Set (ℂ × (Fin k → ℂ) × (Fin j → ℂ))}
    {F : ℂ → (Fin k → ℂ) → (Fin j → ℂ) → Fin k → ℂ}
    {Ux : Set ℂ} {Vx : Set (Fin j → ℂ)}
    {φ : ℂ × (Fin j → ℂ) → Fin k → ℂ}
    (hF : AnalyticOnNhd ℂ (fun p : ℂ × (Fin k → ℂ) × (Fin j → ℂ) ↦ F p.1 p.2.1 p.2.2) Ω)
    (hsol :
      ∀ t ∈ Vx,
        IsHolomorphicSystemSolutionOn
          {p : ℂ × (Fin k → ℂ) | (p.1, p.2, t) ∈ Ω}
          (fun x y ↦ F x y t)
          0
          0
          Ux
          (fun x ↦ φ (x, t)))
    {t0 : Fin j → ℂ} (ht0 : t0 ∈ Vx) (r : Fin j) :
    ∃ Qtr : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ) × ℂ) (Fin k → ℂ),
      HasFPowerSeriesAt
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        Qtr
        ((0 : ℂ), (0 : Fin k → ℂ), 0) ∧
      0 < Qtr.radius := by
  -- Route correction: use the coordinate-update analyticity transport at the translated base
  -- point instead of trying to reuse the obsolete global-origin Taylor model.
  have htranslated :
      AnalyticOnNhd ℂ
        (fun p : ℂ × (Fin k → ℂ) × ℂ ↦
          F p.1 p.2.1 (Function.update t0 r (t0 r + p.2.2)))
        {p : ℂ × (Fin k → ℂ) × ℂ |
          (p.1, p.2.1, Function.update t0 r (t0 r + p.2.2)) ∈ Ω} :=
    analyticOnNhd_coordinateUpdate_rhs hF t0 r
  have h0translated :
      ((0 : ℂ), (0 : Fin k → ℂ), 0) ∈
        {p : ℂ × (Fin k → ℂ) × ℂ |
          (p.1, p.2.1, Function.update t0 r (t0 r + p.2.2)) ∈ Ω} := by
    -- The zero-initial original slice places the translated scalar origin back in `Ω`.
    simpa [Function.update] using zero_section_mem_coeff_domain hsol ht0
  obtain ⟨Qtr, hQtr⟩ := htranslated _ h0translated
  exact ⟨Qtr, hQtr, HasFPowerSeriesAt.radius_pos hQtr⟩

/-- Helper for Cartan section28 0001_Theorem_2: on the weighted `lp` parameter carrier, evaluating
the coefficient sequence at a scalar parameter strictly inside the working radius is summable. -/
theorem weightedParameterSummable
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ)
    (f : lp (fun _ : ℕ => Fin k → ℂ) 1) :
    Summable (fun n : ℕ ↦ ((u / (ρ : ℂ)) ^ n) • f n) := by
  -- First read summability of the unweighted coefficient norms from the `lp` membership.
  have hp : 0 < ENNReal.toReal (1 : ENNReal) := by
    norm_num
  have hsum_norm : Summable (fun n : ℕ ↦ ‖f n‖) := by
    simpa using (lp.memℓp f).summable hp
  -- Then the strict radius bound makes the geometric weights uniformly bounded by `1`.
  have hratio : ‖u / (ρ : ℂ)‖ < 1 := by
    rw [norm_div]
    have hρnorm : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
      simp
    rw [hρnorm]
    have hρpos : 0 < (ρ : ℝ) := lt_of_le_of_lt (norm_nonneg u) hu
    exact (div_lt_one hρpos).2 hu
  exact Summable.of_norm_bounded hsum_norm <| by
    intro n
    rw [norm_smul, norm_pow]
    calc
      ‖u / (ρ : ℂ)‖ ^ n * ‖f n‖ ≤ 1 * ‖f n‖ := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) hratio.le
      _ = ‖f n‖ := by
        ring

/-- Helper for Cartan section28 0001_Theorem_2: evaluating a weighted `lp` coefficient sequence at
a parameter `u` with `‖u‖ < ρ` defines a continuous linear map. -/
noncomputable def weightedParameterEvalCLM
    {k : ℕ} (ρ : NNReal) (u : ℂ)
    (hu : ‖u‖ < ρ) :
    lp (fun _ : ℕ => Fin k → ℂ) 1 →L[ℂ] (Fin k → ℂ) := by
  let L : lp (fun _ : ℕ => Fin k → ℂ) 1 →ₗ[ℂ] Fin k → ℂ :=
    { toFun := fun f ↦ ∑' n : ℕ, ((u / (ρ : ℂ)) ^ n) • f n
      map_add' := by
        intro f g
        -- The weighted evaluation is termwise additive, so the two summable series add.
        change ∑' n : ℕ, (((u / (ρ : ℂ)) ^ n) • (f n + g n)) = _
        have hf := weightedParameterSummable hu f
        have hg := weightedParameterSummable hu g
        simpa [smul_add] using (hf.tsum_add hg)
      map_smul' := by
        intro c f
        -- Scalar multiplication can be pulled through the summation term by term.
        change ∑' n : ℕ, (((u / (ρ : ℂ)) ^ n) • (c • f n)) = _
        have hf := weightedParameterSummable hu f
        calc
          ∑' n : ℕ, (((u / (ρ : ℂ)) ^ n) • (c • f n))
              = ∑' n : ℕ, c • (((u / (ρ : ℂ)) ^ n) • f n) := by
                  simp [smul_smul, mul_comm]
          _ = c • ∑' n : ℕ, (((u / (ρ : ℂ)) ^ n) • f n) := by
                simpa using (hf.tsum_const_smul c) }
  refine L.mkContinuous 1 ?_
  intro f
  -- The same geometric bound controls the operator norm of the evaluation map by `1`.
  have hp : 0 < ENNReal.toReal (1 : ENNReal) := by
    norm_num
  have hsum := weightedParameterSummable hu f
  have hratio : ‖u / (ρ : ℂ)‖ < 1 := by
    rw [norm_div]
    have hρnorm : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
      simp
    rw [hρnorm]
    have hρpos : 0 < (ρ : ℝ) := lt_of_le_of_lt (norm_nonneg u) hu
    exact (div_lt_one hρpos).2 hu
  have hseries_le :
      ∑' n : ℕ, ‖((u / (ρ : ℂ)) ^ n) • f n‖ ≤ ∑' n : ℕ, ‖f n‖ := by
    refine Summable.tsum_le_tsum ?_ hsum.norm ?_
    · intro n
      rw [norm_smul, norm_pow]
      calc
        ‖u / (ρ : ℂ)‖ ^ n * ‖f n‖ ≤ 1 * ‖f n‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hratio.le
        _ = ‖f n‖ := by
            ring
    · simpa using (lp.memℓp f).summable hp
  calc
    ‖L f‖ = ‖∑' n : ℕ, ((u / (ρ : ℂ)) ^ n) • f n‖ := by
      rfl
    _ ≤ ∑' n : ℕ, ‖((u / (ρ : ℂ)) ^ n) • f n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, ‖f n‖ := hseries_le
    _ ≤ 1 * ‖f‖ := by
      have hsumf : ∑' n : ℕ, ‖f n‖ = ‖f‖ := by
        simpa using
          (lp.hasSum_norm (E := fun _ : ℕ => Fin k → ℂ) (p := (1 : ENNReal)) hp f).tsum_eq
      rw [hsumf]
      simp

/-- Helper for Cartan section28 0001_Theorem_2: the weighted evaluation map sends a basis vector
in the `lp` carrier to the expected geometric multiple. -/
theorem weightedParameterEvalCLM_single
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ) (n : ℕ) (v : Fin k → ℂ) :
    weightedParameterEvalCLM ρ u hu (lp.single 1 n v) = ((u / (ρ : ℂ)) ^ n) • v := by
  -- Only the `n`th coefficient of `lp.single` survives in the defining weighted sum.
  rw [weightedParameterEvalCLM, LinearMap.mkContinuous_apply]
  change ∑' m : ℕ, ((u / (ρ : ℂ)) ^ m) • (lp.single 1 n v) m = ((u / (ρ : ℂ)) ^ n) • v
  have hsingle :
      ∑' m : ℕ, ((u / (ρ : ℂ)) ^ m) • (lp.single (E := fun _ : ℕ => Fin k → ℂ) 1 n v) m =
        ((u / (ρ : ℂ)) ^ n) • (lp.single (E := fun _ : ℕ => Fin k → ℂ) 1 n v) n := by
    refine tsum_eq_single
      (f := fun m : ℕ ↦
        ((u / (ρ : ℂ)) ^ m) • (lp.single (E := fun _ : ℕ => Fin k → ℂ) 1 n v) m)
      n ?_
    intro m hm
    simp [lp.single, hm]
  simpa [lp.single] using hsingle

/-- Helper for Cartan section28 0001_Theorem_2: weighted evaluation sends the canonical
`lp.single` expansion of an `lp` coefficient sequence to the corresponding termwise sum. -/
theorem weightedParameterEvalCLM_hasSum_single
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ) (f : lp (fun _ : ℕ => Fin k → ℂ) 1) :
    HasSum
      (fun n : ℕ ↦ weightedParameterEvalCLM ρ u hu (lp.single 1 n (f n)))
      (weightedParameterEvalCLM ρ u hu f) := by
  -- Expand `f` as the convergent sum of its single-coordinate pieces and map that sum through the
  -- continuous weighted evaluation operator.
  simpa using
    (lp.hasSum_single (E := fun _ : ℕ => Fin k → ℂ) (p := (1 : ENNReal))
      ENNReal.one_ne_top f).mapL (weightedParameterEvalCLM ρ u hu)

/-- Helper for Cartan section28 0001_Theorem_2: for `p = 1`, a raw coefficient row with summable
norms already lies in the weighted `lp` carrier. -/
theorem memℓpOneOfSummableNorm
    {k : ℕ} {f : ℕ → Fin k → ℂ}
    (hf : Summable (fun n : ℕ ↦ ‖f n‖)) :
    Memℓp f 1 := by
  -- At exponent `1`, the `Memℓp` predicate reduces definitionally to summability of the norms.
  rw [Memℓp, if_neg one_ne_zero, if_neg ENNReal.one_ne_top]
  simpa using hf

/-- Helper for Cartan section28 0001_Theorem_2: package a raw summable translated coefficient row
as an element of the Banach carrier `lp (fun _ : ℕ => Fin k → ℂ) 1`. -/
noncomputable def summableNormRowToLp
    {k : ℕ} {f : ℕ → Fin k → ℂ}
    (hf : Summable (fun n : ℕ ↦ ‖f n‖)) :
    lp (fun _ : ℕ => Fin k → ℂ) 1 :=
  ⟨f, memℓpOneOfSummableNorm hf⟩

/-- Helper for Cartan section28 0001_Theorem_2: the `lp` packaging of a summable raw row keeps
the original coefficient sequence unchanged coefficientwise. -/
theorem summableNormRowToLp_apply
    {k : ℕ} {f : ℕ → Fin k → ℂ}
    (hf : Summable (fun n : ℕ ↦ ‖f n‖)) (n : ℕ) :
    summableNormRowToLp hf n = f n := rfl

/-- Helper for Cartan section28 0001_Theorem_2: evaluating the `lp` packaging of a raw summable
row recovers the expected weighted coefficient sum. -/
theorem weightedParameterEvalCLM_summableNormRowToLp
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ) {f : ℕ → Fin k → ℂ}
    (hf : Summable (fun n : ℕ ↦ ‖f n‖)) :
    weightedParameterEvalCLM ρ u hu (summableNormRowToLp hf) =
      ∑' n : ℕ, ((u / (ρ : ℂ)) ^ n) • f n := by
  -- Unfold the evaluation operator and read the packaged row back coefficientwise.
  rw [weightedParameterEvalCLM, LinearMap.mkContinuous_apply]
  simpa [summableNormRowToLp_apply hf]

/-- Helper for Cartan section28 0001_Theorem_2: the `lp.single` expansion of a packaged raw row
evaluates termwise to the same weighted series. -/
theorem weightedParameterEvalCLM_summableNormRowToLp_eq_tsum_single
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ) {f : ℕ → Fin k → ℂ}
    (hf : Summable (fun n : ℕ ↦ ‖f n‖)) :
    weightedParameterEvalCLM ρ u hu (summableNormRowToLp hf) =
      ∑' n : ℕ, weightedParameterEvalCLM ρ u hu (lp.single 1 n (f n)) := by
  -- Re-expand the packaged row through the canonical `lp.single` basis and simplify each term.
  symm
  calc
    ∑' n : ℕ, weightedParameterEvalCLM ρ u hu (lp.single 1 n (f n))
        = ∑' n : ℕ,
            weightedParameterEvalCLM ρ u hu
              (lp.single 1 n ((summableNormRowToLp hf) n)) := by
              simpa [summableNormRowToLp_apply hf]
    _ = weightedParameterEvalCLM ρ u hu (summableNormRowToLp hf) :=
          (weightedParameterEvalCLM_hasSum_single hu (summableNormRowToLp hf)).tsum_eq

/-- Helper for Cartan section28 0001_Theorem_2: the packaged one-variable owner sums to the
expected scalar power series with coefficients `a n`. -/
theorem oneVariableSeriesOfCoefficients_sum_eq_tsum {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a : ℕ → E) (z : ℂ) :
    (oneVariableSeriesOfCoefficients a).sum z = ∑' n : ℕ, z ^ n • a n := by
  -- Expand the formal-series sum and evaluate each `mkPiRing` term on the constant tuple.
  simp [FormalMultilinearSeries.sum, oneVariableSeriesOfCoefficients,
    ContinuousMultilinearMap.mkPiRing_apply]

/-- Helper for Cartan section28 0001_Theorem_2: packaging a coefficient row scaled by `ρ^n`
into `lp` and then evaluating at `u` recovers the corresponding one-variable formal-series sum. -/
theorem weightedParameterEvalCLM_scaledCoeffRow_eq_oneVariableSeriesSum
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hρ : 0 < ρ) (hu : ‖u‖ < ρ)
    {a : ℕ → Fin k → ℂ}
    (ha : Summable (fun n : ℕ ↦ ‖a n‖ * (ρ : ℝ) ^ n)) :
    weightedParameterEvalCLM ρ u hu
      (summableNormRowToLp
        (f := fun n ↦ ((ρ : ℂ) ^ n) • a n)
        (by
          -- The scaled row has the same summability budget as the given scalar majorant.
          refine ha.congr ?_
          intro n
          rw [norm_smul, norm_pow]
          have hρnorm : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
            simp
          rw [hρnorm]
          ring)) =
      (oneVariableSeriesOfCoefficients a).sum u := by
  have hscaled :
      Summable (fun n : ℕ ↦ ‖(((ρ : ℂ) ^ n) • a n)‖) := by
    -- Record the row summability explicitly so both the `lp` packaging and the evaluation rewrite
    -- use the same coefficient data.
    refine ha.congr ?_
    intro n
    rw [norm_smul, norm_pow]
    have hρnorm : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
      simp
    rw [hρnorm]
    ring
  have hρcne : (ρ : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hρ
  -- Expand both sides into the same scalar power series in `u`.
  rw [weightedParameterEvalCLM_summableNormRowToLp hu hscaled]
  rw [oneVariableSeriesOfCoefficients_sum_eq_tsum]
  refine tsum_congr fun n ↦ ?_
  calc
    ((u / (ρ : ℂ)) ^ n) • (((ρ : ℂ) ^ n) • a n)
        = (((u / (ρ : ℂ)) ^ n) * (ρ : ℂ) ^ n) • a n := by
            simp [smul_smul]
    _ = (u ^ n) • a n := by
          congr 1
          calc
            ((u / (ρ : ℂ)) ^ n) * (ρ : ℂ) ^ n
                = ((u * (ρ : ℂ)⁻¹) ^ n) * (ρ : ℂ) ^ n := by
                    simp [div_eq_mul_inv]
            _ = (u ^ n * ((ρ : ℂ)⁻¹) ^ n) * (ρ : ℂ) ^ n := by
                  rw [mul_pow]
            _ = u ^ n * (((ρ : ℂ)⁻¹) ^ n * (ρ : ℂ) ^ n) := by
                  ring
            _ = u ^ n * (((ρ : ℂ)⁻¹ * (ρ : ℂ)) ^ n) := by
                  rw [← mul_pow]
            _ = u ^ n := by
                  simp [hρcne]

/-- Helper for Cartan section28 0001_Theorem_2: a one-variable formal owner can be packaged into
the weighted `lp` carrier on any smaller positive radius, and weighted evaluation then recovers
its original series sum. -/
theorem weightedParameterEvalCLM_packageFormalSeriesCoeff_eq_sum
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hρ : 0 < ρ)
    {P : FormalMultilinearSeries ℂ ℂ (Fin k → ℂ)}
    (hρlt : (ρ : ENNReal) < P.radius)
    (hu : ‖u‖ < ρ) :
    weightedParameterEvalCLM ρ u hu
      (summableNormRowToLp
        (f := fun n ↦ ((ρ : ℂ) ^ n) • P.coeff n)
        (by
          -- The coefficient row inherits summability from the radius bound for `P`.
          have hsumP := P.summable_norm_mul_pow hρlt
          refine hsumP.congr ?_
          intro n
          rw [FormalMultilinearSeries.norm_apply_eq_norm_coef (p := P) (n := n)]
          rw [norm_smul, norm_pow]
          have hρnorm : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
            simp
          rw [hρnorm]
          ring)) =
      P.sum u := by
  have hsumCoeff : Summable (fun n : ℕ ↦ ‖P.coeff n‖ * (ρ : ℝ) ^ n) := by
    -- Rewrite the radius-controlled norm summability from multilinear terms to diagonal
    -- coefficients once, so the packaging theorem can consume the canonical coefficient sequence.
    have hsumP := P.summable_norm_mul_pow hρlt
    refine hsumP.congr ?_
    intro n
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef (p := P) (n := n)]
  have hpack :
      P = oneVariableSeriesOfCoefficients (fun n ↦ P.coeff n) :=
    formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients P
  -- Package the diagonal coefficient sequence and then identify the resulting one-variable owner
  -- with the original formal series.
  calc
    weightedParameterEvalCLM ρ u hu
        (summableNormRowToLp
          (f := fun n ↦ ((ρ : ℂ) ^ n) • P.coeff n)
          (by
            have hsumP := P.summable_norm_mul_pow hρlt
            refine hsumP.congr ?_
            intro n
            rw [FormalMultilinearSeries.norm_apply_eq_norm_coef (p := P) (n := n)]
            rw [norm_smul, norm_pow]
            have hρnorm : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
              simp
            rw [hρnorm]
            ring))
        = (oneVariableSeriesOfCoefficients fun n ↦ P.coeff n).sum u :=
          weightedParameterEvalCLM_scaledCoeffRow_eq_oneVariableSeriesSum
            (k := k) (ρ := ρ) (u := u) hρ hu hsumCoeff
    _ = P.sum u := by
          rw [← hpack]

/-- Helper for Cartan section28 0001_Theorem_2: for a fixed weighted `lp` coefficient sequence,
the corresponding weighted evaluation series is analytic on the radius-`ρ` ball. -/
theorem weightedParameterEvalSeries_hasFPowerSeriesOnBall
    {k : ℕ} {ρ : NNReal} (hρ : 0 < ρ)
    (f : lp (fun _ : ℕ => Fin k → ℂ) 1) :
    HasFPowerSeriesOnBall
      (fun u : ℂ ↦ ∑' n : ℕ, ((u / (ρ : ℂ)) ^ n) • f n)
      (oneVariableSeriesOfCoefficients fun n ↦ ((ρ : ℂ)⁻¹ ^ n) • f n)
      0 ρ := by
  let p : FormalMultilinearSeries ℂ ℂ (Fin k → ℂ) :=
    oneVariableSeriesOfCoefficients fun n ↦ ((ρ : ℂ)⁻¹ ^ n) • f n
  have hp : 0 < ENNReal.toReal (1 : ENNReal) := by
    norm_num
  have hsumf : Summable (fun n : ℕ ↦ ‖f n‖) := by
    -- The weighted carrier uses `p = 1`, so the norm row is summable.
    simpa using (lp.memℓp f).summable hp
  have hρne : (ρ : ℝ) ≠ 0 := ne_of_gt hρ
  have hρcne : (ρ : ℂ) ≠ 0 := by
    exact_mod_cast hρne
  have hpSummable :
      Summable (fun n : ℕ ↦ ‖p n‖ * (ρ : ℝ) ^ n) := by
    -- On the radius-`ρ` ball, the packaged coefficients have exactly the original `lp` norm
    -- budget because the factors `ρ⁻n` and `ρ^n` cancel.
    refine hsumf.congr ?_
    intro n
    dsimp [p]
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef (p := p) (n := n)]
    rw [oneVariableSeriesOfCoefficients_coeff]
    rw [norm_smul, norm_pow]
    have hnormInv : ‖((ρ : ℂ)⁻¹)‖ = (ρ : ℝ)⁻¹ := by
      simp
    have hcancel : ((ρ : ℝ)⁻¹ * (ρ : ℝ)) = 1 := by
      field_simp [hρne]
    rw [hnormInv]
    symm
    calc
      (((ρ : ℝ)⁻¹ ^ n) * ‖f n‖) * (ρ : ℝ) ^ n
          = ‖f n‖ * ((((ρ : ℝ)⁻¹) ^ n) * (ρ : ℝ) ^ n) := by ring
      _ = ‖f n‖ * ((((ρ : ℝ)⁻¹) * (ρ : ℝ)) ^ n) := by rw [← mul_pow]
      _ = ‖f n‖ := by simp [hcancel]
  have hρle : (ρ : ENNReal) ≤ p.radius := by
    exact FormalMultilinearSeries.le_radius_of_summable_norm (p := p) (r := ρ) hpSummable
  have hpRad : 0 < p.radius := by
    exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hρ) hρle
  have hpBall : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall hpRad
  refine (hpBall.mono (by simpa [ENNReal.coe_pos] using hρ) hρle).congr ?_
  intro u hu
  -- Rewrite the packaged formal-series sum into the explicit weighted evaluation series.
  rw [oneVariableSeriesOfCoefficients_sum_eq_tsum]
  refine tsum_congr fun n ↦ ?_
  calc
    u ^ n • (((ρ : ℂ)⁻¹ ^ n) • f n)
        = (u ^ n * ((ρ : ℂ)⁻¹ ^ n)) • f n := by simp [smul_smul]
    _ = ((u / (ρ : ℂ)) ^ n) • f n := by
          congr 1
          simp [div_eq_mul_inv, mul_pow]

/-- Helper for Cartan section28 0001_Theorem_2: fixing the translated parameter and postcomposing
an analytic Banach-valued curve by the weighted evaluation map preserves analyticity in `x`. -/
theorem analyticOnNhd_weightedParameterEvalCLM_of_curve
    {k : ℕ} {ρ : NNReal} {u : ℂ}
    (hu : ‖u‖ < ρ)
    {Bx : Set ℂ} {Ψ : ℂ → lp (fun _ : ℕ => Fin k → ℂ) 1}
    (hΨ : AnalyticOnNhd ℂ Ψ Bx) :
    AnalyticOnNhd ℂ (fun x ↦ weightedParameterEvalCLM ρ u hu (Ψ x)) Bx := by
  intro x hx
  -- Freeze the parameter and compose the analytic Banach curve with the continuous linear
  -- evaluation operator.
  exact ((weightedParameterEvalCLM ρ u hu).analyticAt (Ψ x)).comp (hΨ x hx)

/-- Helper for Cartan section28 0001_Theorem_2: postcomposing a one-variable formal series by a
continuous linear map acts coefficientwise. -/
theorem compFormalMultilinearSeries_coeff_apply {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : F →L[ℂ] G) (P : FormalMultilinearSeries ℂ ℂ F) (m : ℕ) :
    (L.compFormalMultilinearSeries P).coeff m = L (P.coeff m) := by
  -- Read the degree-`m` coefficient by evaluating the multilinear term on the constant tuple
  -- `1`; postcomposition by `L` commutes with that evaluation.
  rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe]
  rfl

/-- Helper for Cartan section28 0001_Theorem_2: postcomposing a packaged one-variable Banach
owner by a continuous linear map acts coefficientwise on its stored sequence. -/
theorem oneVariableSeriesOfCoefficients_compFormalMultilinearSeries
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (a : ℕ → E) :
    L.compFormalMultilinearSeries (oneVariableSeriesOfCoefficients a) =
      oneVariableSeriesOfCoefficients (fun m ↦ L (a m)) := by
  -- In one complex variable, postcomposition is determined by the diagonal coefficient sequence.
  calc
    L.compFormalMultilinearSeries (oneVariableSeriesOfCoefficients a)
        = oneVariableSeriesOfCoefficients
            (fun m ↦
              (L.compFormalMultilinearSeries (oneVariableSeriesOfCoefficients a)).coeff m) := by
              symm
              exact
                (formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients
                  (P := L.compFormalMultilinearSeries (oneVariableSeriesOfCoefficients a))).symm
    _ = oneVariableSeriesOfCoefficients (fun m ↦ L (a m)) := by
          congr
          funext m
          rw [compFormalMultilinearSeries_coeff_apply, oneVariableSeriesOfCoefficients_coeff]

/-- Helper for Cartan section28 0001_Theorem_2: postcomposing the recentered Banach curve owner by
`id × L` simply applies `L` to the Banach coefficient sequence. -/
theorem recenteredCurveSeriesBanach_comp_prodMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (a : ℕ → E) :
    ((ContinuousLinearMap.id ℂ ℂ).prodMap L).compFormalMultilinearSeries
        (recenteredCurveSeriesBanach a) =
      recenteredCurveSeriesBanach (fun m ↦ L (a m)) := by
  -- First split the postcomposition by `id × L` into its two componentwise postcompositions, then
  -- rewrite the Banach factor using the coefficientwise transport lemma.
  calc
    ((ContinuousLinearMap.id ℂ ℂ).prodMap L).compFormalMultilinearSeries
        (recenteredCurveSeriesBanach a)
        = (((ContinuousLinearMap.id ℂ ℂ).compFormalMultilinearSeries
            (oneVariableSeriesOfCoefficients identitySeriesCoeff)).prod
          (L.compFormalMultilinearSeries (oneVariableSeriesOfCoefficients a))) := by
            rfl
    _ = (((ContinuousLinearMap.id ℂ ℂ).compFormalMultilinearSeries
            (oneVariableSeriesOfCoefficients identitySeriesCoeff)).prod
          (oneVariableSeriesOfCoefficients (fun m ↦ L (a m)))) := by
            congr 1
            exact oneVariableSeriesOfCoefficients_compFormalMultilinearSeries (L := L) (a := a)
    _ = (oneVariableSeriesOfCoefficients identitySeriesCoeff).prod
          (oneVariableSeriesOfCoefficients (fun m ↦ L (a m))) := by
            simpa using
              congrArg
                (fun P ↦ P.prod (oneVariableSeriesOfCoefficients (fun m ↦ L (a m))))
                (oneVariableSeriesOfCoefficients_compFormalMultilinearSeries
                  (L := ContinuousLinearMap.id ℂ ℂ) (a := identitySeriesCoeff))
    _ = recenteredCurveSeriesBanach (fun m ↦ L (a m)) := by
          rfl

/-- Helper for Cartan section28 0001_Theorem_2: the scalar one-variable owner packaged by
`oneVariableSeriesOfCoefficients` agrees with the standard `ofScalars` owner. -/
theorem oneVariableSeriesOfCoefficients_eq_ofScalars
    (a : ℕ → ℂ) :
    oneVariableSeriesOfCoefficients a = FormalMultilinearSeries.ofScalars ℂ a := by
  -- In one complex variable, both packages store the same diagonal coefficient sequence.
  have hpack :
      oneVariableSeriesOfCoefficients a =
        oneVariableSeriesOfCoefficients
          (fun m ↦ (oneVariableSeriesOfCoefficients a).coeff m) :=
    formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients
      (P := oneVariableSeriesOfCoefficients a)
  calc
    oneVariableSeriesOfCoefficients a
        = oneVariableSeriesOfCoefficients
            (fun m ↦ (oneVariableSeriesOfCoefficients a).coeff m) := hpack
    _ = oneVariableSeriesOfCoefficients
          (fun m ↦ (FormalMultilinearSeries.ofScalars ℂ a).coeff m) := by
              congr
              funext m
              rw [oneVariableSeriesOfCoefficients_coeff, FormalMultilinearSeries.coeff_ofScalars]
    _ = FormalMultilinearSeries.ofScalars ℂ a := by
          exact
            (formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients
              (P := FormalMultilinearSeries.ofScalars ℂ a)).symm

/-- Helper for Cartan section28 0001_Theorem_2: the local identity-coefficient package matches the
section-27 recentered `X`-coefficient sequence. -/
theorem identitySeriesCoeff_eq_recenteredXCoeff
    (m : ℕ) :
    identitySeriesCoeff m = recenteredXCoeff m := by
  -- Both definitions encode the identity map `z ↦ z` as the same degree-`1` coefficient data.
  cases m with
  | zero =>
      rfl
  | succ m =>
      cases m with
      | zero =>
          rfl
      | succ m =>
          rfl

/-- Helper for Cartan section28 0001_Theorem_2: for vector-valued scalar coefficients, the local
one-variable package agrees with the section-27 coordinatewise owner. -/
theorem oneVariableSeriesOfCoefficients_eq_vectorOfScalarsSeries
    {k : ℕ} (a : ℕ → Fin k → ℂ) :
    oneVariableSeriesOfCoefficients a = vectorOfScalarsSeries a := by
  -- Both one-variable owners are determined by the same diagonal coefficient sequence.
  calc
    oneVariableSeriesOfCoefficients a
        = oneVariableSeriesOfCoefficients (fun m ↦ (vectorOfScalarsSeries a).coeff m) := by
            congr
            funext m
            rw [vectorOfScalarsSeries_coeff]
    _ = vectorOfScalarsSeries a := by
          exact
            (formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients
              (P := vectorOfScalarsSeries a)).symm

/-- Helper for Cartan section28 0001_Theorem_2: specializing the Banach recentered curve package
to finite-dimensional vector coefficients recovers the section-27 recentered curve owner. -/
theorem recenteredCurveSeriesBanach_eq_recenteredCurveSeries
    {k : ℕ} (a : ℕ → Fin k → ℂ) :
    recenteredCurveSeriesBanach a = recenteredCurveSeries a := by
  -- Normalize the scalar and vector coefficient packages to the canonical section-27 spellings.
  have hId :
      FormalMultilinearSeries.ofScalars ℂ identitySeriesCoeff =
        FormalMultilinearSeries.ofScalars ℂ recenteredXCoeff := by
    have hIdCoeff : identitySeriesCoeff = recenteredXCoeff := by
      funext m
      exact identitySeriesCoeff_eq_recenteredXCoeff m
    calc
      FormalMultilinearSeries.ofScalars ℂ identitySeriesCoeff
          = oneVariableSeriesOfCoefficients identitySeriesCoeff := by
              exact (oneVariableSeriesOfCoefficients_eq_ofScalars (a := identitySeriesCoeff)).symm
      _ = oneVariableSeriesOfCoefficients recenteredXCoeff := by
            exact congrArg oneVariableSeriesOfCoefficients hIdCoeff
      _ = FormalMultilinearSeries.ofScalars ℂ recenteredXCoeff := by
            exact oneVariableSeriesOfCoefficients_eq_ofScalars (a := recenteredXCoeff)
  unfold recenteredCurveSeriesBanach recenteredCurveSeries
  rw [oneVariableSeriesOfCoefficients_eq_vectorOfScalarsSeries]
  rw [oneVariableSeriesOfCoefficients_eq_ofScalars]
  simpa using congrArg (fun P ↦ P.prod (vectorOfScalarsSeries a)) hId

/-- Helper for Cartan section28 0001_Theorem_2: after normalizing the one-variable curve package,
the Banach recentered composition coefficient agrees with the section-27 scalar coefficient. -/
theorem recenteredComposedCoeffBanach_eq_recenteredComposedCoeff
    {k : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin k → ℂ)) (Fin k → ℂ))
    (a : ℕ → Fin k → ℂ) (m : ℕ) :
    recenteredComposedCoeffBanach Q a m = recenteredComposedCoeff Q a m := by
  -- The only mismatch is the local spelling of the recentered curve owner.
  unfold recenteredComposedCoeffBanach recenteredComposedCoeff
  rw [recenteredCurveSeriesBanach_eq_recenteredCurveSeries]

/-- Helper for Cartan section28 0001_Theorem_2: after transporting the Banach coefficient sequence
through `L`, the recentered composition coefficients can be computed against the normalized
recentered curve without any further transport bookkeeping. -/
theorem recenteredComposedCoeffBanach_comp_prodMap
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : E →L[ℂ] F) (Q : FormalMultilinearSeries ℂ (ℂ × F) G) (a : ℕ → E) (m : ℕ) :
    (Q.comp (((ContinuousLinearMap.id ℂ ℂ).prodMap L).compFormalMultilinearSeries
        (recenteredCurveSeriesBanach a))).coeff m =
      (Q.comp (recenteredCurveSeriesBanach (fun n ↦ L (a n)))).coeff m := by
  -- Normalize the inner recentered curve once; afterwards the coefficient identity is definitional.
  rw [recenteredCurveSeriesBanach_comp_prodMap]

/-- Helper for Cartan section28 0001_Theorem_2: the exact Banach-valued coefficient recursion
forces the formal derivative owner to match the recentered composition owner. -/
theorem recenteredFormalDerivativeOwner_eq_banach {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Q : FormalMultilinearSeries ℂ (ℂ × E) E}
    {P : FormalMultilinearSeries ℂ ℂ E}
    (hP :
      P.coeff 0 = 0 ∧
        ∀ m, P.coeff (m + 1) =
          ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m) :
    ((ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries P.derivSeries)
      =
      Q.comp (recenteredCurveSeriesBanach fun m ↦ P.coeff m) := by
  have hcoeff :
      ∀ m,
        (((ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries P.derivSeries).coeff
            m) =
          (Q.comp (recenteredCurveSeriesBanach fun k ↦ P.coeff k)).coeff m := by
    intro m
    have hscaled :
        (m + 1 : ℂ) • P.coeff (m + 1) =
          recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m := by
      -- Rewrite the recursive coefficient identity and cancel the scalar factor.
      calc
        (m + 1 : ℂ) • P.coeff (m + 1)
            = (m + 1 : ℂ) •
                (((m + 1 : ℂ)⁻¹) •
                  recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m) := by
                  rw [hP.2 m]
        _ = (((m + 1 : ℂ) * (m + 1 : ℂ)⁻¹) •
              recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m) := by
                simp [smul_smul]
        _ = recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m := by
              have hmul : (m + 1 : ℂ) * (m + 1 : ℂ)⁻¹ = 1 := by
                field_simp [Nat.succ_ne_zero m]
              simp [hmul]
    -- Compare the degree-`m` coefficients on the two owners.
    calc
      (((ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries P.derivSeries).coeff
          m)
          = (m + 1 : ℂ) • P.coeff (m + 1) := by
              rw [compFormalMultilinearSeries_coeff_apply]
              change (P.derivSeries.coeff m) 1 = _
              rw [FormalMultilinearSeries.derivSeries_coeff_one]
              simpa [Nat.cast_add, Nat.cast_one] using
                (Nat.cast_smul_eq_nsmul ℂ (m + 1) (P.coeff (m + 1))).symm
      _ = recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m := hscaled
      _ = (Q.comp (recenteredCurveSeriesBanach fun k ↦ P.coeff k)).coeff m := by
            rfl
  -- In one complex variable, the coefficient sequence determines the whole owner.
  calc
    ((ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries P.derivSeries)
        =
          oneVariableSeriesOfCoefficients
            (fun m ↦
              (((ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries
                  P.derivSeries).coeff m)) :=
      formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients _
    _ =
          oneVariableSeriesOfCoefficients
            (fun m ↦ (Q.comp (recenteredCurveSeriesBanach fun k ↦ P.coeff k)).coeff m) := by
          congr
          funext m
          exact hcoeff m
    _ = Q.comp (recenteredCurveSeriesBanach fun m ↦ P.coeff m) := by
          symm
          exact formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients _
