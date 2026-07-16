import Mathlib
import DifferentialForms_Cartan_1970.cartan.V.section19.«0002_Theorem_V_2_extra_2»
import DifferentialForms_Cartan_1970.cartan.V.section20.«0003_Theorem_1»
import DifferentialForms_Cartan_1970.cartan.V.section20.«0002_Definition_V_3_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology

-- Domain sampling: this file is source-facing in the holomorphic infinite-product /
-- logarithmic-derivative domain.
-- The chapter owner for the product hypothesis is `NormallyMultipliableOnCompacta`; the canonical
-- mathlib owners used by these statements are `AnalyticOnNhd`, `logDeriv`, and
-- `logDeriv_tprod_eq_tsum`.
-- Primitive data: the factor family `f`, its holomorphy on `D`, and compact-normal
-- multipliability on `D`.
-- Derived API: analytic logarithmic-derivative tails on compacta and the pointwise sum formula.

section

variable {D : Set ℂ} {f : ℕ → ℂ → ℂ}

/-- Helper for Theorem 2: if a holomorphic function maps a set into the slit plane, then its
principal logarithm is analytic on a neighborhood of that set. -/
lemma clog_comp_analyticOnNhd_of_mapsTo_slit
    {K : Set ℂ} {g : ℂ → ℂ} (hD : IsOpen D) (hg : DifferentiableOn ℂ g D) (hKD : K ⊆ D)
    (hslit : Set.MapsTo g K Complex.slitPlane) :
    AnalyticOnNhd ℂ (fun z ↦ Complex.log (g z)) K := by
  -- Holomorphy on the open domain gives analyticity at each point of `K`, and the slit-plane
  -- hypothesis lets us compose with the principal logarithm.
  intro z hz
  exact (hg.analyticAt (hD.mem_nhds (hKD hz))).clog (hslit hz)

/-- Helper for Theorem 2: on a set where a holomorphic function stays in the slit plane, its
logarithmic derivative is analytic on a neighborhood of that set. -/
lemma logDeriv_analyticOnNhd_of_mapsTo_slit
    {K : Set ℂ} {g : ℂ → ℂ} (hD : IsOpen D) (hg : DifferentiableOn ℂ g D) (hKD : K ⊆ D)
    (hslit : Set.MapsTo g K Complex.slitPlane) :
    AnalyticOnNhd ℂ (logDeriv g) K := by
  -- Differentiate `log ∘ g`, then identify that derivative locally with `logDeriv g`.
  intro z hz
  have hg_analytic : AnalyticAt ℂ g z := hg.analyticAt (hD.mem_nhds (hKD hz))
  have hlog_analytic : AnalyticAt ℂ (fun w ↦ Complex.log (g w)) z :=
    hg_analytic.clog (hslit hz)
  have hEq :
      deriv (fun w ↦ Complex.log (g w)) =ᶠ[𝓝 z] logDeriv g := by
    filter_upwards
      [hD.mem_nhds (hKD hz), hg_analytic.continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds (hslit hz))] with
      w hwD hwslit
    exact Complex.deriv_log_comp_eq_logDeriv
      ((hg w hwD).differentiableAt (hD.mem_nhds hwD)) hwslit
  exact (hlog_analytic.deriv).congr hEq

/-- Theorem 2 (1): with the hypotheses of theorem 1, on every compact subset of `D` there is a
tail of the logarithmic-derivative series whose terms are analytic on a neighborhood of the
subset. -/
theorem logDeriv_series_tail_analytic_on_compact_subsets
    (hf : ∀ n, DifferentiableOn ℂ (f n) D) (hnorm : NormallyMultipliableOnCompacta f D)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ, ∀ n, AnalyticOnNhd ℂ (logDeriv (f (n + N))) K := by
  let hD : IsOpen D := hnorm.isOpen_domain
  let hfixed : NormallyMultipliableOn f D K := hnorm hK hKD
  -- The source proof starts by taking a tail on which every factor admits a principal logarithm.
  rcases hfixed.exists_slit_log_tail with ⟨N, hslit, _hlog⟩
  refine ⟨N, ?_⟩
  intro n
  -- On that tail, the logarithmic derivative is the derivative of `log ∘ f`, hence analytic.
  exact logDeriv_analyticOnNhd_of_mapsTo_slit (D := D) hD (hf (n + N)) hKD (hslit n)

/-- Theorem 2 (2): with the hypotheses of theorem 1, on every compact subset of `D` there is a
tail of the logarithmic-derivative series that is normally summable there. -/
theorem logDeriv_series_tail_summably_bounded_on_compact_subsets
    (hf : ∀ n, DifferentiableOn ℂ (f n) D) (hnorm : NormallyMultipliableOnCompacta f D)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ, NormallySummableOn (fun n z ↦ logDeriv (f (n + N)) z) K := by
  let hD : IsOpen D := hnorm.isOpen_domain
  -- Following the source proof, enlarge `K` to a compact thickening still contained in `D`.
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hD hKD
  let hthick : NormallyMultipliableOn f D (Metric.cthickening δ K) :=
    hnorm hK.cthickening hKδ
  rcases hthick.exists_slit_log_tail with ⟨N, hslit, hlog⟩
  rcases hlog with ⟨a, ha, hbound⟩
  have hanalytic :
      ∀ n, AnalyticOnNhd ℂ (fun z ↦ Complex.log (f (n + N) z)) (Metric.cthickening δ K) := by
    intro n
    -- The logarithm tail is analytic on the thickening because the factors stay in the slit plane.
    exact clog_comp_analyticOnNhd_of_mapsTo_slit (D := D) hD (hf (n + N)) hKδ (hslit n)
  obtain ⟨c, hc⟩ :=
    deriv_tail_majorized_on_compact_of_normal_tail_bound (K := K) (ε := δ) hδ hanalytic hbound
  refine ⟨N, ?_⟩
  refine ⟨fun n ↦ a n * c, ?_, ?_⟩
  · -- Scale the normal majorant for the logarithm tail by the Cauchy-estimate constant.
    exact NNReal.summable_coe.2 ((NNReal.summable_coe.1 ha).mul_right c)
  · intro n z hz
    -- Rewrite the derivative of the logarithm back to the logarithmic derivative of the factor.
    have hzD : z ∈ D := hKD hz
    have hzthick : z ∈ Metric.cthickening δ K := Metric.self_subset_cthickening K hz
    have hderiv_eq :
        deriv (fun w ↦ Complex.log (f (n + N) w)) z = logDeriv (f (n + N)) z :=
      Complex.deriv_log_comp_eq_logDeriv
        ((hf (n + N) z hzD).differentiableAt (hD.mem_nhds hzD))
        (hslit n hzthick)
    simpa [hderiv_eq] using hc n z hz

/-- Theorem 2 (3): at a point of `D` where no factor vanishes, the normally convergent series of
logarithmic derivatives sums to the logarithmic derivative of the infinite product. -/
theorem hasSum_logDeriv_tprod_at_nonvanishing_point
    (hf : ∀ n, DifferentiableOn ℂ (f n) D) (hnorm : NormallyMultipliableOnCompacta f D)
    {z : ℂ} (hz : z ∈ D) (hzero : ∀ n, f n z ≠ 0) :
    HasSum (fun n ↦ logDeriv (f n) z) (logDeriv (fun w : ℂ ↦ ∏' n, f n w) z) := by
  let hD : IsOpen D := hnorm.isOpen_domain
  -- First specialize the compact-normal bound to the singleton `{z}` to get a summable tail.
  rcases
      logDeriv_series_tail_summably_bounded_on_compact_subsets
        (D := D) (f := f) hf hnorm (K := ({z} : Set ℂ)) isCompact_singleton
        (Set.singleton_subset_iff.mpr hz) with
    ⟨N, htail⟩
  have hsummable_tail : Summable (fun n ↦ logDeriv (f (n + N)) z) := by
    rcases htail with ⟨a, ha, hbound⟩
    exact Summable.of_norm_bounded (g := fun n ↦ (a n : ℝ)) ha fun n ↦ hbound n z (by simp)
  have hsummable : Summable (fun n ↦ logDeriv (f n) z) :=
    (summable_nat_add_iff N).1 hsummable_tail
  -- The infinite product is nonzero because both the finite prefix and the nonvanishing tail are.
  rcases exists_nonvanishing_pointwise_tail_of_normallyMultipliableOnCompacta hnorm hz with
    ⟨M, htail_nonzero, htail_prod_nonzero⟩
  have hprefix_nonzero :
      (Finset.range M).prod (fun i ↦ f i z) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hzero i
  have htprod_nonzero : (∏' n, f n z) ≠ 0 := by
    rw [tprod_eq_prod_range_mul_tprod_nat_add_of_mem hnorm hz M]
    exact mul_ne_zero hprefix_nonzero htail_prod_nonzero
  have hsum_eq :
      logDeriv (fun w : ℂ ↦ ∏' n, f n w) z = ∑' n, logDeriv (f n) z :=
    logDeriv_tprod_eq_tsum hD hz hzero hf hsummable
      (hnorm.hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn) htprod_nonzero
  -- The source identity `f' / f = Σ f_n' / f_n` is now exactly mathlib's tprod formula.
  rw [hsum_eq]
  exact hsummable.hasSum

end
