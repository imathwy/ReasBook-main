import Mathlib
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import cartan.V.section20.«0002_Definition_V_3_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Complex Topology

-- Domain sampling: this file is source-facing in the complex infinite-product domain.
-- The chapter owner for the compact-normal convergence hypothesis is
-- `NormallyMultipliableOnCompacta`; the core/canonical owners used below are
-- `HasProdLocallyUniformlyOn.differentiableOn`,
-- `NormallyMultipliableOnCompacta.multipliable`,
-- `Multipliable.prod_mul_tprod_nat_add`, and `analyticOrderAt`.
-- Primitive data: the factor family `f` and the compact-normal product hypothesis on `D`.
-- Derived API: the local `tprod` splitting and holomorphy consequences.

section

variable {D : Set ℂ} {f : ℕ → ℂ → ℂ}

/-- Helper for Theorem 1: a finite product of functions analytic at `z` is itself analytic at
`z`. -/
lemma analyticAt_finsetProd {ι : Type*} {s : Finset ι} {g : ι → ℂ → ℂ} {z : ℂ}
    (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) z) :
    AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, g i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty product is the constant function `1`.
      simpa using (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z))
  | @insert a s ha ih =>
      -- Peel off the leading factor and apply multiplicativity of analyticity.
      have hga : AnalyticAt ℂ (g a) z := hg a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, AnalyticAt ℂ (g i) z := fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
      simpa [Finset.prod_insert ha] using hga.mul (ih hgs)

/-- Helper for Theorem 1: shifting the index of a normally summable series preserves normal
summability on the same compact set. -/
lemma NormallySummableOn.nat_add {u : ℕ → ℂ → ℂ} {K : Set ℂ} (N : ℕ)
    (h : NormallySummableOn u K) :
    NormallySummableOn (fun n z ↦ u (n + N) z) K := by
  rcases h with ⟨a, ha, hbound⟩
  refine ⟨fun n ↦ a (n + N), ?_, ?_⟩
  · exact (summable_nat_add_iff N).2 ha
  · intro n z hz
    exact hbound (n + N) z hz

/-- Helper for Theorem 1: the analytic order of a finite product is the sum of the analytic
orders of its factors. -/
lemma analyticOrderAt_finsetProd_eq_sum {ι : Type*} {s : Finset ι} {g : ι → ℂ → ℂ} {z : ℂ}
    (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) z) :
    analyticOrderAt (fun w ↦ ∏ i ∈ s, g i w) z = ∑ i ∈ s, analyticOrderAt (g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty product is constantly `1`, so its vanishing order is `0`.
      simp [analyticOrderAt_eq_zero]
  | @insert a s ha ih =>
      -- Split off one factor and use additivity of analytic order under multiplication.
      have hga : AnalyticAt ℂ (g a) z := hg a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, AnalyticAt ℂ (g i) z := fun i hi ↦ hg i (Finset.mem_insert_of_mem hi)
      have hprod : AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, g i w) z := analyticAt_finsetProd hgs
      have hsum :
          analyticOrderAt (fun w ↦ ∏ i ∈ s, g i w) z =
            ∑ i ∈ s, analyticOrderAt (g i) z :=
        ih hgs
      calc
        analyticOrderAt (fun w ↦ ∏ i ∈ insert a s, g i w) z
            = analyticOrderAt (g a) z +
                analyticOrderAt (fun w ↦ ∏ i ∈ s, g i w) z := by
                  simpa [Finset.prod_insert ha] using analyticOrderAt_mul hga hprod
        _ = analyticOrderAt (g a) z + ∑ i ∈ s, analyticOrderAt (g i) z := by
              rw [hsum]
        _ = ∑ i ∈ insert a s, analyticOrderAt (g i) z := by
              simp [Finset.sum_insert, ha]

/-- Helper for Theorem 1: at any point of the domain, one can discard a finite prefix so that the
remaining factors are all nonzero at that point and their tail product is nonzero. -/
lemma exists_nonvanishing_pointwise_tail_of_normallyMultipliableOnCompacta
    (hnorm : NormallyMultipliableOnCompacta f D) {z : ℂ} (hz : z ∈ D) :
    ∃ N, (∀ n, f (n + N) z ≠ 0) ∧ (∏' n, f (n + N) z) ≠ 0 := by
  have hsingleton_subset : ({z} : Set ℂ) ⊆ D := by
    intro w hw
    simpa [Set.mem_singleton_iff.mp hw] using hz
  let hsingleton : NormallyMultipliableOn f D ({z} : Set ℂ) :=
    hnorm isCompact_singleton hsingleton_subset
  rcases hsingleton.exists_slit_log_tail with ⟨N, hslit, hlog⟩
  have hz_singleton : z ∈ ({z} : Set ℂ) := by
    simp
  have hnonzero : ∀ n, f (n + N) z ≠ 0 := fun n ↦
    Complex.slitPlane_ne_zero (hslit n hz_singleton)
  have hhasSum :
      HasSum (fun n ↦ Complex.log (f (n + N) z))
        (∑' n, Complex.log (f (n + N) z)) :=
    hlog.hasSumUniformlyOn.hasSum hz_singleton
  have htprod :
      cexp (∑' n, Complex.log (f (n + N) z)) = ∏' n, f (n + N) z :=
    Complex.cexp_tsum_eq_tprod hnonzero hhasSum.summable
  refine ⟨N, hnonzero, ?_⟩
  rw [← htprod]
  exact Complex.exp_ne_zero _

/-- Helper for Theorem 1: shifting the index of a compact-normally convergent product preserves
compact-normal convergence on the same domain. -/
lemma normallyMultipliableOnCompacta_nat_add (N : ℕ)
    (hnorm : NormallyMultipliableOnCompacta f D) :
    NormallyMultipliableOnCompacta (fun n z ↦ f (n + N) z) D := by
  intro K hK hKD
  let hfixed : NormallyMultipliableOn f D K := hnorm hK hKD
  rcases hfixed with ⟨hopen, hsubset, hcont, htail⟩
  rcases htail with ⟨M, hslit, hlog⟩
  refine ⟨hopen, hsubset, ?_, ?_⟩
  · intro n
    simpa [Nat.add_assoc] using hcont (n + N)
  · refine ⟨M, ?_, ?_⟩
    · intro n
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hslit (n + N)
    · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlog.nat_add N

/-- Theorem 1 (1): if the holomorphic factors `f n` have an infinite product converging normally on
compact subsets of `D`, then the limit function `z ↦ ∏' n, f n z` is holomorphic on `D`. -/
theorem differentiableOn_tprod_of_normallyMultipliableOnCompacta
    (hD : IsOpen D) (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hnorm : NormallyMultipliableOnCompacta f D) :
    DifferentiableOn ℂ (fun z ↦ ∏' n, f n z) D := by
  -- The finite partial products are holomorphic, and they converge locally uniformly on `D`.
  refine hnorm.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange.differentiableOn
    (Filter.Eventually.of_forall fun N ↦ ?_) hD
  simpa [Finset.prod_fn] using
    (DifferentiableOn.finsetProd (u := Finset.range N) fun n _ ↦ hf n)

/-- Theorem 1 (2): at each point `z ∈ D`, the infinite product splits into its first `p` factors
times the tail product. -/
theorem tprod_eq_prod_range_mul_tprod_nat_add_of_mem
    (hnorm : NormallyMultipliableOnCompacta f D) {z : ℂ} (hz : z ∈ D) (p : ℕ) :
    (∏' n, f n z) = (Finset.range p).prod (fun i ↦ f i z) * ∏' n, f (n + p) z := by
  -- Pointwise multipliability gives the standard finite-prefix / infinite-tail split.
  let g : ℕ → ℂ → ℂ := fun n w ↦ f (n + p) w
  have hshift : NormallyMultipliableOnCompacta g D :=
    normallyMultipliableOnCompacta_nat_add p hnorm
  have htail :
      HasProd (fun n ↦ g n z) (∏' n, g n z) :=
    hshift.hasProd hz
  have hfull :
      HasProd (fun n ↦ f n z) ((Finset.range p).prod (fun i ↦ f i z) * ∏' n, g n z) :=
    htail.prod_range_mul
  simpa [g] using hfull.tprod_eq

/-- Under compact-normal convergence, only finitely many factors can vanish at a fixed point of
`D`. -/
theorem zero_factor_indices_finite_of_normallyMultipliableOnCompacta
    (hnorm : NormallyMultipliableOnCompacta f D) {z : ℂ} (hz : z ∈ D) :
    {n : ℕ | f n z = 0}.Finite := by
  rcases exists_nonvanishing_pointwise_tail_of_normallyMultipliableOnCompacta hnorm hz with
    ⟨N, htail, _⟩
  -- Any zero factor must occur before the nonvanishing tail begins.
  refine (Set.finite_lt_nat N).subset ?_
  intro n hzero
  by_contra hnlt
  have hNn : N ≤ n := Nat.not_lt.mp hnlt
  have hzero_tail : f (n - N + N) z = 0 := by
    simpa [Nat.sub_add_cancel hNn] using hzero
  exact htail (n - N) hzero_tail

/-- Theorem 1 (3): on `D`, the zero set of the product function is the union of the zero sets of
its factors. -/
theorem zeroSet_tprod_eq_iUnion_zeroSet_of_normallyMultipliableOnCompacta
    (hnorm : NormallyMultipliableOnCompacta f D) :
    D ∩ (fun z : ℂ ↦ ∏' n, f n z) ⁻¹' {0} = ⋃ n : ℕ, D ∩ (f n) ⁻¹' {0} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hz, hzprod⟩
    rcases exists_nonvanishing_pointwise_tail_of_normallyMultipliableOnCompacta hnorm hz with
      ⟨N, _, htailprod⟩
    have hsplit := tprod_eq_prod_range_mul_tprod_nat_add_of_mem hnorm hz N
    have hprefix_zero :
        (Finset.range N).prod (fun i ↦ f i z) = 0 := by
      have hmul_zero :
          (Finset.range N).prod (fun i ↦ f i z) * ∏' n, f (n + N) z = 0 := by
        simpa [hsplit] using hzprod
      exact (mul_eq_zero.mp hmul_zero).resolve_right htailprod
    rcases Finset.prod_eq_zero_iff.mp hprefix_zero with ⟨n, hn, hnzero⟩
    exact ⟨n, hz, hnzero⟩
  · rintro ⟨n, hz, hnzero⟩
    have hsplit := tprod_eq_prod_range_mul_tprod_nat_add_of_mem hnorm hz (n + 1)
    have hn_mem : n ∈ Finset.range (n + 1) := by
      simp
    have hprefix_zero :
        (Finset.range (n + 1)).prod (fun i ↦ f i z) = 0 :=
      Finset.prod_eq_zero hn_mem hnzero
    exact ⟨hz, by rw [hsplit, hprefix_zero, zero_mul]⟩

/-- Theorem 1 (4): for a zero `z ∈ D` of the product, its vanishing order equals the sum of the
orders contributed by the finitely many factors vanishing at `z`. -/
theorem analyticOrderAt_tprod_eq_sum_zero_factor_orders
    (hD : IsOpen D) (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hnorm : NormallyMultipliableOnCompacta f D) {z : ℂ} (hz : z ∈ D) :
    analyticOrderAt (fun w ↦ ∏' n, f n w) z =
      ((zero_factor_indices_finite_of_normallyMultipliableOnCompacta hnorm hz).toFinset).sum
        (fun n ↦ analyticOrderAt (f n) z) := by
  classical
  let hzero_finite := zero_factor_indices_finite_of_normallyMultipliableOnCompacta hnorm hz
  rcases exists_nonvanishing_pointwise_tail_of_normallyMultipliableOnCompacta hnorm hz with
    ⟨N, htail, htailprod⟩
  have hprefix_diff :
      DifferentiableOn ℂ (fun w ↦ ∏ i ∈ Finset.range N, f i w) D := by
    -- Finite prefix products remain holomorphic on the whole domain.
    simpa [Finset.prod_fn] using
      (DifferentiableOn.finsetProd (u := Finset.range N) fun n _ ↦ hf n)
  have hprefix_analytic :
      AnalyticAt ℂ (fun w ↦ ∏ i ∈ Finset.range N, f i w) z :=
    hprefix_diff.analyticAt (hD.mem_nhds hz)
  have htail_diff :
      DifferentiableOn ℂ (fun w ↦ ∏' n, f (n + N) w) D :=
    differentiableOn_tprod_of_normallyMultipliableOnCompacta hD
      (fun n ↦ hf (n + N)) (normallyMultipliableOnCompacta_nat_add N hnorm)
  have htail_analytic :
      AnalyticAt ℂ (fun w ↦ ∏' n, f (n + N) w) z :=
    htail_diff.analyticAt (hD.mem_nhds hz)
  have htail_order_zero :
      analyticOrderAt (fun w ↦ ∏' n, f (n + N) w) z = 0 := by
    exact (htail_analytic.analyticOrderAt_eq_zero).2 htailprod
  have hsplit_event :
      (fun w ↦ ∏' n, f n w) =ᶠ[𝓝 z]
        (fun w ↦ (Finset.range N).prod (fun i ↦ f i w) * ∏' n, f (n + N) w) :=
    Filter.mem_of_superset (hD.mem_nhds hz) fun w hw ↦
      tprod_eq_prod_range_mul_tprod_nat_add_of_mem hnorm hw N
  have hprefix_orders :
      analyticOrderAt (fun w ↦ ∏ i ∈ Finset.range N, f i w) z =
        ∑ i ∈ Finset.range N, analyticOrderAt (f i) z := by
    -- The finite prefix order is the sum of the individual factor orders.
    exact analyticOrderAt_finsetProd_eq_sum fun i hi ↦
      (hf i).analyticAt (hD.mem_nhds hz)
  have hzero_lt : ∀ {n : ℕ}, f n z = 0 → n < N := by
    intro n hnzero
    by_contra hnlt
    have hNn : N ≤ n := Nat.not_lt.mp hnlt
    have hzero_tail : f (n - N + N) z = 0 := by
      simpa [Nat.sub_add_cancel hNn] using hnzero
    exact htail (n - N) hzero_tail
  have hzero_finset :
      hzero_finite.toFinset = (Finset.range N).filter (fun n ↦ f n z = 0) := by
    ext n
    constructor
    · intro hn
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simpa [Finset.mem_range] using
          hzero_lt ((Set.Finite.mem_toFinset hzero_finite).mp hn)
      · exact (Set.Finite.mem_toFinset hzero_finite).mp hn
    · intro hn
      exact (Set.Finite.mem_toFinset hzero_finite).mpr ((Finset.mem_filter.mp hn).2)
  have hsum_prefix :
      ∑ i ∈ Finset.range N, analyticOrderAt (f i) z =
        hzero_finite.toFinset.sum (fun n ↦ analyticOrderAt (f n) z) := by
    calc
      ∑ i ∈ Finset.range N, analyticOrderAt (f i) z
          = ∑ i ∈ Finset.range N, if f i z = 0 then analyticOrderAt (f i) z else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hfi : f i z = 0
              · simp [hfi]
              · have hfi_analytic : AnalyticAt ℂ (f i) z := (hf i).analyticAt (hD.mem_nhds hz)
                simp [hfi, (hfi_analytic.analyticOrderAt_eq_zero).2 hfi]
      _ = ((Finset.range N).filter (fun n ↦ f n z = 0)).sum (fun n ↦ analyticOrderAt (f n) z) := by
            rw [Finset.sum_filter]
      _ = hzero_finite.toFinset.sum (fun n ↦ analyticOrderAt (f n) z) := by
            rw [hzero_finset]
  -- Rewrite the product near `z` as finite prefix times analytic nonvanishing tail.
  calc
    analyticOrderAt (fun w ↦ ∏' n, f n w) z
        = analyticOrderAt
            (fun w ↦ (Finset.range N).prod (fun i ↦ f i w) * ∏' n, f (n + N) w) z := by
              rw [analyticOrderAt_congr hsplit_event]
    _ = analyticOrderAt (fun w ↦ ∏ i ∈ Finset.range N, f i w) z +
          analyticOrderAt (fun w ↦ ∏' n, f (n + N) w) z := by
            exact analyticOrderAt_mul hprefix_analytic htail_analytic
    _ = analyticOrderAt (fun w ↦ ∏ i ∈ Finset.range N, f i w) z := by
          rw [htail_order_zero, add_zero]
    _ = ∑ i ∈ Finset.range N, analyticOrderAt (f i) z := hprefix_orders
    _ = hzero_finite.toFinset.sum (fun n ↦ analyticOrderAt (f n) z) := hsum_prefix

end
