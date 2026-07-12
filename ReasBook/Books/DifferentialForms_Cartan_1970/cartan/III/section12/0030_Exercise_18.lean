import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0010_Theorem_3»
import DifferentialForms_Cartan_1970.III.section07.«0001_Remark_III_1_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool `lean_leansearch` was unavailable in this environment; the statement uses
-- the canonical pole predicate `meromorphicOrderAt f z < 0`, the divisor owner
-- `MeromorphicOn.divisor`, and the inversion chart at infinity.

open MeromorphicOn
open FormalMultilinearSeries
open scoped Topology BigOperators

noncomputable section

/-- A complex-valued function on `ℂ` is meromorphic at infinity if it is meromorphic at `0` in the
inversion chart `z ↦ z⁻¹`. This is the source-facing owner for meromorphy on the Riemann sphere,
while `MeromorphicAt` remains the core chart-level predicate. -/
def MeromorphicAtInfinity (f : ℂ → ℂ) : Prop :=
  MeromorphicAt (fun z : ℂ ↦ f z⁻¹) 0

/-- Helper for Exercise 18: a pole contributes a nonzero coefficient to the divisor on `univ`. -/
lemma pole_set_subset_divisor_support
    {f : ℂ → ℂ} (hf : Meromorphic f) :
    {z : ℂ | meromorphicOrderAt f z < 0} ⊆ Function.support (divisor f Set.univ) := by
  intro z hz
  have hz' : meromorphicOrderAt f z < 0 := by
    simpa using hz
  rw [Function.mem_support]
  -- A negative meromorphic order is finite and cannot map to `0` under `untop₀`.
  lift meromorphicOrderAt f z to ℤ using hz'.ne_top with n hn
  have hnneg : n < 0 := by
    exact_mod_cast hz'
  have hnne : n ≠ 0 := by
    linarith
  have hzDiv : divisor f Set.univ z = n := by
    rw [divisor_apply hf.meromorphicOn (by simp), ← hn, WithTop.untop₀_coe]
  rw [hzDiv]
  exact hnne

/-- Helper for Exercise 18: in the inversion chart, points sufficiently close to `0` have
meromorphic order either `0` or `⊤`. -/
lemma inversion_chart_order_eq_zero_or_top_near_zero
    {h : ℂ → ℂ} (hh : MeromorphicAt h 0) :
    ∃ ε > 0, ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε →
      meromorphicOrderAt h w = 0 ∨ meromorphicOrderAt h w = ⊤ := by
  rcases hh.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · have hzero' :
        ∀ᶠ w in nhdsWithin (0 : ℂ) ({0}ᶜ), ∀ᶠ z in nhdsWithin w ({0}ᶜ), h z = 0 := by
      exact (eventually_eventually_nhdsWithin.2 hzero)
    have htop : ∀ᶠ w in nhdsWithin (0 : ℂ) ({0}ᶜ), meromorphicOrderAt h w = ⊤ := by
      -- If the inversion chart vanishes on a punctured neighborhood of `w`, then its order is `⊤`.
      filter_upwards [hzero', self_mem_nhdsWithin] with w hw hwne
      have hcompl : ({0}ᶜ : Set ℂ) ∈ 𝓝 w := isOpen_compl_singleton.mem_nhds hwne
      have hw' : ∀ᶠ z in 𝓝 w, z ∈ ({0}ᶜ : Set ℂ) → h z = 0 :=
        eventually_nhdsWithin_iff.1 hw
      have hw_nhds : ∀ᶠ z in 𝓝 w, h z = 0 := by
        filter_upwards [hw', hcompl] with z hz hz0
        exact hz hz0
      exact (meromorphicOrderAt_eq_top_iff).2 (hw_nhds.filter_mono nhdsWithin_le_nhds)
    have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → meromorphicOrderAt h w = 0 ∨
        meromorphicOrderAt h w = ⊤ := by
      have hnear' :
          ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ({0}ᶜ : Set ℂ) → meromorphicOrderAt h w = 0 ∨
            meromorphicOrderAt h w = ⊤ := by
        exact (eventually_nhdsWithin_iff.1 htop).mono fun w hw hwmem ↦ Or.inr (hw hwmem)
      simpa using hnear'
    rcases Metric.mem_nhds_iff.1 hnear with ⟨ε, hεpos, hε⟩
    refine ⟨ε, hεpos, ?_⟩
    intro w hwne hwlt
    -- Convert the neighborhood statement into the requested punctured-ball statement.
    have hwball : w ∈ Metric.ball (0 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hwlt
    exact hε hwball hwne
  · have hanalytic : ∀ᶠ w in nhdsWithin (0 : ℂ) ({0}ᶜ), AnalyticAt ℂ h w :=
        hh.eventually_analyticAt
    have hzero : ∀ᶠ w in nhdsWithin (0 : ℂ) ({0}ᶜ), meromorphicOrderAt h w = 0 := by
      -- On the eventual nonzero branch, analyticity forces order `0`.
      filter_upwards [hanalytic, hne] with w hwa hwne
      simpa [hwa.meromorphicOrderAt_eq] using hwa.analyticOrderAt_eq_zero.2 hwne
    have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → meromorphicOrderAt h w = 0 ∨
        meromorphicOrderAt h w = ⊤ := by
      have hnear' :
          ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ({0}ᶜ : Set ℂ) → meromorphicOrderAt h w = 0 ∨
            meromorphicOrderAt h w = ⊤ := by
        exact (eventually_nhdsWithin_iff.1 hzero).mono fun w hw hwmem ↦ Or.inl (hw hwmem)
      simpa using hnear'
    rcases Metric.mem_nhds_iff.1 hnear with ⟨ε, hεpos, hε⟩
    refine ⟨ε, hεpos, ?_⟩
    intro w hwne hwlt
    -- Convert the neighborhood statement into the requested punctured-ball statement.
    have hwball : w ∈ Metric.ball (0 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hwlt
    exact hε hwball hwne

/-- Helper for Exercise 18: a meromorphic function on `ℂ` that is meromorphic at infinity has
trivial divisor outside a sufficiently large closed ball. -/
lemma exterior_divisor_eq_zero_of_meromorphic_at_infinity
    {f : ℂ → ℂ} (hf : Meromorphic f) (hinfty : MeromorphicAtInfinity f) :
    ∃ R > 0, ∀ z : ℂ, R < ‖z‖ → divisor f Set.univ z = 0 := by
  rcases inversion_chart_order_eq_zero_or_top_near_zero (h := fun w : ℂ ↦ f w⁻¹) hinfty with
    ⟨ε, hεpos, hε⟩
  refine ⟨ε⁻¹, inv_pos.mpr hεpos, ?_⟩
  intro z hzlarge
  have hznorm_pos : 0 < ‖z‖ := lt_trans (inv_pos.mpr hεpos) hzlarge
  have hz0 : z ≠ 0 := by
    exact norm_ne_zero_iff.1 hznorm_pos.ne'
  have hinv_norm : ‖z⁻¹‖ < ε := by
    rw [norm_inv]
    have hzlarge' : 1 / ε < ‖z‖ := by
      simpa [one_div] using hzlarge
    simpa [one_div] using (one_div_lt hεpos hznorm_pos).1 hzlarge'
  have hchart_order :
      meromorphicOrderAt (fun w : ℂ ↦ f w⁻¹) (z⁻¹) = 0 ∨
        meromorphicOrderAt (fun w : ℂ ↦ f w⁻¹) (z⁻¹) = ⊤ :=
    hε (z⁻¹) (inv_ne_zero hz0) hinv_norm
  have htransport :
      meromorphicOrderAt (fun w : ℂ ↦ f w⁻¹) (z⁻¹) = meromorphicOrderAt f z := by
    -- Route correction: transport the local order statement through inversion before touching
    -- the divisor, so the exterior vanishing becomes a one-line divisor computation.
    simpa [Function.comp] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := Inv.inv) (x := z⁻¹)
        (analyticAt_inv (inv_ne_zero hz0)) (by
          simp [deriv_inv, hz0]))
  rcases hchart_order with hchart_zero | hchart_top
  · have horder_zero : meromorphicOrderAt f z = 0 := by
      calc
        meromorphicOrderAt f z = meromorphicOrderAt (fun w : ℂ ↦ f w⁻¹) (z⁻¹) := htransport.symm
        _ = 0 := hchart_zero
    -- Once the order is `0`, the divisor coefficient is `0`.
    rw [divisor_apply hf.meromorphicOn (by simp), horder_zero]
    simp
  · have horder_top : meromorphicOrderAt f z = ⊤ := by
      calc
        meromorphicOrderAt f z = meromorphicOrderAt (fun w : ℂ ↦ f w⁻¹) (z⁻¹) := htransport.symm
        _ = ⊤ := hchart_top
    -- Once the order is `⊤`, the divisor coefficient is also `0` by definition.
    rw [divisor_apply hf.meromorphicOn (by simp), horder_top]
    simp

/-- Helper for Exercise 18: a function that is meromorphic at infinity is already in meromorphic
normal form outside a sufficiently large closed ball. -/
lemma meromorphicNFAt_outside_closedBall_of_meromorphic_at_infinity
    {f : ℂ → ℂ} (hinfty : MeromorphicAtInfinity f) :
    ∃ R > 0, ∀ z : ℂ, R < ‖z‖ → MeromorphicNFAt f z := by
  have hnear :
      ∀ᶠ w in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ (fun w : ℂ ↦ f w⁻¹) w :=
    hinfty.eventually_analyticAt
  have hnear' :
      ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → AnalyticAt ℂ (fun w : ℂ ↦ f w⁻¹) w := by
    simpa using (eventually_nhdsWithin_iff.1 hnear)
  rcases Metric.mem_nhds_iff.1 hnear' with ⟨ε, hεpos, hε⟩
  refine ⟨ε⁻¹, inv_pos.mpr hεpos, ?_⟩
  intro z hzlarge
  have hznorm_pos : 0 < ‖z‖ := lt_trans (inv_pos.mpr hεpos) hzlarge
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 hznorm_pos.ne'
  have hinv_norm : ‖z⁻¹‖ < ε := by
    rw [norm_inv]
    have hzlarge' : 1 / ε < ‖z‖ := by
      simpa [one_div] using hzlarge
    simpa [one_div] using (one_div_lt hεpos hznorm_pos).1 hzlarge'
  have hball : z⁻¹ ∈ Metric.ball (0 : ℂ) ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hinv_norm
  have hchart : AnalyticAt ℂ (fun w : ℂ ↦ f w⁻¹) (z⁻¹) :=
    hε hball (inv_ne_zero hz0)
  have hcomp : AnalyticAt ℂ (fun x : ℂ ↦ (fun w : ℂ ↦ f w⁻¹) (x⁻¹)) z := by
    -- Compose the analytic inversion-chart representative back with inversion at `z`.
    exact hchart.comp (analyticAt_inv hz0)
  have heq :
      (fun x : ℂ ↦ (fun w : ℂ ↦ f w⁻¹) (x⁻¹)) =ᶠ[𝓝 z] f := by
    -- Near a nonzero point, double inversion is literally the identity.
    filter_upwards [eventually_ne_nhds hz0] with x hx
    simp
  have hanalytic : AnalyticAt ℂ f z := hcomp.congr heq
  -- Analyticity is the normal-form branch needed outside the large ball.
  exact (meromorphicNFAt_iff_analyticAt_or).2 (Or.inl hanalytic)

/-- Core/canonical bridge for Exercise 18: a meromorphic function on `ℂ` that is also meromorphic
at infinity has divisor with finite support on `ℂ`. -/
theorem finite_divisor_support_of_meromorphic_on_riemann_sphere
    {f : ℂ → ℂ} (hf : Meromorphic f) (hinfty : MeromorphicAtInfinity f) :
    (divisor f Set.univ).support.Finite := by
  rcases exterior_divisor_eq_zero_of_meromorphic_at_infinity hf hinfty with ⟨R, hRpos, hR⟩
  have hsubset : (divisor f Set.univ).support ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hzsupport
    by_contra hzball
    have hzlarge : R < ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] using hzball
    -- Outside the closed ball the previous helper kills the divisor, contradicting support.
    rw [Function.mem_support] at hzsupport
    exact hzsupport (hR z hzlarge)
  -- Compactness of the closed ball upgrades local finiteness of the divisor support to finiteness.
  let D : Function.locallyFinsupp ℂ ℤ := divisor f Set.univ
  have hloc : LocallyFiniteSupport D := by
    simpa [D] using
      (Function.locallyFinsupp.locallyFiniteSupport (X := ℂ) (Y := ℤ) (f := D))
  have hfinite_ball :
      (Metric.closedBall (0 : ℂ) R ∩ D.support).Finite :=
    hloc.finite_inter_support_of_isCompact (isCompact_closedBall (0 : ℂ) R)
  exact hfinite_ball.subset fun z hz ↦ by
    refine ⟨hsubset ?_, ?_⟩
    · simpa [D] using hz
    · simpa [D] using hz

/-- Exercise 18 (1): if `f : ℂ → ℂ` is meromorphic on `ℂ` and also meromorphic at infinity, then
`f` has only finitely many poles in `ℂ`. -/
theorem finite_poles_of_meromorphic_on_riemann_sphere
    {f : ℂ → ℂ} (hf : Meromorphic f) (hinfty : MeromorphicAtInfinity f) :
    {z : ℂ | meromorphicOrderAt f z < 0}.Finite := by
  -- Poles are contained in the finite divisor support proved above.
  exact (finite_divisor_support_of_meromorphic_on_riemann_sphere hf hinfty).subset
    (pole_set_subset_divisor_support hf)

/-- Helper for Exercise 18: the canonical normal-form representative only differs from the raw
function at finitely many points on the sphere. -/
lemma finite_discrepancy_set_toMeromorphicNFOn_of_meromorphic_on_riemann_sphere
    {f : ℂ → ℂ} (hf : Meromorphic f) (hinfty : MeromorphicAtInfinity f) :
    {z : ℂ | toMeromorphicNFOn f Set.univ z ≠ f z}.Finite := by
  classical
  rcases meromorphicNFAt_outside_closedBall_of_meromorphic_at_infinity hinfty with
    ⟨R, hRpos, hR⟩
  let S : Set ℂ := {z : ℂ | toMeromorphicNFOn f Set.univ z = f z}
  have hS : S ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
    simpa [S, Filter.EventuallyEq, Filter.eventually_iff] using
      (toMeromorphicNFOn_eqOn_codiscrete (hf := hf.meromorphicOn) :
        f =ᶠ[Filter.codiscreteWithin Set.univ] toMeromorphicNFOn f Set.univ).symm
  have hSball : S ∈ Filter.codiscreteWithin (Metric.closedBall (0 : ℂ) R) :=
    Filter.codiscreteWithin_mono (by intro z hz; simp) hS
  have hfinite :
      (Metric.closedBall (0 : ℂ) R \ S).Finite :=
    (isCompact_closedBall (0 : ℂ) R).finite_diff_of_mem_codiscreteWithin hSball
  refine hfinite.subset ?_
  intro z hz
  have hzball : z ∈ Metric.closedBall (0 : ℂ) R := by
    by_contra hzball
    have hzlarge : R < ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] using hzball
    have hzNF : MeromorphicNFAt f z := hR z hzlarge
    have hzEq : toMeromorphicNFOn f Set.univ z = f z := by
      -- Outside the large ball, `f` is already in normal form, so conversion changes nothing.
      calc
        toMeromorphicNFOn f Set.univ z = toMeromorphicNFAt f z z := by
          rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf.meromorphicOn (by simp)]
        _ = f z := by
          exact congrFun (toMeromorphicNFAt_eq_self.2 hzNF) z
    exact hz hzEq
  refine ⟨hzball, ?_⟩
  simpa [S] using hz

/-- Helper for Exercise 18: a finitely supported nonnegative integer-valued function on `ℂ` is
realized by a polynomial whose evaluation is the corresponding finite product of linear factors. -/
lemma exists_polynomial_eval_eq_finset_prod_of_nonneg_finite_support
    {d : ℂ → ℤ} (hfin : d.support.Finite) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧
      ∀ z : ℂ, q.eval z = Finset.prod hfin.toFinset (fun u ↦ (z - u) ^ Int.toNat (d u)) := by
  classical
  let q : Polynomial ℂ :=
    Finset.prod hfin.toFinset (fun u ↦ (Polynomial.X - Polynomial.C u) ^ Int.toNat (d u))
  refine ⟨q, ?_, ?_⟩
  · -- Every linear factor is nonzero, so the finite product is nonzero as well.
    dsimp [q]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro u hu
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero u)
  · intro z
    -- Evaluate factorwise and collapse each linear factor to `z - u`.
    dsimp [q]
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl ?_
    intro u hu
    simp

/-- Helper for Exercise 18: the negative part of the divisor has finite support on the sphere. -/
lemma finite_support_neg_divisor_of_meromorphic_on_riemann_sphere
    {f : ℂ → ℂ} (hf : Meromorphic f) (hinfty : MeromorphicAtInfinity f) :
    ((divisor f Set.univ)⁻).support.Finite := by
  let D : Function.locallyFinsupp ℂ ℤ := (divisor f Set.univ)⁻
  have hfin_div : (divisor f Set.univ).support.Finite :=
    finite_divisor_support_of_meromorphic_on_riemann_sphere hf hinfty
  refine hfin_div.subset ?_
  intro z hz
  rw [Function.mem_support] at hz ⊢
  by_contra hz0
  exact hz (by simpa [D, hz0])

/-- Helper for Exercise 18: the finite negative part of the divisor is realized by a polynomial
denominator whose evaluation matches the finite linear-factor product pointwise. -/
lemma q0_eval_eq_factorized_negative_divisor_part
    {f : ℂ → ℂ} {q₀ : Polynomial ℂ}
    (hfin_D : ((divisor f Set.univ)⁻).support.Finite)
    (hq₀_eval : ∀ z : ℂ,
      q₀.eval z = Finset.prod hfin_D.toFinset
        (fun u ↦ (z - u) ^ Int.toNat (((divisor f Set.univ)⁻) u))) :
    (fun z : ℂ ↦ q₀.eval z) =
      ∏ᶠ u, (fun z : ℂ ↦ z - u) ^ ((divisor f Set.univ)⁻) u := by
  -- Route correction: make the polynomial denominator explicit as the canonical factorized
  -- rational attached to the negative divisor part before doing divisor or growth calculations.
  funext z
  calc
    q₀.eval z =
        Finset.prod hfin_D.toFinset
          (fun u ↦ (z - u) ^ Int.toNat (((divisor f Set.univ)⁻) u)) := hq₀_eval z
    _ = Finset.prod hfin_D.toFinset
          (fun u ↦ (z - u) ^ ((divisor f Set.univ)⁻) u) := by
        refine Finset.prod_congr rfl ?_
        intro u hu
        have hnonneg : 0 ≤ ((divisor f Set.univ)⁻) u :=
          negPart_nonneg (divisor f Set.univ u)
        calc
          (z - u) ^ Int.toNat (((divisor f Set.univ)⁻) u) =
              (z - u) ^ ((Int.toNat (((divisor f Set.univ)⁻) u) : ℤ)) := by
                symm
                exact zpow_natCast (z - u) (Int.toNat (((divisor f Set.univ)⁻) u))
          _ = (z - u) ^ ((divisor f Set.univ)⁻ u) := by
                rw [Int.toNat_of_nonneg hnonneg]
    _ = ∏ᶠ u, (z - u) ^ ((divisor f Set.univ)⁻) u := by
        symm
        refine finprod_eq_prod_of_mulSupport_subset _ ?_
        intro u hu
        have hu_support : ((divisor f Set.univ)⁻) u ≠ 0 := by
          contrapose! hu
          change ¬ ((z - u) ^ (((divisor f Set.univ)⁻) u) ≠ 1)
          rw [hu, zpow_zero]
          simp
        exact hfin_D.mem_toFinset.2 hu_support
    _ = (∏ᶠ u, (fun z : ℂ ↦ z - u) ^ ((divisor f Set.univ)⁻) u) z := by
        symm
        exact congrFun
          (Function.FactorizedRational.finprod_eq_fun (d := (divisor f Set.univ)⁻) hfin_D) z

/-- Helper for Exercise 18: once the denominator realizes the negative divisor part, multiplying
the canonical normal form of `f` by that denominator leaves exactly the positive divisor. -/
lemma divisor_pole_cleared_product_eq_pos_divisor
    {f : ℂ → ℂ} (hf : Meromorphic f) {q₀ : Polynomial ℂ}
    (hfin_D : ((divisor f Set.univ)⁻).support.Finite)
    (hq₀_eval : ∀ z : ℂ,
      q₀.eval z = Finset.prod hfin_D.toFinset
        (fun u ↦ (z - u) ^ Int.toNat (((divisor f Set.univ)⁻) u))) :
    divisor (fun z ↦ q₀.eval z * toMeromorphicNFOn f Set.univ z) Set.univ =
      (divisor f Set.univ)⁺ := by
  let D : Function.locallyFinsupp ℂ ℤ := (divisor f Set.univ)⁻
  let f₀ : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  have hq₀_factorized :
      (fun z : ℂ ↦ q₀.eval z) = ∏ᶠ u, (fun z : ℂ ↦ z - u) ^ D u :=
    q0_eval_eq_factorized_negative_divisor_part hfin_D hq₀_eval
  have hq₀_meromorphicOn : MeromorphicOn (fun z : ℂ ↦ q₀.eval z) Set.univ := by
    -- Rewrite to the canonical factorized rational, whose meromorphicity is built into mathlib.
    rw [hq₀_factorized]
    exact (Function.FactorizedRational.meromorphicNFOn D Set.univ).meromorphicOn
  have hf₀_meromorphicOn : MeromorphicOn f₀ Set.univ :=
    (meromorphicNFOn_toMeromorphicNFOn f Set.univ).meromorphicOn
  have hprod_meromorphicOn :
      MeromorphicOn (fun z ↦ q₀.eval z * f₀ z) Set.univ :=
    hq₀_meromorphicOn.mul hf₀_meromorphicOn
  ext z
  by_cases htop : meromorphicOrderAt f₀ z = ⊤
  · have horder_f : meromorphicOrderAt f z = ⊤ := by
      -- Transfer the infinite-order branch back through the canonical normal-form representative.
      rw [← meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hf.meromorphicOn (by simp)]
      exact htop
    have hdiv_f : divisor f Set.univ z = 0 := by
      rw [divisor_apply hf.meromorphicOn (by simp), horder_f]
      simp
    have hq₀_order : meromorphicOrderAt (fun z : ℂ ↦ q₀.eval z) z = (D z : ℤ) := by
      rw [hq₀_factorized, Function.FactorizedRational.meromorphicOrderAt_eq D hfin_D]
    have hprod_top : meromorphicOrderAt (fun z ↦ q₀.eval z * f₀ z) z = ⊤ := by
      -- A locally vanishing branch stays locally vanishing after multiplying by the polynomial.
      calc
        meromorphicOrderAt (fun z ↦ q₀.eval z * f₀ z) z =
            meromorphicOrderAt (fun z : ℂ ↦ q₀.eval z) z + meromorphicOrderAt f₀ z := by
              simpa [f₀] using
                meromorphicOrderAt_mul (hq₀_meromorphicOn z (by simp)) (hf₀_meromorphicOn z (by simp))
        _ = ⊤ := by
          rw [hq₀_order, htop]
          simp
    -- On the infinite-order branch both the pole-cleared product and the original divisor
    -- contribute `0` to the divisor coefficient.
    rw [divisor_apply hprod_meromorphicOn (by simp), hprod_top]
    simp [hdiv_f]
  · lift meromorphicOrderAt f₀ z to ℤ using htop with n hn
    have horder_f : meromorphicOrderAt f z = n := by
      -- On the finite-order branch, `toMeromorphicNFOn` preserves the precise meromorphic order.
      rw [← meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hf.meromorphicOn (by simp)]
      exact hn.symm
    have hdiv_f : divisor f Set.univ z = n := by
      rw [divisor_apply hf.meromorphicOn (by simp), horder_f, WithTop.untop₀_coe]
    have hq₀_order : meromorphicOrderAt (fun z : ℂ ↦ q₀.eval z) z = (D z : ℤ) := by
      rw [hq₀_factorized, Function.FactorizedRational.meromorphicOrderAt_eq D hfin_D]
    have hprod_order : meromorphicOrderAt (fun z ↦ q₀.eval z * f₀ z) z = (D z + n : ℤ) := by
      -- Finite orders add exactly, so the negative divisor part cancels the poles of `f`.
      calc
        meromorphicOrderAt (fun z ↦ q₀.eval z * f₀ z) z =
            meromorphicOrderAt (fun z : ℂ ↦ q₀.eval z) z + meromorphicOrderAt f₀ z := by
              simpa [f₀] using
                meromorphicOrderAt_mul (hq₀_meromorphicOn z (by simp)) (hf₀_meromorphicOn z (by simp))
        _ = (D z + n : ℤ) := by
          rw [hq₀_order, ← hn, ← WithTop.coe_add]
    have hparts' :
        (divisor f Set.univ)⁺ z - (divisor f Set.univ)⁻ z = divisor f Set.univ z := by
      simpa using
        congrArg (fun m : Function.locallyFinsupp ℂ ℤ => m z)
          (posPart_sub_negPart (divisor f Set.univ))
    have hparts : (divisor f Set.univ)⁻ z + divisor f Set.univ z = (divisor f Set.univ)⁺ z := by
      omega
    rw [divisor_apply hprod_meromorphicOn (by simp), hprod_order, WithTop.untop₀_coe]
    simpa [D, hdiv_f] using hparts

/-- Helper for Exercise 18: after pole-clearing, the canonical normal-form representative is entire
and still agrees with the raw pole-cleared product away from the denominator roots. -/
lemma analyticOnNhd_pole_cleared_normal_form_extension
    {f : ℂ → ℂ} (hf : Meromorphic f) {q₀ : Polynomial ℂ}
    (hfin_D : ((divisor f Set.univ)⁻).support.Finite)
    (hq₀_eval : ∀ z : ℂ,
      q₀.eval z = Finset.prod hfin_D.toFinset
        (fun u ↦ (z - u) ^ Int.toNat (((divisor f Set.univ)⁻) u))) :
    let h₀ : ℂ → ℂ := fun z ↦ q₀.eval z * toMeromorphicNFOn f Set.univ z
    let g₀ : ℂ → ℂ := toMeromorphicNFOn h₀ Set.univ
    AnalyticOnNhd ℂ g₀ Set.univ ∧ Set.EqOn g₀ h₀ {z | ¬ q₀.IsRoot z} := by
  let h₀ : ℂ → ℂ := fun z ↦ q₀.eval z * toMeromorphicNFOn f Set.univ z
  let g₀ : ℂ → ℂ := toMeromorphicNFOn h₀ Set.univ
  have hh₀_meromorphicOn : MeromorphicOn h₀ Set.univ := by
    -- The pole-cleared product is still meromorphic on `ℂ`.
    dsimp [h₀]
    have hq₀_analyticOnNhd : AnalyticOnNhd ℂ (fun z : ℂ ↦ q₀.eval z) Set.univ := by
      simpa using (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) q₀)
    exact hq₀_analyticOnNhd.meromorphicOn.mul
      (meromorphicNFOn_toMeromorphicNFOn f Set.univ).meromorphicOn
  have hg₀_meromorphicNFOn : MeromorphicNFOn g₀ Set.univ := by
    simpa [g₀] using meromorphicNFOn_toMeromorphicNFOn h₀ Set.univ
  have hg₀_analytic : AnalyticOnNhd ℂ g₀ Set.univ := by
    -- Route correction: prove entire-ness through the divisor identity first, then convert the
    -- canonical representative back to analytic data.
    rw [← hg₀_meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd,
      divisor_of_toMeromorphicNFOn hh₀_meromorphicOn,
      divisor_pole_cleared_product_eq_pos_divisor hf hfin_D hq₀_eval]
    intro z
    exact posPart_nonneg (divisor f Set.univ z)
  refine ⟨hg₀_analytic, ?_⟩
  intro z hz
  have hq₀_analyticAt : AnalyticAt ℂ (fun w : ℂ ↦ q₀.eval w) z := by
    simpa using (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) q₀ z (by simp))
  have hq₀_ne : q₀.eval z ≠ 0 := by
    simpa [Polynomial.IsRoot] using hz
  have hh₀_meromorphicNFAt : MeromorphicNFAt h₀ z := by
    -- Off the denominator roots, multiplying by the polynomial does not disturb normal form.
    dsimp [h₀]
    simpa using
      (meromorphicNFAt_mul_iff_right (f := toMeromorphicNFOn f Set.univ)
        (g := fun w : ℂ ↦ q₀.eval w) (x := z) hq₀_analyticAt hq₀_ne).2
        ((meromorphicNFOn_toMeromorphicNFOn f Set.univ) (by simp))
  calc
    g₀ z = toMeromorphicNFAt h₀ z z := by
      simpa [g₀] using
        (toMeromorphicNFOn_eq_toMeromorphicNFAt (f := h₀) (U := Set.univ)
          hh₀_meromorphicOn (x := z) (by simp))
    _ = h₀ z := by
      exact congrFun (toMeromorphicNFAt_eq_self.2 hh₀_meromorphicNFAt) z

/-- Helper for Exercise 18: the finite negative part of the divisor is realized by a polynomial
denominator whose evaluation matches the finite linear-factor product pointwise. -/
lemma exists_polynomial_realizing_negative_divisor_part
    {f : ℂ → ℂ} (hfin_D : ((divisor f Set.univ)⁻).support.Finite) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧
      (∀ z : ℂ,
        q.eval z = Finset.prod hfin_D.toFinset
          (fun u ↦ (z - u) ^ Int.toNat (((divisor f Set.univ)⁻) u))) ∧
      divisor (fun z ↦ q.eval z) Set.univ = (divisor f Set.univ)⁻ := by
  let D : Function.locallyFinsupp ℂ ℤ := (divisor f Set.univ)⁻
  obtain ⟨q, hq_ne, hq_eval⟩ := exists_polynomial_eval_eq_finset_prod_of_nonneg_finite_support hfin_D
  refine ⟨q, hq_ne, ?_, ?_⟩
  · intro z
    simpa [D] using hq_eval z
  · have hfactorized :
        (fun z : ℂ ↦ q.eval z) = ∏ᶠ u, (fun z : ℂ ↦ z - u) ^ D u :=
      q0_eval_eq_factorized_negative_divisor_part hfin_D (f := f) hq_eval
    -- Route correction: identify the polynomial evaluation with the canonical factorized
    -- rational function before invoking the divisor API.
    rw [hfactorized, Function.FactorizedRational.divisor hfin_D]

/-- Helper for Exercise 18: a meromorphic germ at infinity satisfies a polynomial-growth bound on
the exterior of a large ball. -/
lemma meromorphic_at_infinity_exterior_norm_le_mul_zpow
    {f : ℂ → ℂ} (hinfty : MeromorphicAtInfinity f) :
    ∃ n : ℤ, ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n := by
  let chart : ℂ → ℂ := fun w ↦ f w⁻¹
  by_cases htop : meromorphicOrderAt chart 0 = ⊤
  · have hzero : ∀ᶠ w in 𝓝[≠] (0 : ℂ), chart w = 0 := by
      exact (meromorphicOrderAt_eq_top_iff).1 htop
    have hzero' : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → chart w = 0 := by
      simpa [chart] using (eventually_nhdsWithin_iff.1 hzero)
    rcases Metric.mem_nhds_iff.1 hzero' with ⟨ε, hεpos, hε⟩
    refine ⟨0, ε⁻¹ + 1, 0, by positivity, le_rfl, ?_⟩
    intro z hz
    have hzlarge : ε⁻¹ < ‖z‖ := by
      exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hz
    have hznorm_pos : 0 < ‖z‖ := lt_trans (inv_pos.mpr hεpos) hzlarge
    have hz0 : z ≠ 0 := norm_ne_zero_iff.1 hznorm_pos.ne'
    have hinv_norm : ‖z⁻¹‖ < ε := by
      rw [norm_inv]
      simpa [one_div] using (one_div_lt hεpos hznorm_pos).1 (by simpa [one_div] using hzlarge)
    have hball : z⁻¹ ∈ Metric.ball (0 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hinv_norm
    have hchart : chart (z⁻¹) = 0 := hε hball (inv_ne_zero hz0)
    have hfz : f z = 0 := by
      simpa [chart] using hchart
    simp [hfz]
  · lift meromorphicOrderAt chart 0 to ℤ using htop with m hm
    obtain ⟨g, hg_an, -, hchart_eq⟩ := (meromorphicOrderAt_eq_int_iff hinfty).1 hm.symm
    have hchart_eq' : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → chart w = w ^ m * g w := by
      simpa [chart] using (eventually_nhdsWithin_iff.1 hchart_eq)
    rcases Metric.mem_nhds_iff.1 hchart_eq' with ⟨ε₁, hε₁pos, hε₁⟩
    have hgbounded : ∀ᶠ w in 𝓝 (0 : ℂ), ‖g w‖ ≤ ‖g 0‖ + 1 := by
      have hball : ∀ᶠ w in 𝓝 (0 : ℂ), g w ∈ Metric.ball (g 0) 1 :=
        hg_an.continuousAt (Metric.ball_mem_nhds _ zero_lt_one)
      filter_upwards [hball] with w hw
      have hw' : ‖g w - g 0‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      calc
        ‖g w‖ = ‖(g w - g 0) + g 0‖ := by ring_nf
        _ ≤ ‖g w - g 0‖ + ‖g 0‖ := norm_add_le _ _
        _ ≤ ‖g 0‖ + 1 := by linarith
    rcases Metric.mem_nhds_iff.1 hgbounded with ⟨ε₂, hε₂pos, hε₂⟩
    let ε : ℝ := min ε₁ ε₂
    let R : ℝ := max 1 (ε⁻¹ + 1)
    let M : ℝ := ‖g 0‖ + 1
    refine ⟨-m, R, M, ?_, ?_, ?_⟩
    · dsimp [R, ε]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    · dsimp [M]
      positivity
    · intro z hz
      have hR_one : 1 ≤ R := by
        exact le_max_left _ _
      have hz_one : 1 ≤ ‖z‖ := le_trans hR_one hz
      have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hz_one
      have hz0 : z ≠ 0 := norm_ne_zero_iff.1 hz_pos.ne'
      have hR_inv : ε⁻¹ + 1 ≤ R := by
        exact le_max_right _ _
      have hz_inv : ε⁻¹ + 1 ≤ ‖z‖ := le_trans hR_inv hz
      have hεpos : 0 < ε := lt_min hε₁pos hε₂pos
      have hinv_norm : ‖z⁻¹‖ < ε := by
        rw [norm_inv]
        have hzlarge : ε⁻¹ < ‖z‖ := by
          exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) hz_inv
        simpa [one_div] using (one_div_lt hεpos hz_pos).1 (by simpa [one_div] using hzlarge)
      have hball₁ : z⁻¹ ∈ Metric.ball (0 : ℂ) ε₁ := by
        have : ‖z⁻¹‖ < ε₁ := lt_of_lt_of_le hinv_norm (min_le_left _ _)
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hball₂ : z⁻¹ ∈ Metric.ball (0 : ℂ) ε₂ := by
        have : ‖z⁻¹‖ < ε₂ := lt_of_lt_of_le hinv_norm (min_le_right _ _)
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hchart_val : f z = (z⁻¹) ^ m * g (z⁻¹) := by
        simpa [chart] using hε₁ hball₁ (inv_ne_zero hz0)
      have hg_bound : ‖g (z⁻¹)‖ ≤ M := by
        simpa [M] using hε₂ hball₂
      have hnorm_pow : ‖(z⁻¹ : ℂ) ^ m‖ = ‖z‖ ^ (-m) := by
        calc
          ‖(z⁻¹ : ℂ) ^ m‖ = ‖z⁻¹‖ ^ m := norm_zpow _ _
          _ = (1 / ‖z‖) ^ m := by simp [norm_inv, one_div]
          _ = ‖z‖ ^ (-m) := by
            rw [one_div_zpow]
            simpa [one_div] using (zpow_neg hz_pos.ne' (n := m) (a := ‖z‖)).symm
      calc
        ‖f z‖ = ‖(z⁻¹ : ℂ) ^ m * g (z⁻¹)‖ := by rw [hchart_val]
        _ = ‖(z⁻¹ : ℂ) ^ m‖ * ‖g (z⁻¹)‖ := norm_mul _ _
        _ ≤ ‖(z⁻¹ : ℂ) ^ m‖ * M := by gcongr
        _ = M * ‖z‖ ^ (-m) := by rw [hnorm_pow, mul_comm]

/-- Helper for Exercise 18: every polynomial has at most polynomial growth on the exterior of the
unit ball. -/
lemma polynomial_exterior_norm_le_mul_natDegree (q : Polynomial ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖q.eval z‖ ≤ M * ‖z‖ ^ q.natDegree := by
  let M : ℝ := Finset.sum (Finset.range (q.natDegree + 1)) fun i ↦ ‖q.coeff i‖
  refine ⟨M, by positivity, ?_⟩
  intro z hz
  calc
    ‖q.eval z‖ = ‖Finset.sum (Finset.range (q.natDegree + 1)) fun i ↦ q.coeff i * z ^ i‖ := by
      rw [Polynomial.eval_eq_sum_range]
    _ ≤ Finset.sum (Finset.range (q.natDegree + 1)) (fun i ↦ ‖q.coeff i * z ^ i‖) :=
      norm_sum_le _ _
    _ = Finset.sum (Finset.range (q.natDegree + 1)) (fun i ↦ ‖q.coeff i‖ * ‖z‖ ^ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [norm_mul, norm_pow]
    _ ≤ Finset.sum (Finset.range (q.natDegree + 1)) (fun i ↦ ‖q.coeff i‖ * ‖z‖ ^ q.natDegree) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hz (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (norm_nonneg _)
    _ = M * ‖z‖ ^ q.natDegree := by
      simpa [M, mul_comm, mul_left_comm, mul_assoc] using
        (Finset.sum_mul (s := Finset.range (q.natDegree + 1))
          (f := fun i ↦ ‖q.coeff i‖) (a := ‖z‖ ^ q.natDegree)).symm

/-- Helper for Exercise 18: a finite subset of `ℂ` is contained in the zero set of some nonzero
polynomial. -/
lemma exists_polynomial_vanishing_on_finite_set
    {s : Set ℂ} (hs : s.Finite) :
    ∃ r : Polynomial ℂ, r ≠ 0 ∧ s ⊆ {z : ℂ | r.IsRoot z} := by
  classical
  let r : Polynomial ℂ :=
    Finset.prod hs.toFinset fun u ↦ (Polynomial.X - Polynomial.C u)
  refine ⟨r, ?_, ?_⟩
  · -- Every linear factor is nonzero, so the finite product is nonzero.
    dsimp [r]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro u hu
    exact sub_ne_zero.mpr (Polynomial.X_ne_C u)
  · intro z hz
    have hzmem : z ∈ hs.toFinset := hs.mem_toFinset.2 hz
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero_iff.2 ⟨z, hzmem, by simp⟩

/-- Helper for Exercise 18: the polynomial realizing the negative divisor part vanishes at every
pole of the original meromorphic function. -/
lemma pole_set_subset_isRoot_of_negative_divisor_denominator
    {f : ℂ → ℂ} {q₀ : Polynomial ℂ} (hf : Meromorphic f)
    (hq₀_divisor : divisor (fun z ↦ q₀.eval z) Set.univ = (divisor f Set.univ)⁻) :
    {z : ℂ | meromorphicOrderAt f z < 0} ⊆ {z : ℂ | q₀.IsRoot z} := by
  intro z hz
  by_contra hzroot
  have hq₀_analyticAt : AnalyticAt ℂ (fun w : ℂ ↦ q₀.eval w) z := by
    simpa using (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) q₀ z (by simp))
  have hq₀_ne : q₀.eval z ≠ 0 := by
    simpa [Polynomial.IsRoot] using hzroot
  have hq₀_order : meromorphicOrderAt (fun w : ℂ ↦ q₀.eval w) z = 0 := by
    simpa [hq₀_analyticAt.meromorphicOrderAt_eq] using
      hq₀_analyticAt.analyticOrderAt_eq_zero.2 hq₀_ne
  have hq₀_coeff : divisor (fun w ↦ q₀.eval w) Set.univ z = 0 := by
    rw [divisor_apply (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) q₀).meromorphicOn (by simp), hq₀_order]
    simp
  lift meromorphicOrderAt f z to ℤ using hz.ne_top with n hn
  have hz' : meromorphicOrderAt f z < 0 := by
    simpa using hz
  have hnneg_top : (n : WithTop ℤ) < 0 := by
    simpa [hn] using hz'
  have hnneg : n < 0 := by
    exact_mod_cast hnneg_top
  have hdiv_f : divisor f Set.univ z = n := by
    rw [divisor_apply hf.meromorphicOn (by simp), ← hn, WithTop.untop₀_coe]
  have hparts :
      (divisor f Set.univ)⁺ z - (divisor f Set.univ)⁻ z = divisor f Set.univ z := by
    simpa using
      congrArg (fun m : Function.locallyFinsupp ℂ ℤ => m z)
        (posPart_sub_negPart (divisor f Set.univ))
  have hnegpart_pos : 0 < (divisor f Set.univ)⁻ z := by
    have hpos_nonneg : 0 ≤ (divisor f Set.univ)⁺ z := posPart_nonneg _
    have hneg_nonneg : 0 ≤ (divisor f Set.univ)⁻ z := negPart_nonneg _
    omega
  have hnegpart_ne : (divisor f Set.univ)⁻ z ≠ 0 := by
    linarith
  have : (divisor f Set.univ)⁻ z = 0 := by
    simpa [hq₀_divisor] using hq₀_coeff
  exact hnegpart_ne this

/-- Helper for Exercise 18: the scalar Taylor coefficient at the origin used in the entire-growth
argument. -/
def entire_growth_taylor_coeff (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k f 0 / k.factorial

/-- Helper for Exercise 18: Cauchy's estimate bounds the Taylor coefficients of an entire function
from the exterior polynomial-growth hypothesis. -/
lemma entire_growth_taylor_coeff_norm_le_of_exterior_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M r : ℝ} (hr0 : 0 < r) (hR : R ≤ r)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) (k : ℕ) :
    ‖entire_growth_taylor_coeff f k‖ ≤ max M 0 * r ^ (n - (k : ℤ)) := by
  have hball : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (r + 1)) := by
    intro z hz
    exact (hf z).differentiableWithinAt
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    ofScalars ℂ (fun m ↦ entire_growth_taylor_coeff f m)
  have hseries : HasFPowerSeriesAt f p 0 := by
    -- The global Taylor series of an entire function is its power-series expansion at the origin.
    rw [hasFPowerSeriesAt_iff]
    refine Filter.Eventually.of_forall ?_
    intro z
    simpa [p, entire_growth_taylor_coeff, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
  have hseriesBall : HasFPowerSeriesOnBall f p 0 (ENNReal.ofReal (r + 1)) := by
    rcases holomorphic_on_disc_has_power_series_expansion
        (f := f) (ρ := r + 1) (by positivity) hball with ⟨a, ha⟩
    have hcoeffs : a = fun m ↦ entire_growth_taylor_coeff f m := by
      funext m
      have hpeq : ofScalars ℂ a = p := ha.hasFPowerSeriesAt.eq_formalMultilinearSeries hseries
      have hm := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q.coeff m) hpeq
      simpa [p, FormalMultilinearSeries.coeff_ofScalars, entire_growth_taylor_coeff] using hm
    simpa [p, hcoeffs] using ha
  have hcircle : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ max M 0 * r ^ n := by
    intro z hz
    have hznorm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, sub_zero] using hz
    have hzR : R ≤ ‖z‖ := by
      rw [hznorm]
      exact hR
    calc
      ‖f z‖ ≤ M * ‖z‖ ^ n := hbound z hzR
      _ = M * r ^ n := by rw [hznorm]
      _ ≤ max M 0 * r ^ n := by
        exact mul_le_mul_of_nonneg_right (le_max_left M 0) (by positivity)
  have hcoeff :
      ‖p.coeff k‖ ≤ (max M 0 * r ^ n) / r ^ k := by
    simpa [p] using
      norm_taylor_coefficient_le_of_circle_bound (f := f)
        (a := fun m ↦ entire_growth_taylor_coeff f m) k hseriesBall hr0 (by linarith) hcircle
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  calc
    ‖entire_growth_taylor_coeff f k‖ = ‖p.coeff k‖ := by simp [p, entire_growth_taylor_coeff]
    _ ≤ (max M 0 * r ^ n) / r ^ k := hcoeff
    _ = max M 0 * r ^ (n - (k : ℤ)) := by
      calc
        (max M 0 * r ^ n) / r ^ k = max M 0 * (r ^ n / r ^ (k : ℤ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
          simp [zpow_natCast]
        _ = max M 0 * r ^ (n - (k : ℤ)) := by rw [zpow_sub₀ hrne]

/-- Helper for Exercise 18: Taylor coefficients above the growth exponent vanish. -/
lemma entire_growth_taylor_coeff_eq_zero_of_int_lt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M : ℝ}
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) {k : ℕ} (hk : n < (k : ℤ)) :
    entire_growth_taylor_coeff f k = 0 := by
  by_contra hk0
  let B : ℝ := max M 0
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_max_right M 0
  have hk_norm_pos : 0 < ‖entire_growth_taylor_coeff f k‖ := norm_pos_iff.mpr hk0
  obtain ⟨m, hm⟩ := exists_nat_gt (max R 2 + B / ‖entire_growth_taylor_coeff f k‖)
  have hm_one : (1 : ℝ) < m := by
    have haux : (2 : ℝ) < m := by
      have hdiv_nonneg : 0 ≤ B / ‖entire_growth_taylor_coeff f k‖ := by positivity
      linarith [show (2 : ℝ) ≤ max R 2 by exact le_max_right _ _]
    linarith
  have hm_pos : 0 < (m : ℝ) := by linarith
  have hR : R ≤ (m : ℝ) := by
    have hdiv_nonneg : 0 ≤ B / ‖entire_growth_taylor_coeff f k‖ := by positivity
    linarith [show R ≤ max R 2 by exact le_max_left _ _]
  have hcoeff := entire_growth_taylor_coeff_norm_le_of_exterior_growth
    hf (n := n) (R := R) (M := M) hm_pos hR hbound k
  have hsub : n - (k : ℤ) ≤ (-1 : ℤ) := by linarith
  have hpow : (m : ℝ) ^ (n - (k : ℤ)) ≤ (m : ℝ) ^ (-1 : ℤ) := by
    exact (zpow_le_zpow_iff_right₀ hm_one).2 hsub
  have hnorm_le : ‖entire_growth_taylor_coeff f k‖ ≤ B / (m : ℝ) := by
    calc
      ‖entire_growth_taylor_coeff f k‖ ≤ B * (m : ℝ) ^ (n - (k : ℤ)) := by simpa [B] using hcoeff
      _ ≤ B * (m : ℝ) ^ (-1 : ℤ) := mul_le_mul_of_nonneg_left hpow hB_nonneg
      _ = B / (m : ℝ) := by simp [B, div_eq_mul_inv]
  have hdiv_lt_m : B / ‖entire_growth_taylor_coeff f k‖ < (m : ℝ) := by
    have hmax_nonneg : 0 ≤ max R 2 := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right R 2)
    linarith
  have hmul_lt : B < ‖entire_growth_taylor_coeff f k‖ * (m : ℝ) := by
    have := (div_lt_iff₀ hk_norm_pos).mp hdiv_lt_m
    simpa [mul_comm] using this
  have hnorm_lt : B / (m : ℝ) < ‖entire_growth_taylor_coeff f k‖ := by
    exact (div_lt_iff₀ hm_pos).2 hmul_lt
  exact (not_lt_of_ge hnorm_le) hnorm_lt

/-- Helper for Exercise 18: evaluating the finite monomial sum recovers the corresponding finite
Taylor sum. -/
lemma polynomial_eval_eq_taylor_sum_range (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    Polynomial.eval z
      (Finset.sum (Finset.range N) fun m : ℕ ↦ Polynomial.monomial m (c m)) =
      Finset.sum (Finset.range N) fun m : ℕ ↦ c m * z ^ m := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Polynomial.eval_add]
      simp [Finset.sum_range_succ, ih, add_comm]

/-- Helper for Exercise 18: once high Taylor coefficients vanish, the Taylor series collapses to a
polynomial evaluation. -/
lemma scalar_tsum_eq_polynomial_eval_of_eventually_zero
    {c : ℕ → ℂ} {N : ℕ} (hc : ∀ m > N, c m = 0) (z : ℂ) :
    ∑' m : ℕ, c m * z ^ m =
      Polynomial.eval z
        (Finset.sum (Finset.range (N + 1)) fun m : ℕ ↦ Polynomial.monomial m (c m)) := by
  have hzero : ∀ m ∉ Finset.range (N + 1), c m * z ^ m = 0 := by
    intro m hm
    have hm' : N < m := by
      exact Nat.lt_of_not_ge fun hge ↦ hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hge))
    simp [hc m hm']
  rw [tsum_eq_sum (s := Finset.range (N + 1)) hzero]
  -- Rewrite the remaining finite Taylor sum as a polynomial evaluation.
  exact (polynomial_eval_eq_taylor_sum_range c (N + 1) z).symm

/-- Helper for Exercise 18: an entire function on `ℂ` with a polynomial-growth bound outside a
large ball is itself a polynomial. -/
lemma exists_polynomial_of_entire_norm_le_mul_zpow_local
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M : ℝ}
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  let c : ℕ → ℂ := entire_growth_taylor_coeff f
  have hc : ∀ m : ℕ, n < (m : ℤ) → c m = 0 := by
    intro m hm
    exact entire_growth_taylor_coeff_eq_zero_of_int_lt hf hbound hm
  by_cases hn : 0 ≤ n
  · let N : ℕ := Int.toNat n
    let p : Polynomial ℂ :=
      Finset.sum (Finset.range (N + 1)) fun m : ℕ ↦ Polynomial.monomial m (c m)
    refine ⟨p, ?_⟩
    intro z
    have hsum : HasSum (fun m : ℕ ↦ c m * z ^ m) (f z) := by
      simpa [c, entire_growth_taylor_coeff, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
    have hcollapse : ∑' m : ℕ, c m * z ^ m = p.eval z := by
      apply scalar_tsum_eq_polynomial_eval_of_eventually_zero
      intro m hm
      have hm' : ((N : ℕ) : ℤ) < (m : ℤ) := by
        exact_mod_cast hm
      exact hc m (by simpa [N, Int.toNat_of_nonneg hn] using hm')
    calc
      f z = ∑' m : ℕ, c m * z ^ m := hsum.tsum_eq.symm
      _ = p.eval z := hcollapse
  · have hnneg : n < 0 := lt_of_not_ge hn
    refine ⟨0, ?_⟩
    intro z
    have hsum : HasSum (fun m : ℕ ↦ c m * z ^ m) (f z) := by
      simpa [c, entire_growth_taylor_coeff, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
    have hzero : HasSum (fun m : ℕ ↦ c m * z ^ m) 0 := by
      have hfun : (fun m : ℕ ↦ c m * z ^ m) = fun _ : ℕ ↦ 0 := by
        funext m
        have hm : n < (m : ℤ) := lt_of_lt_of_le hnneg (by exact_mod_cast (Nat.zero_le m))
        simp [c, hc m hm]
      rw [hfun]
      exact hasSum_zero
    simpa using hsum.unique hzero

/-- Helper for Exercise 18: after clearing the finite poles, the resulting entire numerator still
has polynomial growth on the exterior of a large ball. -/
lemma pole_cleared_numerator_exterior_norm_le_mul_zpow
    {f : ℂ → ℂ} (hf : Meromorphic f) (hinfty : MeromorphicAtInfinity f) {q₀ : Polynomial ℂ}
    (hfin_D : ((divisor f Set.univ)⁻).support.Finite)
    (hq₀_eval : ∀ z : ℂ,
      q₀.eval z = Finset.prod hfin_D.toFinset
        (fun u ↦ (z - u) ^ Int.toNat (((divisor f Set.univ)⁻) u))) :
    let h₀ : ℂ → ℂ := fun z ↦ q₀.eval z * toMeromorphicNFOn f Set.univ z
    let g₀ : ℂ → ℂ := toMeromorphicNFOn h₀ Set.univ
    ∃ n : ℤ, ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖g₀ z‖ ≤ M * ‖z‖ ^ n := by
  let h₀ : ℂ → ℂ := fun z ↦ q₀.eval z * toMeromorphicNFOn f Set.univ z
  let g₀ : ℂ → ℂ := toMeromorphicNFOn h₀ Set.univ
  obtain ⟨n₁, R₁, M₁, hR₁pos, hM₁nonneg, hf_bound⟩ :=
    meromorphic_at_infinity_exterior_norm_le_mul_zpow hinfty
  obtain ⟨M₂, hM₂nonneg, hq_bound⟩ := polynomial_exterior_norm_le_mul_natDegree q₀
  have hg₀_eq : Set.EqOn g₀ h₀ {z | ¬ q₀.IsRoot z} := by
    -- Off the zeros of `q₀`, the entire normal-form extension agrees with the raw product.
    simpa [h₀, g₀] using
      (analyticOnNhd_pole_cleared_normal_form_extension hf hfin_D hq₀_eval).2
  obtain ⟨R₃, hR₃pos, hNF⟩ := meromorphicNFAt_outside_closedBall_of_meromorphic_at_infinity hinfty
  let R₂ : ℝ := Finset.sum hfin_D.toFinset fun u ↦ (‖u‖ + 1)
  let R : ℝ := max R₁ (max 1 (max R₂ (R₃ + 1)))
  refine ⟨(q₀.natDegree : ℤ) + n₁, R, M₂ * M₁, ?_, mul_nonneg hM₂nonneg hM₁nonneg, ?_⟩
  · dsimp [R]
    exact lt_of_lt_of_le hR₁pos (le_max_left _ _)
  · intro z hz
    have hzR₁ : R₁ ≤ ‖z‖ := le_trans (le_max_left _ _) hz
    have hz_mid : max 1 (max R₂ (R₃ + 1)) ≤ ‖z‖ := le_trans (le_max_right _ _) hz
    have hz_one : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz_mid
    have hz_tail : max R₂ (R₃ + 1) ≤ ‖z‖ := le_trans (le_max_right _ _) hz_mid
    have hzR₂ : R₂ ≤ ‖z‖ := le_trans (le_max_left _ _) hz_tail
    have hzR₃ : R₃ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz_tail
    have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (lt_of_lt_of_le zero_lt_one hz_one).ne'
    have hq₀_nonroot : ¬ q₀.IsRoot z := by
      rw [Polynomial.IsRoot, hq₀_eval z]
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro u hu
      have hu_le : ‖u‖ + 1 ≤ R₂ := by
        dsimp [R₂]
        exact Finset.single_le_sum (f := fun v ↦ ‖v‖ + 1)
          (fun v hv => by positivity) hu
      have huz : z ≠ u := by
        intro hzu
        subst hzu
        linarith
      exact pow_ne_zero _ (sub_ne_zero.mpr huz)
    have hzNF : MeromorphicNFAt f z := by
      exact hNF z (lt_of_lt_of_le (lt_add_of_pos_right R₃ zero_lt_one) hzR₃)
    have hzEqNF : toMeromorphicNFOn f Set.univ z = f z := by
      calc
        toMeromorphicNFOn f Set.univ z = toMeromorphicNFAt f z z := by
          rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf.meromorphicOn (by simp)]
        _ = f z := by
          exact congrFun (toMeromorphicNFAt_eq_self.2 hzNF) z
    have hg_eq : g₀ z = h₀ z := hg₀_eq hq₀_nonroot
    have hzpow :
        ‖z‖ ^ q₀.natDegree * ‖z‖ ^ n₁ = ‖z‖ ^ ((q₀.natDegree : ℤ) + n₁) := by
      calc
        ‖z‖ ^ q₀.natDegree * ‖z‖ ^ n₁ = ‖z‖ ^ ((q₀.natDegree : ℤ)) * ‖z‖ ^ n₁ := by
          rw [zpow_natCast]
        _ = ‖z‖ ^ ((q₀.natDegree : ℤ) + n₁) := by
          rw [← zpow_add₀ (norm_ne_zero_iff.2 hz0)]
    calc
      ‖g₀ z‖ = ‖h₀ z‖ := by rw [hg_eq]
      _ = ‖q₀.eval z * toMeromorphicNFOn f Set.univ z‖ := by rfl
      _ = ‖q₀.eval z‖ * ‖f z‖ := by rw [hzEqNF, norm_mul]
      _ ≤ (M₂ * ‖z‖ ^ q₀.natDegree) * (M₁ * ‖z‖ ^ n₁) := by
        gcongr
        · exact hq_bound z hz_one
        · exact hf_bound z hzR₁
      _ = (M₂ * M₁) * ‖z‖ ^ ((q₀.natDegree : ℤ) + n₁) := by
        calc
          (M₂ * ‖z‖ ^ q₀.natDegree) * (M₁ * ‖z‖ ^ n₁)
              = (M₂ * M₁) * (‖z‖ ^ q₀.natDegree * ‖z‖ ^ n₁) := by ring
          _ = (M₂ * M₁) * ‖z‖ ^ ((q₀.natDegree : ℤ) + n₁) := by rw [hzpow]

/-- Exercise 18 (2): if `f : ℂ → ℂ` is meromorphic on `ℂ` and also meromorphic at infinity, then
`f` is represented by a quotient of complex polynomials away from the zeros of the denominator, and
every pole lies among those zeros. -/
theorem exists_polynomial_quotient_of_meromorphic_on_riemann_sphere
    {f : ℂ → ℂ} (hf : Meromorphic f) (hinfty : MeromorphicAtInfinity f) :
    ∃ p q : Polynomial ℂ, q ≠ 0 ∧
      Set.EqOn f (fun z ↦ p.eval z / q.eval z) {z | ¬ q.IsRoot z} ∧
      {z : ℂ | meromorphicOrderAt f z < 0} ⊆ {z | q.IsRoot z} := by
  have hfin_neg : ((divisor f Set.univ)⁻).support.Finite :=
    finite_support_neg_divisor_of_meromorphic_on_riemann_sphere hf hinfty
  rcases exists_polynomial_realizing_negative_divisor_part hfin_neg with
    ⟨q₀, hq₀_ne, hq₀_eval, hq₀_divisor⟩
  let h₀ : ℂ → ℂ := fun z ↦ q₀.eval z * toMeromorphicNFOn f Set.univ z
  let g₀ : ℂ → ℂ := toMeromorphicNFOn h₀ Set.univ
  have hg₀_analytic :
      AnalyticOnNhd ℂ g₀ Set.univ := by
    -- The divisor computation shows the pole-cleared canonical representative is entire.
    simpa [h₀, g₀] using
      (analyticOnNhd_pole_cleared_normal_form_extension hf hfin_neg hq₀_eval).1
  have hg₀_eq :
      Set.EqOn g₀ h₀ {z | ¬ q₀.IsRoot z} := by
    -- Off the zeros of `q₀`, the canonical representative agrees with the raw pole-cleared product.
    simpa [h₀, g₀] using
      (analyticOnNhd_pole_cleared_normal_form_extension hf hfin_neg hq₀_eval).2
  have hg₀_growth :
      ∃ n : ℤ, ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
        ∀ z : ℂ, R ≤ ‖z‖ → ‖g₀ z‖ ≤ M * ‖z‖ ^ n := by
    simpa [h₀, g₀] using
      pole_cleared_numerator_exterior_norm_le_mul_zpow hf hinfty hfin_neg hq₀_eval
  rcases hg₀_growth with ⟨n₀, R₀, M₀, hR₀pos, hM₀nonneg, hg₀_bound⟩
  have hg₀_diff : Differentiable ℂ g₀ := by
    simpa using (Complex.analyticOnNhd_univ_iff_differentiable.mp hg₀_analytic)
  obtain ⟨p₀, hp₀_eval⟩ :=
    exists_polynomial_of_entire_norm_le_mul_zpow_local hg₀_diff (n := n₀) (R := R₀) (M := M₀)
      hg₀_bound
  have hdiscrepancy :
      {z : ℂ | toMeromorphicNFOn f Set.univ z ≠ f z}.Finite :=
    finite_discrepancy_set_toMeromorphicNFOn_of_meromorphic_on_riemann_sphere hf hinfty
  obtain ⟨r, hr_ne, hr_roots⟩ := exists_polynomial_vanishing_on_finite_set hdiscrepancy
  let p : Polynomial ℂ := r * p₀
  let q : Polynomial ℂ := r * q₀
  refine ⟨p, q, mul_ne_zero hr_ne hq₀_ne, ?_, ?_⟩
  · intro z hz
    have hq_nonroot : ¬ q.IsRoot z := hz
    have hr_nonroot : ¬ r.IsRoot z := by
      intro hrz
      have hr_eval_zero : r.eval z = 0 := by
        simpa [Polynomial.IsRoot] using hrz
      have hqz : q.IsRoot z := by
        simpa [q, Polynomial.IsRoot, Polynomial.eval_mul, hr_eval_zero]
      exact hq_nonroot hqz
    have hq₀_nonroot : ¬ q₀.IsRoot z := by
      intro hq₀z
      have hq₀_eval_zero : q₀.eval z = 0 := by
        simpa [Polynomial.IsRoot] using hq₀z
      have hqz : q.IsRoot z := by
        simpa [q, Polynomial.IsRoot, Polynomial.eval_mul, hq₀_eval_zero]
      exact hq_nonroot hqz
    have hz_discrepancy : toMeromorphicNFOn f Set.univ z = f z := by
      by_contra hneq
      have hzmem : z ∈ {z : ℂ | toMeromorphicNFOn f Set.univ z ≠ f z} := hneq
      have hrz : r.IsRoot z := hr_roots hzmem
      exact hr_nonroot hrz
    have hg₀z : g₀ z = q₀.eval z * f z := by
      calc
        g₀ z = h₀ z := hg₀_eq hq₀_nonroot
        _ = q₀.eval z * toMeromorphicNFOn f Set.univ z := by rfl
        _ = q₀.eval z * f z := by rw [hz_discrepancy]
    have hq_eval_ne : q.eval z ≠ 0 := by
      simpa [Polynomial.IsRoot] using hq_nonroot
    have hr_eval_ne : r.eval z ≠ 0 := by
      simpa [Polynomial.IsRoot] using hr_nonroot
    have hq₀_eval_ne : q₀.eval z ≠ 0 := by
      simpa [Polynomial.IsRoot] using hq₀_nonroot
    have hpz : p₀.eval z = q₀.eval z * f z := by
      calc
        p₀.eval z = g₀ z := (hp₀_eval z).symm
        _ = q₀.eval z * f z := hg₀z
    have hmul : p.eval z = q.eval z * f z := by
      calc
        p.eval z = r.eval z * p₀.eval z := by simp [p, Polynomial.eval_mul]
        _ = r.eval z * (q₀.eval z * f z) := by rw [hpz]
        _ = (r.eval z * q₀.eval z) * f z := by ring
        _ = q.eval z * f z := by simp [q, Polynomial.eval_mul, mul_assoc]
    have hdiv : f z = p.eval z / q.eval z := by
      apply (eq_div_iff hq_eval_ne).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.symm
    simpa [p, q] using hdiv
  · intro z hz
    have hzq₀ : q₀.IsRoot z := pole_set_subset_isRoot_of_negative_divisor_denominator hf hq₀_divisor hz
    have hzq₀_eval : q₀.eval z = 0 := by
      simpa [Polynomial.IsRoot] using hzq₀
    show q.IsRoot z
    simpa [q, Polynomial.IsRoot, Polynomial.eval_mul, hzq₀_eval]

end
