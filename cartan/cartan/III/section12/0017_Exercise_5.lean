import Mathlib

open Set
open scoped Topology

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the statement
-- surface was chosen by direct mathlib inspection of `AnalyticOnNhd`, the open-mapping API on
-- preconnected sets, and the boundary maximum-modulus API around
-- `Complex.norm_le_of_forall_mem_frontier_norm_le`.

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Exercise 5: analyticity on a neighborhood of `D` restricts to the standard
`DiffContOnCl` package on `U` once `closure U ⊆ D`. -/
lemma diffContOnCl_of_analyticOnNhd_of_closure_subset
    {D U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D)
    (hclosure : closure U ⊆ D) :
    DiffContOnCl ℂ f U := by
  -- We first restrict analyticity to differentiability on `closure U`, then package the result as
  -- the boundary-value owner used by the maximum-modulus theorem.
  exact (hf.differentiableOn.mono hclosure).diffContOnCl

/-- Helper for Exercise 5: if `f` has no zero on `U` and its boundary norm is the positive constant
`c`, then `f` has no zero anywhere on `closure U`. -/
lemma nonvanishing_on_closure_of_nonvanishing_interior_and_positive_frontier_norm
    {U : Set ℂ} {f : ℂ → ℂ} {c : ℝ}
    (hc : 0 < c)
    (hfrontier : EqOn (norm ∘ f) (fun _ ↦ c) (frontier U))
    (hzero_free : ∀ z ∈ U, f z ≠ 0) :
    ∀ z ∈ closure U, f z ≠ 0 := by
  intro z hz hz0
  -- We split closure points into interior points of `U` and boundary points, where the positive
  -- boundary norm rules out vanishing.
  rw [closure_eq_self_union_frontier U, mem_union] at hz
  rcases hz with hz | hz
  · exact hzero_free z hz hz0
  · have hnorm : ‖f z‖ = c := hfrontier hz
    have hc_zero : c = 0 := by
      simpa [hz0] using hnorm.symm
    exact hc.ne' hc_zero

/-- Helper for Exercise 5: if `f` is zero-free on `closure U` and its boundary norm is the positive
constant `c`, then `‖f‖` is already equal to `c` on all of `U`. -/
lemma eqOn_norm_const_of_constant_norm_on_frontier_of_zero_free
    {U : Set ℂ} {f : ℂ → ℂ} {c : ℝ}
    (hU_bounded : Bornology.IsBounded U)
    (hd : DiffContOnCl ℂ f U)
    (hfrontier : EqOn (norm ∘ f) (fun _ ↦ c) (frontier U))
    (hzero_free : ∀ z ∈ closure U, f z ≠ 0) :
    EqOn (norm ∘ f) (fun _ ↦ c) U := by
  intro z hz
  have hz_closure : z ∈ closure U := subset_closure hz
  -- The maximum-modulus theorem gives the upper bound `‖f z‖ ≤ c`.
  have hle : ‖f z‖ ≤ c := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le hU_bounded hd (fun w hw ↦ ?_) hz_closure
    have hw_eq : ‖f w‖ = c := by
      simpa using hfrontier hw
    rw [hw_eq]
  -- Applying the same theorem to `1 / f` gives the reverse inequality.
  have hinv : DiffContOnCl ℂ (fun w ↦ (f w)⁻¹) U := hd.inv hzero_free
  have hle_inv : ‖(f z)⁻¹‖ ≤ c⁻¹ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le hU_bounded hinv (fun w hw ↦ ?_) hz_closure
    have hw_eq : ‖f w‖ = c := by
      simpa using hfrontier hw
    rw [norm_inv, hw_eq]
  have hz_pos : 0 < ‖f z‖ := norm_pos_iff.mpr (hzero_free z hz_closure)
  have hge : c ≤ ‖f z‖ := by
    have hle_one_div : 1 / ‖f z‖ ≤ 1 / c := by
      simpa [one_div, norm_inv] using hle_inv
    exact le_of_one_div_le_one_div hz_pos hle_one_div
  exact le_antisymm hle hge

/-- Exercise 5: if a nonconstant holomorphic function on a connected set `D` has constant
modulus on the frontier of a nonempty open set `D'` whose closure is a compact subset of `D`,
then `f` has a zero in `D'`. -/
theorem exists_zero_of_constant_norm_on_frontier
    {D D' : Set ℂ} {f : ℂ → ℂ}
    (hD_preconnected : IsPreconnected D)
    (hD'_open : IsOpen D') (hD'_nonempty : D'.Nonempty)
    (hD'_closure_compact : IsCompact (closure D'))
    (hD'_closure_subset : closure D' ⊆ D)
    (hf : AnalyticOnNhd ℂ f D)
    (hf_nonconst : ¬ ∃ c : ℂ, EqOn f (fun _ ↦ c) D)
    (hfrontier : ∃ c : ℝ, EqOn (norm ∘ f) (fun _ ↦ c) (frontier D')) :
    ∃ z ∈ D', f z = 0 := by
  rcases hfrontier with ⟨c, hfrontier⟩
  have hD'_bounded : Bornology.IsBounded D' := hD'_closure_compact.isBounded.subset subset_closure
  have hdiff : DiffContOnCl ℂ f D' :=
    diffContOnCl_of_analyticOnNhd_of_closure_subset hf hD'_closure_subset
  have hD'_ne_univ : D' ≠ univ := by
    -- The closure is compact, so `D'` cannot be all of `ℂ`; otherwise `univ` would be bounded.
    intro hD'_eq_univ
    have hbounded_univ : Bornology.IsBounded (univ : Set ℂ) := by
      simpa [hD'_eq_univ] using hD'_closure_compact.isBounded
    exact NormedSpace.unbounded_univ ℂ ℂ hbounded_univ
  have hfrontier_nonempty : (frontier D').Nonempty := by
    exact nonempty_frontier_iff.2 ⟨hD'_nonempty, hD'_ne_univ⟩
  have hc_nonneg : 0 ≤ c := by
    -- A boundary point witnesses that the constant boundary norm cannot be negative.
    rcases hfrontier_nonempty with ⟨w, hw⟩
    have hw_eq : ‖f w‖ = c := by
      simpa using hfrontier hw
    rw [← hw_eq]
    exact norm_nonneg (f w)
  by_contra hnozero
  have hzero_free : ∀ z ∈ D', f z ≠ 0 := by
    intro z hz hz0
    exact hnozero ⟨z, hz, hz0⟩
  rcases lt_or_eq_of_le hc_nonneg with hc_pos | hc_zero
  · have hclosure_zero_free : ∀ z ∈ closure D', f z ≠ 0 :=
      nonvanishing_on_closure_of_nonvanishing_interior_and_positive_frontier_norm
        hc_pos hfrontier hzero_free
    have hnorm_const : EqOn (norm ∘ f) (fun _ ↦ c) D' :=
      eqOn_norm_const_of_constant_norm_on_frontier_of_zero_free
        hD'_bounded hdiff hfrontier hclosure_zero_free
    rcases hD'_nonempty with ⟨z₀, hz₀⟩
    have hz₀D : z₀ ∈ D := hD'_closure_subset (subset_closure hz₀)
    have heq_norm : (norm ∘ f) =ᶠ[𝓝 z₀] (fun _ : ℂ ↦ c) :=
      hnorm_const.eventuallyEq_of_mem (hD'_open.mem_nhds hz₀)
    -- Constant norm on the open set gives a local maximum of `‖f‖` at any interior point.
    have hlocalMax : IsLocalMax (norm ∘ f) z₀ := by
      exact (heq_norm.isLocalMax_iff).2 isLocalMax_const
    have hdiff_eventually : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ f z := by
      -- Analyticity at `z₀` propagates to nearby points, and analytic functions are differentiable.
      filter_upwards [(hf z₀ hz₀D).eventually_analyticAt] with z hz
      exact AnalyticAt.differentiableAt hz
    -- The maximum-modulus principle now forces `f` to be locally constant near `z₀`.
    have heq_local : f =ᶠ[𝓝 z₀] (fun _ : ℂ ↦ f z₀) :=
      Complex.eventually_eq_of_isLocalMax_norm hdiff_eventually hlocalMax
    have hconst : EqOn f (fun _ : ℂ ↦ f z₀) D := by
      simpa using
        (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
          (f := f) (g := fun _ : ℂ ↦ f z₀) (U := D)
          hf analyticOnNhd_const hD_preconnected hz₀D heq_local)
    exact hf_nonconst ⟨f z₀, hconst⟩
  · rcases hD'_nonempty with ⟨z₀, hz₀⟩
    -- If the boundary norm were zero, the maximum-modulus theorem would force a zero inside `D'`.
    have hnorm_le : ‖f z₀‖ ≤ 0 := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le hD'_bounded hdiff (fun w hw ↦ ?_)
        (subset_closure hz₀)
      have hw_eq : ‖f w‖ = c := by
        simpa using hfrontier hw
      rw [hw_eq, hc_zero]
    have hz₀_zero : f z₀ = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm hnorm_le (norm_nonneg _)
    exact hzero_free z₀ hz₀ hz₀_zero
