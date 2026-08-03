import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: for each `ε > 0`, Corollary 11.16 gives a minimizer `z` of
-- `x ↦ f x + ε * ‖x‖`. Fermat's rule from Theorem 16.3 yields
-- `0 ∈ (∂ (pointwiseAdd f (ε • normFunctionIoi))) z`, Corollary 16.48 splits this
-- subdifferential as a sum, and Example 16.32 identifies the norm subdifferential with the closed
-- unit ball. Hence for every `ε > 0` there is `u ∈ SetValuedOperator.range (∂ f)` with
-- `‖u‖ ≤ ε`, which implies `0 ∈ closure (SetValuedOperator.range (∂ f))`.
/- Source/core/bridge triage:
- `source-facing`: the printed proof and surrounding prose for Corollary 16.52 only justify the
  closure statement `0 ∈ closure (ran ∂ f)`, so the numbered entry must live directly at
  `closure (SetValuedOperator.range (∂ f))`.
- `core/canonical`: the owner objects are `∂ f`, `SetValuedOperator.range`, `closure`, and the
  canonical `EReal` coercion `f.asEReal`.
- `bridge/view`: no extra bridge owner is needed; the source-facing statement is already expressed
  directly in the canonical owner language.
-/
/-- Corollary 16 52: if `f ∈ Γ₀(H)` is bounded below, then `0` belongs to the closure of the
range of its subdifferential. -/
theorem zero_mem_closure_range_subdifferential_of_mem_gammaZero_of_bddBelow
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hbounded : BddBelow (Set.range f)) :
    (0 : H) ∈ closure (SetValuedOperator.range (∂ f)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases hf.2.nonempty with ⟨p, hp⟩
  rcases hbounded with ⟨η, hη⟩
  have hηp : (η : EReal) ≤ (f p : EReal) := hη ⟨p, rfl⟩
  have hp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hηp_real : (η : EReal).toReal ≤ (f p : EReal).toReal := by
    exact EReal.toReal_le_toReal hηp (ne_of_gt η.2) hp_top
  let C : ℝ := 2 * ((f p : EReal).toReal - (η : EReal).toReal) + ‖p‖ ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [hηp_real, sq_nonneg ‖p‖]
  let γ : PosReal := ⟨C / ε ^ 2 + 1, by positivity⟩
  let q : H := Prox[γ, f, hf] 0
  have hprox : IsProxPoint (γ • f) (0 : H) q := by
    simpa [q] using
      proximityOperator_isProxPoint
        (γ • f)
        (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ))
        (0 : H)
  have hmin : proximalObjective (γ • f) 0 q ≤ proximalObjective (γ • f) 0 p := by
    rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hprox
    exact hprox p
  have hp_scaled_lt_top : ((γ • f) p : EReal) < ⊤ := by
    rw [posReal_smul_apply, lt_top_iff_ne_top, EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
        Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hp_top⟩
  have hp_obj_lt_top : proximalObjective (γ • f) 0 p < ⊤ := by
    exact
      EReal.add_lt_top
        (by simpa [proximalObjective] using hp_scaled_lt_top.ne)
        (EReal.coe_ne_top ((1 / 2 : ℝ) * ‖(0 : H) - p‖ ^ 2))
  have hq_obj_lt_top : proximalObjective (γ • f) 0 q < ⊤ := lt_of_le_of_lt hmin hp_obj_lt_top
  have hq_dom : q ∈ effectiveDomain f := by
    by_contra hq_dom
    have hq_top : (f q : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hq_dom))
    have hq_scaled_top : ((γ • f) q : EReal) = ⊤ := by
      rw [posReal_smul_apply, hq_top]
      simpa using EReal.coe_mul_top_of_pos γ.2
    have hq_obj_top : proximalObjective (γ • f) 0 q = ⊤ := by
      rw [proximalObjective, hq_scaled_top]
      rw [EReal.top_add_coe]
    have hfalse : ¬ ((⊤ : EReal) < ⊤) := lt_irrefl _
    rw [hq_obj_top] at hq_obj_lt_top
    exact hfalse hq_obj_lt_top
  have hq_top : (f q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq_dom)
  have hq_bot : (f q : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f q : EReal) from (f q).2)
  have hvar :=
    (isProxPoint_iff_forall_inner_add_le (γ • f) (smul_mem_gammaZero f hf γ).2 (0 : H) q).1 hprox
  let u : H := (γ : ℝ)⁻¹ • (-q)
  have hu : u ∈ (∂ f) q := by
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy : y ∈ effectiveDomain f
    · have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
      have hy_bot : (f y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
      have hvar_real :
          inner ℝ (y - q) (-q) + (γ : ℝ) * (f q : EReal).toReal ≤
            (γ : ℝ) * (f y : EReal).toReal := by
        have hcast :
            (((inner ℝ (y - q) (-q) + (γ : ℝ) * (f q : EReal).toReal : ℝ) : EReal)) ≤
              (((γ : ℝ) * (f y : EReal).toReal : ℝ) : EReal) := by
          simpa [posReal_smul_apply, Function.toEReal_apply, EReal.coe_add, EReal.coe_mul,
            EReal.coe_toReal hq_top hq_bot, EReal.coe_toReal hy_top hy_bot] using hvar y
        exact EReal.coe_le_coe_iff.mp hcast
      have hdiv :
          inner ℝ (y - q) u + (f q : EReal).toReal ≤ (f y : EReal).toReal := by
        have hdiv' :
            (inner ℝ (y - q) (-q) + (γ : ℝ) * (f q : EReal).toReal) / (γ : ℝ) ≤
              (f y : EReal).toReal := by
          have hvar_real' :
              inner ℝ (y - q) (-q) + (γ : ℝ) * (f q : EReal).toReal ≤
                (f y : EReal).toReal * (γ : ℝ) := by
            simpa [mul_comm] using hvar_real
          exact (div_le_iff₀ γ.2).2 hvar_real'
        have hleft :
            (inner ℝ (y - q) (-q) + (γ : ℝ) * (f q : EReal).toReal) / (γ : ℝ) =
              inner ℝ (y - q) u + (f q : EReal).toReal := by
          dsimp [u]
          rw [inner_smul_right]
          field_simp [γ.2.ne']
        rw [hleft] at hdiv'
        exact hdiv'
      have hcast :
          (((inner ℝ (y - q) u + (f q : EReal).toReal : ℝ) : EReal)) ≤
            (((f y : EReal).toReal : ℝ) : EReal) := by
        exact_mod_cast hdiv
      simpa [EReal.coe_add, EReal.coe_toReal hq_top hq_bot, EReal.coe_toReal hy_top hy_bot] using
        hcast
    · have hy_top : (f y : EReal) = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
      change (⟪y - q, u⟫_ℝ : EReal) + (f q : EReal) ≤ (f y : EReal)
      rw [hy_top]
      exact le_top
  have hu_range : u ∈ SetValuedOperator.range (∂ f) := by
    rw [SetValuedOperator.mem_range_iff]
    exact ⟨q, hu⟩
  have hmin_real :
      (γ : ℝ) * (f q : EReal).toReal + (1 / 2 : ℝ) * ‖q‖ ^ 2 ≤
        (γ : ℝ) * (f p : EReal).toReal + (1 / 2 : ℝ) * ‖p‖ ^ 2 := by
    have hcast :
        (((γ : ℝ) * (f q : EReal).toReal + (1 / 2 : ℝ) * ‖q‖ ^ 2 : ℝ) : EReal) ≤
          (((γ : ℝ) * (f p : EReal).toReal + (1 / 2 : ℝ) * ‖p‖ ^ 2 : ℝ) : EReal) := by
      simpa [proximalObjective, posReal_smul_apply, Function.toEReal_apply,
        EReal.coe_add, EReal.coe_mul, EReal.coe_toReal hq_top hq_bot,
        EReal.coe_toReal hp_top hp_bot] using hmin
    exact EReal.coe_le_coe_iff.mp hcast
  have hηq : (η : EReal) ≤ (f q : EReal) := hη ⟨q, rfl⟩
  have hηq_real : (η : EReal).toReal ≤ (f q : EReal).toReal := by
    exact EReal.toReal_le_toReal hηq (ne_of_gt η.2) hq_top
  have hγ_ge_one : 1 ≤ (γ : ℝ) := by
    dsimp [γ]
    have hfrac_nonneg : 0 ≤ C / ε ^ 2 := by
      positivity
    linarith
  have hq_sq_le : ‖q‖ ^ 2 ≤ (γ : ℝ) * C := by
    dsimp [C]
    nlinarith [hmin_real, hηq_real, hγ_ge_one]
  have hu_sq_le : ‖u‖ ^ 2 ≤ C / (γ : ℝ) := by
    have hunorm : ‖u‖ = (γ : ℝ)⁻¹ * ‖q‖ := by
      dsimp [u]
      rw [norm_smul, norm_neg]
      have hγinv_nonneg : 0 ≤ (γ : ℝ)⁻¹ := inv_nonneg.mpr γ.2.le
      rw [Real.norm_eq_abs, abs_of_nonneg hγinv_nonneg]
    have hu_sq_eq : ‖u‖ ^ 2 = ‖q‖ ^ 2 / (γ : ℝ) ^ 2 := by
      rw [hunorm]
      field_simp [γ.2.ne']
    rw [hu_sq_eq]
    have hγsq_pos : 0 < (γ : ℝ) ^ 2 := sq_pos_of_pos γ.2
    refine (div_le_iff₀ hγsq_pos).2 ?_
    have hq_sq_le' : ‖q‖ ^ 2 ≤ C * (γ : ℝ) := by
      simpa [mul_comm] using hq_sq_le
    have hEq : C * (γ : ℝ) = C / (γ : ℝ) * (γ : ℝ) ^ 2 := by
      field_simp [γ.2.ne']
    exact hEq ▸ hq_sq_le'
  have hC_div_lt : C / (γ : ℝ) < ε ^ 2 := by
    dsimp [γ]
    have hden_pos : 0 < C / ε ^ 2 + 1 := by positivity
    refine (div_lt_iff₀ hden_pos).2 ?_
    have hrewrite : ε ^ 2 * (C / ε ^ 2 + 1) = C + ε ^ 2 := by
      field_simp [ne_of_gt hε]
    rw [hrewrite]
    nlinarith [hε, hC_nonneg]
  have hu_norm_lt : ‖u‖ < ε := by
    have hu_sq_lt : ‖u‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt hu_sq_le hC_div_lt
    nlinarith [hu_sq_lt, norm_nonneg u]
  exact ⟨u, hu_range, by simpa [dist_eq_norm] using hu_norm_lt⟩

end SubdifferentialCalculus

end ERealFunction
