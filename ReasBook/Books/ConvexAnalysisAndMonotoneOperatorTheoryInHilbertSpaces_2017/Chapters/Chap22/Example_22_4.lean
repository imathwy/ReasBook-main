import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap22.Definition_22_1

open scoped InnerProductSpace

universe u

namespace ERealFunction

-- Semantic recall: Chapter 22 already provides the owners
-- `SetValuedOperator.IsParamonotone`, `IsStrictlyMonotone`, `IsUniformlyMonotone`, and
-- `IsStronglyMonotone`; the source-facing proper-convex surface is
-- `ConvexOn f (effectiveDomain f)`, while `UniformlyConvex` and `StronglyConvex` already package
-- that convexity data. For clause (2), strict convexity does not encode the source's properness
-- side condition, so nonempty effective domain remains explicit in the public surface.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 22.4: a graph point of the subdifferential lies over the effective
domain. -/
lemma basepoint_mem_effectiveDomain_of_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) {x u : H}
    (hu : u ∈ (∂ f) x) :
    x ∈ effectiveDomain f := by
  -- Promote the graph point to domain membership and apply Proposition 16.4.
  have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  exact subdifferential_domain_subset_effectiveDomain f hdom hx_dom

/-- Helper for Example 22.4: a subgradient bounds the secant slope to any effective-domain point
by the corresponding value difference. -/
lemma cross_subgradient_le_value_diff
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) {x y u : H}
    (hu : u ∈ (∂ f) x) (hy : y ∈ effectiveDomain f) :
    ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
  -- Rewrite the active fiber as the intersection of the affine half-spaces over the effective
  -- domain and evaluate it at `y`.
  have hx : x ∈ effectiveDomain f :=
    basepoint_mem_effectiveDomain_of_mem_subdifferential hdom hu
  rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hu
  exact hu y hy

/-- Helper for Example 22.4: a positive weighted family `(1 - α) c ≤ d` on the open unit interval
already forces the endpoint inequality `c ≤ d`. -/
lemma weighted_open_unit_le_limit {c d : ℝ} (hc : 0 ≤ c)
    (hweight : ∀ {α : ℝ}, 0 < α → α < 1 → (1 - α) * c ≤ d) :
    c ≤ d := by
  by_cases hc0 : c = 0
  · -- When `c = 0`, the endpoint inequality is immediate from the assumed nonnegativity.
    subst hc0
    have hhalf :=
      hweight (show 0 < (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    nlinarith
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    by_contra hcd
    have hdc : d < c := lt_of_not_ge hcd
    let α : ℝ := (c - d) / (2 * c)
    -- Choose an explicit point of the open unit interval witnessing that `(1 - α) * c` stays
    -- strictly above `d`.
    have hα0 : 0 < α := by
      dsimp [α]
      have hnum : 0 < c - d := by
        linarith
      have hden : 0 < 2 * c := by
        nlinarith
      exact div_pos hnum hden
    have hα1 : α < 1 := by
      dsimp [α]
      have hden : 0 < 2 * c := by
        nlinarith
      have hhalf :=
        hweight (show 0 < (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
      have hd_nonneg : 0 ≤ d := by
        nlinarith
      have hlt : c - d < 2 * c := by
        nlinarith
      exact (div_lt_iff₀ hden).2 (by simpa [mul_comm] using hlt)
    have hineq := hweight hα0 hα1
    have hαeq : (1 - α) * c = (c + d) / 2 := by
      dsimp [α]
      field_simp [hcpos.ne']
      ring
    rw [hαeq] at hineq
    linarith

/-- Helper for Example 22.4: on an effective-domain secant, a uniformly convex modulus takes a
finite value. -/
lemma modulus_value_lt_top_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (huniform : UniformlyConvex f φ)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    φ ‖x - y‖₊ < ⊤ := by
  let α : ℝ := 1 / 2
  have hα0 : 0 < α := by
    dsimp [α]
    norm_num
  have hα1 : α < 1 := by
    dsimp [α]
    norm_num
  have hsegment :
      x + α • (y - x) ∈ effectiveDomain f := by
    -- Convexity keeps the midpoint of the secant inside the effective domain.
    have hconvex : Convex ℝ (effectiveDomain f) := huniform.convexOn.convex_effectiveDomain
    exact hconvex.add_smul_sub_mem hx hy ⟨hα0.le, hα1.le⟩
  have hnorm : ‖y - x‖₊ = ‖x - y‖₊ := by
    simpa [sub_eq_add_neg, add_comm] using nnnorm_neg (x - y)
  have hineq_raw :
      (f (x + α • (y - x)) : EReal) +
          (((α * (1 - α) : ℝ) : EReal) * φ ‖y - x‖₊) ≤
        (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) := by
    -- Evaluate the uniform Jensen inequality at the midpoint of the chord.
    simpa [α, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add, smul_sub]
      using huniform.ineq (x := y) (y := x) hy hx hα0 hα1
  have hineq :
      (f (x + α • (y - x)) : EReal) +
          (((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊) ≤
        (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) := by
    -- Rewrite the secant length into the canonical `‖x - y‖₊` orientation.
    simpa [hnorm] using hineq_raw
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hrhs_ne_top :
      (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) ≠ ⊤ := by
    have hα_nonneg : 0 ≤ (α : EReal) := by
      exact_mod_cast hα0.le
    have h1α0 : 0 < 1 - α := by
      linarith
    have h1α_nonneg : 0 ≤ (1 - α : EReal) := by
      exact_mod_cast h1α0.le
    have hterm1_ne_top : (α : EReal) * (f y : EReal) ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl hα_nonneg, Or.inl (EReal.coe_ne_top α),
        Or.inr hfy_top⟩
    have hterm2_ne_top : (1 - α : EReal) * (f x : EReal) ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl h1α_nonneg,
        Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hfx_top⟩
    exact EReal.add_ne_top hterm1_ne_top hterm2_ne_top
  have hphi_ne_top : φ ‖x - y‖₊ ≠ ⊤ := by
    intro hphi_top
    have hcoeff_pos : 0 < α * (1 - α) := by
      dsimp [α]
      norm_num
    have hmul_top :
        (((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊) = ⊤ := by
      simpa [hphi_top] using
        (EReal.coe_mul_top_of_pos hcoeff_pos :
          (((α * (1 - α) : ℝ) : EReal) * ⊤) = ⊤)
    have hleft_top :
        (f (x + α • (y - x)) : EReal) +
            (((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊) = ⊤ := by
      rw [hmul_top]
      exact EReal.add_top_of_ne_bot
        (ne_of_gt (show (⊥ : EReal) < (f (x + α • (y - x))) from
          (f (x + α • (y - x))).2))
    rw [hleft_top] at hineq
    exact hrhs_ne_top (top_unique hineq)
  exact lt_of_le_of_ne le_top hphi_ne_top

/-- Helper for Example 22.4: strict convexity upgrades the secant bound at a subgradient to a
strict inequality. -/
lemma cross_subgradient_lt_value_diff_of_strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hstrict : StrictlyConvex f)
    {x y v : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hxy : x ≠ y)
    (hv : v ∈ (∂ f) y) :
    ⟪x - y, v⟫_ℝ < (f x : EReal).toReal - (f y : EReal).toReal := by
  let z : H := y + (1 / 2 : ℝ) • (x - y)
  have hdom : (effectiveDomain f).Nonempty := ⟨y, hy⟩
  -- The midpoint stays in the effective domain because strict Jensen bounds it by a finite value.
  have hstrict_mid :
      (f z : EReal) <
        ((1 / 2 : ℝ) : EReal) * (f x : EReal) + (1 - (1 / 2 : ℝ) : EReal) * (f y : EReal) := by
    simpa [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add, smul_sub]
      using
      hstrict.ineq hx hy hxy (show 0 < (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) < 1 by norm_num)
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hweighted_top :
      ((1 / 2 : ℝ) : EReal) * (f x : EReal) + (1 - (1 / 2 : ℝ) : EReal) * (f y : EReal) ≠ ⊤ := by
    have hhalf_x_top : ((1 / 2 : ℝ) : EReal) * (f x : EReal) ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl ?_, Or.inl (EReal.coe_ne_top _), Or.inr hfx_top⟩
      positivity
    have hhalf_y_top : (1 - (1 / 2 : ℝ) : EReal) * (f y : EReal) ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl ?_, Or.inl (EReal.coe_ne_top _), Or.inr hfy_top⟩
      exact_mod_cast (show 0 ≤ 1 - (1 / 2 : ℝ) by norm_num)
    exact EReal.add_ne_top hhalf_x_top hhalf_y_top
  have hz : z ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    refine lt_of_lt_of_le hstrict_mid ?_
    exact (lt_of_le_of_ne le_top hweighted_top).le
  -- Evaluate the subgradient half-space bound at the midpoint and compare it to strict Jensen.
  have hsecant :
      ⟪z - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal :=
    cross_subgradient_le_value_diff hdom hv hz
  have hzy : z - y = (1 / 2 : ℝ) • (x - y) := by
    dsimp [z]
    abel_nf
  have hsecant_half :
      (1 / 2 : ℝ) * ⟪x - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal := by
    simpa [hzy, real_inner_smul_left] using hsecant
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hfz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hfz_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
  have hstrict_mid_real :
      (f z : EReal).toReal <
        ((f x : EReal).toReal + (f y : EReal).toReal) / 2 := by
    have hhalf_sub : (1 - (((1 / 2 : ℝ)) : EReal)) = (((1 / 2 : ℝ)) : EReal) := by
      exact_mod_cast (show (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num)
    have hstrict_mid' := hstrict_mid
    rw [hhalf_sub] at hstrict_mid'
    rw [← EReal.coe_toReal hfz_top hfz_bot, ← EReal.coe_toReal hfx_top hfx_bot,
      ← EReal.coe_toReal hfy_top hfy_bot, ← EReal.coe_mul, ← EReal.coe_mul,
      ← EReal.coe_add] at hstrict_mid'
    have hstrict_mid_half :
        (f z : EReal).toReal <
          (1 / 2 : ℝ) * (f x : EReal).toReal + (1 / 2 : ℝ) * (f y : EReal).toReal := by
      exact_mod_cast hstrict_mid'
    nlinarith
  have hz_bound :
      (f z : EReal).toReal - (f y : EReal).toReal <
        ((f x : EReal).toReal - (f y : EReal).toReal) / 2 := by
    linarith
  have htarget :
      (1 / 2 : ℝ) * ⟪x - y, v⟫_ℝ <
        ((f x : EReal).toReal - (f y : EReal).toReal) / 2 := by
    exact lt_of_le_of_lt hsecant_half hz_bound
  nlinarith

/-- Helper for Example 22.4: uniform convexity yields the one-sided source inequality relating a
subgradient and the modulus term. -/
lemma cross_subgradient_add_modulus_le_value_diff_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (huniform : UniformlyConvex f φ)
    {x y v : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hv : v ∈ (∂ f) y) :
    (φ ‖x - y‖₊).toReal + ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal := by
  let hdom : (effectiveDomain f).Nonempty := huniform.uniformlyConvexOn.nonempty
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hphi_top : φ ‖x - y‖₊ ≠ ⊤ :=
    (modulus_value_lt_top_of_uniformlyConvex huniform hx hy).ne
  have hphi_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ := by
    -- A uniformly convex modulus is increasing and vanishes at `0`, hence nonnegative.
    rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
    exact huniform.monotone bot_le
  have hphi_bot : φ ‖x - y‖₊ ≠ ⊥ := by
    intro hphi_bot
    rw [hphi_bot] at hphi_nonneg
    simp at hphi_nonneg
  have hphi_nonneg_real : 0 ≤ (φ ‖x - y‖₊).toReal := by
    have hcast_nonneg : (((0 : ℝ) : EReal)) ≤ (((φ ‖x - y‖₊).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_toReal hphi_top hphi_bot] using hphi_nonneg
    exact_mod_cast hcast_nonneg
  -- For each `α ∈ (0,1)`, combine the midpoint subgradient estimate with the uniform Jensen
  -- inequality.
  have hweighted :
      ∀ {α : ℝ}, 0 < α → α < 1 →
        (1 - α) * (φ ‖x - y‖₊).toReal + ⟪x - y, v⟫_ℝ ≤
          (f x : EReal).toReal - (f y : EReal).toReal := by
    intro α hα0 hα1
    let z : H := y + α • (x - y)
    have hz : z ∈ effectiveDomain f := by
      -- Convexity keeps the active secant point in the effective domain.
      have hconvex : Convex ℝ (effectiveDomain f) := huniform.convexOn.convex_effectiveDomain
      exact hconvex.add_smul_sub_mem hy hx ⟨hα0.le, hα1.le⟩
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
    have hsecant :
        α * ⟪x - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal := by
      -- Evaluate the subgradient half-space inequality at the secant point `z`.
      have hz_eval :
          ⟪z - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal :=
        cross_subgradient_le_value_diff hdom hv hz
      have hz_sub : z - y = α • (x - y) := by
        dsimp [z]
        abel_nf
      simpa [hz_sub, real_inner_smul_left] using hz_eval
    have huniform_real :
        (f z : EReal).toReal + (α * (1 - α)) * (φ ‖x - y‖₊).toReal ≤
          α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
      -- Rewrite the uniform Jensen inequality inside `ℝ` after proving finiteness.
      have huniform_ereal :
          (f z : EReal) + (((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊) ≤
            (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
        simpa [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add,
          smul_sub]
          using huniform.ineq (x := x) (y := y) hx hy hα0 hα1
      have hcoeff : (1 - (α : EReal)) = ((1 - α : ℝ) : EReal) := by
        exact_mod_cast rfl
      rw [← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_toReal hphi_top hphi_bot,
        ← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hfy_top hfy_bot,
        hcoeff, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        ← EReal.coe_add] at huniform_ereal
      exact_mod_cast huniform_ereal
    have hcombined :
        α * ((1 - α) * (φ ‖x - y‖₊).toReal + ⟪x - y, v⟫_ℝ) ≤
          α * ((f x : EReal).toReal - (f y : EReal).toReal) := by
      nlinarith [hsecant, huniform_real]
    nlinarith [hcombined, hα0]
  -- Let `α ↓ 0` through the algebraic endpoint lemma after isolating the modulus term.
  have hlimit :
      (φ ‖x - y‖₊).toReal ≤
        (f x : EReal).toReal - (f y : EReal).toReal - ⟪x - y, v⟫_ℝ := by
    exact weighted_open_unit_le_limit hphi_nonneg_real (by
      intro α hα0 hα1
      have hα := hweighted hα0 hα1
      linarith)
  linarith

/-- Example 22.4 (1): for a proper convex `]-∞,+∞]`-valued function, the subdifferential is
paramonotone. -/
theorem subdifferential_isParamonotone_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    (∂ f).IsParamonotone := by
  let hdom : (effectiveDomain f).Nonempty := hconv.nonempty
  refine ⟨?_ , ?_⟩
  · -- Monotonicity comes from the two secant bounds centered at `x` and `y`.
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hu hv
    have hrev_u : ⟪y - x, u⟫_ℝ = -⟪x - y, u⟫_ℝ := by
      have hsub : y - x = -(x - y) := by
        abel_nf
      rw [hsub, inner_neg_left]
    have hxuy : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal :=
      cross_subgradient_le_value_diff hdom hu
        (basepoint_mem_effectiveDomain_of_mem_subdifferential hdom hv)
    have hyvx : ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal :=
      cross_subgradient_le_value_diff hdom hv
        (basepoint_mem_effectiveDomain_of_mem_subdifferential hdom hu)
    have hxu :
        (f x : EReal).toReal - (f y : EReal).toReal ≤ ⟪x - y, u⟫_ℝ := by
      linarith
    have hmono : 0 ≤ ⟪x - y, u⟫_ℝ - ⟪x - y, v⟫_ℝ := by
      linarith
    simpa only [inner_sub_right] using hmono
  · intro x u y v hu hv hinner
    have hx : x ∈ effectiveDomain f :=
      basepoint_mem_effectiveDomain_of_mem_subdifferential hdom hu
    have hy : y ∈ effectiveDomain f :=
      basepoint_mem_effectiveDomain_of_mem_subdifferential hdom hv
    have hxyu : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal :=
      cross_subgradient_le_value_diff hdom hu hy
    have hyxv : ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal :=
      cross_subgradient_le_value_diff hdom hv hx
    have hrev_u : ⟪y - x, u⟫_ℝ = -⟪x - y, u⟫_ℝ := by
      have hsub : y - x = -(x - y) := by
        abel_nf
      rw [hsub, inner_neg_left]
    have hrev_v : ⟪y - x, v⟫_ℝ = -⟪x - y, v⟫_ℝ := by
      have hsub : y - x = -(x - y) := by
        abel_nf
      rw [hsub, inner_neg_left]
    have huv_eq : ⟪x - y, u⟫_ℝ = ⟪x - y, v⟫_ℝ := by
      have hinner' : ⟪x - y, u⟫_ℝ - ⟪x - y, v⟫_ℝ = 0 := by
        simpa only [inner_sub_right] using hinner
      linarith
    have hxu_eq :
        ⟪x - y, u⟫_ℝ = (f x : EReal).toReal - (f y : EReal).toReal := by
      linarith
    have hxv_eq :
        ⟪x - y, v⟫_ℝ = (f x : EReal).toReal - (f y : EReal).toReal := by
      linarith
    have hyu_eq :
        ⟪y - x, u⟫_ℝ = (f y : EReal).toReal - (f x : EReal).toReal := by
      linarith
    have hyv_eq :
        ⟪y - x, v⟫_ℝ = (f y : EReal).toReal - (f x : EReal).toReal := by
      linarith
    refine ⟨?_ , ?_⟩
    · -- Replace the base value at `x` using the equality case along the secant to `y`.
      rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂]
      intro z hz
      have hvz : ⟪z - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal :=
        cross_subgradient_le_value_diff hdom hv hz
      have hz_split : z - x = (z - y) + (y - x) := by
        abel_nf
      calc
        ⟪z - x, v⟫_ℝ = ⟪z - y, v⟫_ℝ + ⟪y - x, v⟫_ℝ := by
          rw [hz_split, inner_add_left]
        _ ≤ ((f z : EReal).toReal - (f y : EReal).toReal) +
              ((f y : EReal).toReal - (f x : EReal).toReal) := by
                linarith [hvz, hyv_eq]
        _ = (f z : EReal).toReal - (f x : EReal).toReal := by ring
    · -- The symmetric argument swaps the roles of `(x, u)` and `(y, v)`.
      rw [subdifferential_eq_iInter_affine_halfspaces f y hy, Set.mem_iInter₂]
      intro z hz
      have huz : ⟪z - x, u⟫_ℝ ≤ (f z : EReal).toReal - (f x : EReal).toReal :=
        cross_subgradient_le_value_diff hdom hu hz
      have hz_split : z - y = (z - x) + (x - y) := by
        abel_nf
      calc
        ⟪z - y, u⟫_ℝ = ⟪z - x, u⟫_ℝ + ⟪x - y, u⟫_ℝ := by
          rw [hz_split, inner_add_left]
        _ ≤ ((f z : EReal).toReal - (f x : EReal).toReal) +
              ((f x : EReal).toReal - (f y : EReal).toReal) := by
                linarith [huz, hxu_eq]
        _ = (f z : EReal).toReal - (f y : EReal).toReal := by ring

/-- Example 22.4 (2): if an `]-∞,+∞]`-valued function has nonempty effective domain and is
strictly convex, then its subdifferential is strictly monotone. -/
theorem subdifferential_isStrictlyMonotone_of_strictlyConvex
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty)
    (hstrict : StrictlyConvex f) :
    (∂ f).IsStrictlyMonotone := by
  intro x u y v hu hv hxy
  have hx : x ∈ effectiveDomain f :=
    basepoint_mem_effectiveDomain_of_mem_subdifferential hdom hu
  have hy : y ∈ effectiveDomain f :=
    basepoint_mem_effectiveDomain_of_mem_subdifferential hdom hv
  -- Combine the two strict one-sided secant inequalities at `(x, v)` and `(y, u)`.
  have hxv :
      ⟪x - y, v⟫_ℝ < (f x : EReal).toReal - (f y : EReal).toReal :=
    cross_subgradient_lt_value_diff_of_strictlyConvex hstrict hx hy hxy hv
  have hyu :
      ⟪y - x, u⟫_ℝ < (f y : EReal).toReal - (f x : EReal).toReal :=
    cross_subgradient_lt_value_diff_of_strictlyConvex hstrict hy hx hxy.symm hu
  have hrev_u : ⟪y - x, u⟫_ℝ = -⟪x - y, u⟫_ℝ := by
    have hsub : y - x = -(x - y) := by
      abel_nf
    rw [hsub, inner_neg_left]
  have hpos : 0 < ⟪x - y, u⟫_ℝ - ⟪x - y, v⟫_ℝ := by
    linarith
  simpa only [inner_sub_right] using hpos

/-- Example 22.4 (3): if a proper convex `]-∞,+∞]`-valued function is uniformly convex with
modulus `φ`, then its subdifferential is uniformly monotone with modulus `2φ`. -/
theorem subdifferential_isUniformlyMonotone_of_uniformlyConvex
    (f : H → Set.Ioi (⊥ : EReal)) {φ : NNReal → EReal} (huniform : UniformlyConvex f φ) :
    (∂ f).IsUniformlyMonotone (fun r ↦ (2 : EReal) * φ r) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The doubled modulus stays monotone because `2 ≥ 0`.
    intro r s hrs
    exact mul_le_mul_of_nonneg_left (huniform.monotone hrs) (by norm_num : (0 : EReal) ≤ 2)
  · intro r
    constructor
    · intro hr
      have hphi_nonneg : (0 : EReal) ≤ φ r := by
        rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
        exact huniform.monotone bot_le
      have hphi_top : φ r ≠ ⊤ := by
        intro hphi_top
        rw [hphi_top] at hr
        simp at hr
      have hphi_bot : φ r ≠ ⊥ := by
        intro hphi_bot
        rw [hphi_bot] at hphi_nonneg
        simp at hphi_nonneg
      have hr_real : (2 : ℝ) * (φ r).toReal = 0 := by
        have hr_cast := hr
        rw [show (2 : EReal) = ((2 : ℝ) : EReal) by rfl,
          ← EReal.coe_toReal hphi_top hphi_bot, ← EReal.coe_mul,
          show (0 : EReal) = ((0 : ℝ) : EReal) by norm_num] at hr_cast
        exact_mod_cast hr_cast
      have hphi_zero_real : (φ r).toReal = 0 := by
        linarith
      have hphi_zero : φ r = 0 := by
        calc
          φ r = (((φ r).toReal : ℝ) : EReal) := (EReal.coe_toReal hphi_top hphi_bot).symm
          _ = 0 := by simp [hphi_zero_real]
      exact (huniform.modulus_eq_zero_iff r).1 hphi_zero
    · intro hr
      rw [(huniform.modulus_eq_zero_iff r).2 hr]
      simp
  · intro x u y v hu hv
    have hx : x ∈ effectiveDomain f :=
      basepoint_mem_effectiveDomain_of_mem_subdifferential huniform.uniformlyConvexOn.nonempty hu
    have hy : y ∈ effectiveDomain f :=
      basepoint_mem_effectiveDomain_of_mem_subdifferential huniform.uniformlyConvexOn.nonempty hv
    -- Add the two one-sided uniform bounds and normalize the doubled modulus.
    have hxv :
        (φ ‖x - y‖₊).toReal + ⟪x - y, v⟫_ℝ ≤
          (f x : EReal).toReal - (f y : EReal).toReal :=
      cross_subgradient_add_modulus_le_value_diff_of_uniformlyConvex huniform hx hy hv
    have hyu :
        (φ ‖x - y‖₊).toReal + ⟪y - x, u⟫_ℝ ≤
          (f y : EReal).toReal - (f x : EReal).toReal :=
      by
        have hyu' :=
          cross_subgradient_add_modulus_le_value_diff_of_uniformlyConvex huniform hy hx hu
        have hnorm : ‖y - x‖₊ = ‖x - y‖₊ := by
          simpa [sub_eq_add_neg, add_comm] using nnnorm_neg (x - y)
        simpa [hnorm] using hyu'
    have hpairing :
        (2 : ℝ) * (φ ‖x - y‖₊).toReal ≤ ⟪x - y, u - v⟫_ℝ := by
      have hrev_u : ⟪y - x, u⟫_ℝ = -⟪x - y, u⟫_ℝ := by
        have hsub : y - x = -(x - y) := by
          abel_nf
        rw [hsub, inner_neg_left]
      have hpairing_raw :
          (2 : ℝ) * (φ ‖x - y‖₊).toReal ≤
            ⟪x - y, u⟫_ℝ - ⟪x - y, v⟫_ℝ := by
        linarith [hxv, hyu, hrev_u]
      simpa only [inner_sub_right] using hpairing_raw
    have hphi_top : φ ‖x - y‖₊ ≠ ⊤ :=
      (modulus_value_lt_top_of_uniformlyConvex huniform hx hy).ne
    have hphi_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ := by
      rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
      exact huniform.monotone bot_le
    have hphi_bot : φ ‖x - y‖₊ ≠ ⊥ := by
      intro hphi_bot
      rw [hphi_bot] at hphi_nonneg
      simp at hphi_nonneg
    have hpairing_cast :
        (((2 : ℝ) * (φ ‖x - y‖₊).toReal : ℝ) : EReal) ≤
          (⟪x - y, u - v⟫_ℝ : EReal) := by
      exact_mod_cast hpairing
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) by rfl,
      ← EReal.coe_toReal hphi_top hphi_bot, ← EReal.coe_mul]
    simpa using hpairing_cast

/-- Example 22.4 (4): if a proper convex `]-∞,+∞]`-valued function is strongly convex with
constant `β`, then its subdifferential is strongly monotone with the same constant. -/
theorem subdifferential_isStronglyMonotone_of_stronglyConvex
    (f : H → Set.Ioi (⊥ : EReal)) {β : ℝ} (hstrong : StronglyConvex f β) :
    (∂ f).IsStronglyMonotone β := by
  have huniform :
      (∂ f).IsUniformlyMonotone (fun r ↦ (2 : EReal) * strongConvexityModulus β r) :=
    subdifferential_isUniformlyMonotone_of_uniformlyConvex f hstrong.uniformlyConvex
  refine ⟨hstrong.pos, ?_⟩
  intro x u y v hu hv
  -- Reuse clause (3) with the quadratic modulus and simplify the scalar factor `2 * (β / 2)`.
  have hineq :
      (2 : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
        (⟪x - y, u - v⟫_ℝ : EReal) :=
    huniform.ineq hu hv
  have hnormsq :
      (((β * ‖x - y‖ ^ 2 : ℝ) : EReal)) =
        (2 : EReal) * strongConvexityModulus β ‖x - y‖₊ := by
    calc
      (((β * ‖x - y‖ ^ 2 : ℝ) : EReal))
          = (((2 : ℝ) * ((β / 2 : ℝ) * ‖x - y‖ ^ 2) : ℝ) : EReal) := by
              congr 1
              ring
      _ = (2 : EReal) * (((β / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
            rw [show (2 : EReal) = ((2 : ℝ) : EReal) by rfl, ← EReal.coe_mul]
      _ = (2 : EReal) * strongConvexityModulus β ‖x - y‖₊ := by
            simp [strongConvexityModulus]
  rw [← hnormsq] at hineq
  exact_mod_cast hineq

end ERealFunction
