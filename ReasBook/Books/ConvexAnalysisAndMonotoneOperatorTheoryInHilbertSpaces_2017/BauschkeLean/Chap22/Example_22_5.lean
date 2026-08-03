import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap22.Remark_22_3
import BauschkeLean.Chap22.Example_22_4

open scoped InnerProductSpace

universe u

namespace ERealFunction

-- Source/core/bridge triage:
-- `source-facing`: Example 22.5 concludes that `∂ f` is uniformly monotone on `C`.
-- `core/canonical`: the Chapter 22 owners are `SetValuedOperator.IsUniformlyMonotoneOnWith` and
--   `SetValuedOperator.IsUniformlyMonotoneOn`.
-- `bridge/view`: the explicit modulus `2φ` is the localized witness behind the source-facing
--   owner conclusion, so the second theorem should be only a thin wrapper around the first.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 22.5: on a pair of points of `C`, the localized uniform-convexity modulus
takes a finite value. -/
lemma modulus_value_lt_top_of_uniformlyConvexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (huniform : UniformlyConvexOn f C φ) {x y : H} (hx : x ∈ C) (hy : y ∈ C) :
    φ ‖x - y‖₊ < ⊤ := by
  let α : ℝ := 1 / 2
  have hα0 : 0 < α := by
    dsimp [α]
    norm_num
  have hα1 : α < 1 := by
    dsimp [α]
    norm_num
  have hx_dom : x ∈ effectiveDomain f := huniform.subset_effectiveDomain hx
  have hy_dom : y ∈ effectiveDomain f := huniform.subset_effectiveDomain hy
  have hnorm : ‖y - x‖₊ = ‖x - y‖₊ := by
    simpa [sub_eq_add_neg, add_comm] using nnnorm_neg (x - y)
  -- Evaluate the localized Jensen inequality at the midpoint of the secant through `x` and `y`.
  have hineq_raw :
      (f (x + α • (y - x)) : EReal) +
          (((α * (1 - α) : ℝ) : EReal) * φ ‖y - x‖₊) ≤
        (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) := by
    simpa [α, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add, smul_sub]
      using huniform.ineq (x := y) (y := x) hy hx hα0 hα1
  have hineq :
      (f (x + α • (y - x)) : EReal) +
          (((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊) ≤
        (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) := by
    simpa [hnorm] using hineq_raw
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
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
  -- If the modulus were `⊤`, the left side of Jensen would be `⊤`, contradicting finiteness of
  -- the weighted endpoint values.
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

/-- Helper for Example 22.5: a localized uniform-convexity modulus and a subgradient at `y`
control the secant slope from `y` to `x`. -/
lemma cross_subgradient_add_modulus_le_value_diff_of_uniformlyConvexOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {C : Set H} {φ : NNReal → EReal} (huniform : UniformlyConvexOn f C φ)
    {x y v : H} (hx : x ∈ C) (hy : y ∈ C) (hv : v ∈ (∂ f) y) :
    (φ ‖x - y‖₊).toReal + ⟪x - y, v⟫_ℝ ≤ (f x : EReal).toReal - (f y : EReal).toReal := by
  let hdom : (effectiveDomain f).Nonempty := hconv.nonempty
  have hx_dom : x ∈ effectiveDomain f := huniform.subset_effectiveDomain hx
  have hy_dom : y ∈ effectiveDomain f := huniform.subset_effectiveDomain hy
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hphi_top : φ ‖x - y‖₊ ≠ ⊤ :=
    (modulus_value_lt_top_of_uniformlyConvexOn huniform hx hy).ne
  have hphi_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ := by
    -- The localized modulus is monotone and vanishes at the origin.
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
  -- Compare each interior secant point against the subgradient at `y`, then combine it with the
  -- localized Jensen inequality on `C`.
  have hweighted :
      ∀ {α : ℝ}, 0 < α → α < 1 →
        (1 - α) * (φ ‖x - y‖₊).toReal + ⟪x - y, v⟫_ℝ ≤
          (f x : EReal).toReal - (f y : EReal).toReal := by
    intro α hα0 hα1
    let z : H := y + α • (x - y)
    have hz : z ∈ effectiveDomain f := by
      -- Global convexity on the effective domain keeps the secant point finite.
      have hconvex : Convex ℝ (effectiveDomain f) := hconv.convex_effectiveDomain
      exact hconvex.add_smul_sub_mem hy_dom hx_dom ⟨hα0.le, hα1.le⟩
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
    have hsecant :
        α * ⟪x - y, v⟫_ℝ ≤ (f z : EReal).toReal - (f y : EReal).toReal := by
      -- Rewrite the subgradient bound at `z` into the secant-direction pairing.
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
      -- Cast the localized Jensen inequality from `EReal` to `ℝ` after proving finiteness.
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
  -- Let `α ↓ 0` through the endpoint lemma to isolate the full modulus contribution.
  have hlimit :
      (φ ‖x - y‖₊).toReal ≤
        (f x : EReal).toReal - (f y : EReal).toReal - ⟪x - y, v⟫_ℝ := by
    exact weighted_open_unit_le_limit hphi_nonneg_real (by
      intro α hα0 hα1
      have hα := hweighted hα0 hα1
      linarith)
  linarith

/-- Example 22.5: let `f : ℋ → ]-∞,+∞]` be proper and convex, let `C` be a nonempty subset of
`dom ∂f`, and suppose that `f` is uniformly convex on `C`. Then the subdifferential `∂f` is
uniformly monotone on `C`, witnessed here by the explicit modulus `2φ`. -/
theorem subdifferential_isUniformlyMonotoneOnWith_of_convexOn_of_uniformlyConvexOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {C : Set H} (hC : C ⊆ (∂ f).dom) {φ : NNReal → EReal}
    (huniform : UniformlyConvexOn f C φ) :
    (∂ f).IsUniformlyMonotoneOnWith C (fun r ↦ (2 : EReal) * φ r) := by
  refine ⟨hC, ?_, ?_, ?_⟩
  · -- The localized doubled modulus stays monotone because multiplication by `2` is order
    -- preserving on `EReal`.
    intro r s hrs
    exact mul_le_mul_of_nonneg_left (huniform.monotone hrs) (by norm_num : (0 : EReal) ≤ 2)
  · intro r
    constructor
    · intro hr
      have hr' : (2 : EReal) * φ r = 0 := by
        simpa using hr
      have hphi_nonneg : (0 : EReal) ≤ φ r := by
        -- The original modulus is already monotone and vanishes at the origin.
        rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
        exact huniform.monotone bot_le
      have hphi_top : φ r ≠ ⊤ := by
        intro hphi_top
        simp [hphi_top] at hr'
      have hphi_bot : φ r ≠ ⊥ := by
        intro hphi_bot
        rw [hphi_bot] at hphi_nonneg
        simp at hphi_nonneg
      have hr_real : (2 : ℝ) * (φ r).toReal = 0 := by
        have hr_cast := hr'
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
      have hphi_zero : φ r = 0 := (huniform.modulus_eq_zero_iff r).2 hr
      simp [hphi_zero]
  · intro x u y v hx hy hu hv
    -- Add the two localized one-sided estimates and rewrite them into the monotonicity pairing.
    have hxv :
        (φ ‖x - y‖₊).toReal + ⟪x - y, v⟫_ℝ ≤
          (f x : EReal).toReal - (f y : EReal).toReal :=
      cross_subgradient_add_modulus_le_value_diff_of_uniformlyConvexOn
        f hconv huniform hx hy hv
    have hyu :
        (φ ‖x - y‖₊).toReal + ⟪y - x, u⟫_ℝ ≤
          (f y : EReal).toReal - (f x : EReal).toReal := by
      have hyu' :=
        cross_subgradient_add_modulus_le_value_diff_of_uniformlyConvexOn
          f hconv huniform hy hx hu
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
      (modulus_value_lt_top_of_uniformlyConvexOn huniform hx hy).ne
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
    change (2 : EReal) * φ ‖x - y‖₊ ≤ (⟪x - y, u - v⟫_ℝ : EReal)
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) by rfl,
      ← EReal.coe_toReal hphi_top hphi_bot, ← EReal.coe_mul]
    exact hpairing_cast

/-- Helper for Example 22.5: the source-facing uniformly monotone conclusion follows immediately
from the explicit modulus theorem. -/
theorem subdifferential_isUniformlyMonotoneOn_of_convexOn_of_uniformlyConvexOn
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {C : Set H} (hC : C ⊆ (∂ f).dom) {φ : NNReal → EReal}
    (huniform : UniformlyConvexOn f C φ) :
    (∂ f).IsUniformlyMonotoneOn C := by
  refine ⟨fun r ↦ (2 : EReal) * φ r, ?_⟩
  exact
    subdifferential_isUniformlyMonotoneOnWith_of_convexOn_of_uniformlyConvexOn
      f hconv hC huniform

end ERealFunction
