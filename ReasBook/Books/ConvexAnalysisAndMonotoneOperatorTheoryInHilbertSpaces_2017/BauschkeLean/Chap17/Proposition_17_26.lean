import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap10.Proposition_10_12
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap10.Corollary_10_13
import BauschkeLean.Chap11.Corollary_11_9
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap14.Proposition_14_15
import BauschkeLean.Chap17.Proposition_17_21

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search note: `lean_leansearch` was unavailable in this runner, so the statement
-- surface below was checked against the local Chapter 9, 10, 11, and 17 APIs.

universe u

namespace ERealFunction

section InnerProduct

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 17.26: the exact modulus is strictly positive at radius `1` whenever a
uniform-convex modulus exists. -/
private theorem exact_modulus_one_pos_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) :
    0 < exactModulusOfConvexity f 1 := by
  -- The exact modulus inherits the source zero-set characterization from any uniform-convex
  -- modulus, so positivity at radius `1` reduces to nonnegativity plus exclusion of `0`.
  have hconv : ConvexOn f (effectiveDomain f) := huniform.convexOn
  have hnonneg : 0 ≤ exactModulusOfConvexity f 1 :=
    exactModulusOfConvexity_nonneg f hconv 1
  have hne : exactModulusOfConvexity f 1 ≠ 0 := by
    intro hzero
    have hOneZero : (1 : NNReal) = 0 :=
      (UniformlyConvex.exactModulusOfConvexity_eq_zero_iff huniform 1).1 hzero
    norm_num at hOneZero
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Helper for Proposition 17.26: a uniformly convex modulus takes finite values on effective-domain
pairs, because the Jensen inequality compares it with a finite weighted secant gap. -/
private theorem modulus_value_lt_top_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    φ ‖y - x‖₊ < ⊤ := by
  let α : ℝ := 1 / 2
  have hα0 : 0 < α := by
    dsimp [α]
    norm_num
  have hα1 : α < 1 := by
    dsimp [α]
    norm_num
  have hsegment :
      x + α • (y - x) ∈ effectiveDomain f := by
    -- Convexity keeps the midpoint of the secant segment inside the effective domain.
    have hconvex : Convex ℝ (effectiveDomain f) := huniform.convexOn.convex_effectiveDomain
    exact hconvex.add_smul_sub_mem hx hy ⟨hα0.le, hα1.le⟩
  have hineq :
      (f (x + α • (y - x)) : EReal) +
          (((α * (1 - α) : ℝ) : EReal) * φ ‖y - x‖₊) ≤
        (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) := by
    -- Rewrite the source Jensen combination into the secant-point form `x + α • (y - x)`.
    simpa [α, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add, smul_sub]
      using huniform.ineq (x := y) (y := x) hy hx hα0 hα1
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hrhs_ne_top :
      (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) ≠ ⊤ :=
    by
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
  have hphi_ne_top : φ ‖y - x‖₊ ≠ ⊤ := by
    intro hphi_top
    have hcoeff_pos : 0 < α * (1 - α) := by
      dsimp [α]
      norm_num
    have hmul_top :
        (((α * (1 - α) : ℝ) : EReal) * φ ‖y - x‖₊) = ⊤ := by
      simpa [hphi_top] using
        (EReal.coe_mul_top_of_pos hcoeff_pos :
          (((α * (1 - α) : ℝ) : EReal) * ⊤) = ⊤)
    have hleft_top :
        (f (x + α • (y - x)) : EReal) +
            (((α * (1 - α) : ℝ) : EReal) * φ ‖y - x‖₊) = ⊤ := by
      rw [hmul_top]
      exact EReal.add_top_of_ne_bot (ne_of_gt (show (⊥ : EReal) < (f (x + α • (y - x))) from
        (f (x + α • (y - x))).2))
    rw [hleft_top] at hineq
    exact hrhs_ne_top (top_unique hineq)
  exact lt_of_le_of_ne le_top hphi_ne_top

/-- Helper for Proposition 17.26: uniform convexity gives the source secant-quotient inequality
before taking the right limit at `0`. -/
private theorem uniformlyConvex_secant_quotient_add_scaled_modulus_le
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (((f (x + α • (y - x)) : EReal) - (f x : EReal)) / α) +
        (((1 - α : ℝ) : EReal) * φ ‖y - x‖₊) ≤
      (f y : EReal) - (f x : EReal) := by
  rcases Set.mem_Ioo.mp hα with ⟨hα0, hα1⟩
  let z : H := x + α • (y - x)
  have hz : z ∈ effectiveDomain f := by
    -- Convexity keeps the whole secant segment from `x` to `y` inside the effective domain.
    have hconvex : Convex ℝ (effectiveDomain f) := huniform.convexOn.convex_effectiveDomain
    exact hconvex.add_smul_sub_mem hx hy ⟨hα0.le, hα1.le⟩
  have hsecant :
      (f z : EReal) + (((α * (1 - α) : ℝ) : EReal) * φ ‖y - x‖₊) ≤
        (α : EReal) * (f y : EReal) + (1 - α : EReal) * (f x : EReal) := by
    -- Route correction: use the source Jensen inequality with endpoints swapped so that the
    -- affine point is exactly `x + α • (y - x)`.
    simpa [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add, smul_sub]
      using huniform.ineq (x := y) (y := x) hy hx hα0 hα1
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hz_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hφ_top : φ ‖y - x‖₊ ≠ ⊤ :=
    (modulus_value_lt_top_of_uniformlyConvex huniform hx hy).ne
  have hφ_nonneg : 0 ≤ φ ‖y - x‖₊ := by
    -- A uniformly convex modulus is increasing and vanishes at `0`, hence nonnegative.
    rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
    exact huniform.monotone bot_le
  have hφ_bot : φ ‖y - x‖₊ ≠ ⊥ := by
    intro hφ_bot
    rw [hφ_bot] at hφ_nonneg
    simp at hφ_nonneg
  have hcoeff : (1 - (α : EReal)) = ((1 - α : ℝ) : EReal) := by
    exact_mod_cast rfl
  have hreal_secant :
      (f z : EReal).toReal + (α * (1 - α)) * (φ ‖y - x‖₊).toReal ≤
        α * (f y : EReal).toReal + (1 - α) * (f x : EReal).toReal := by
    -- Rewrite the finite Jensen inequality entirely inside `ℝ`.
    rw [← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_toReal hφ_top hφ_bot,
      ← EReal.coe_toReal hfy_top hfy_bot, ← EReal.coe_toReal hfx_top hfx_bot, hcoeff,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add] at hsecant
    exact_mod_cast hsecant
  have hreal_quot :
      (((f z : EReal).toReal - (f x : EReal).toReal) / α) +
          (1 - α) * (φ ‖y - x‖₊).toReal ≤
        (f y : EReal).toReal - (f x : EReal).toReal := by
    -- First isolate the quotient term, then divide by the positive scalar `α`.
    have hquot_only :
        ((f z : EReal).toReal - (f x : EReal).toReal) / α ≤
          ((f y : EReal).toReal - (f x : EReal).toReal) -
            (1 - α) * (φ ‖y - x‖₊).toReal := by
      refine (div_le_iff₀ hα0).2 ?_
      nlinarith [hreal_secant]
    nlinarith [hquot_only]
  have hquot_eq :
      (((f z : EReal) - (f x : EReal)) / α) +
          (((1 - α : ℝ) : EReal) * φ ‖y - x‖₊) =
        ((((((f z : EReal).toReal - (f x : EReal).toReal) / α) +
            (1 - α) * (φ ‖y - x‖₊).toReal : ℝ)) : EReal) := by
    rw [differenceQuotient_eq_coe_toReal_of_mem_effectiveDomain (f := f) (x := x) (d := y - x)
      hx hα0 hz, ← EReal.coe_toReal hφ_top hφ_bot, ← EReal.coe_mul, ← EReal.coe_add]
    simp [z]
  -- Cast the normalized real secant inequality back to `EReal`.
  rw [hquot_eq, ← EReal.coe_toReal hfy_top hfy_bot, ← EReal.coe_toReal hfx_top hfx_bot,
    ← EReal.coe_sub]
  exact_mod_cast hreal_quot

/-- Helper for Proposition 17.26: multiplying a finite nonnegative `EReal` constant by
`1 - α` tends back to the same constant as `α ↓ 0`. -/
private theorem tendsto_one_sub_mul_const_finite_ereal
    {c : EReal} (hc_fin : c < ⊤) (hc_nonneg : 0 ≤ c) :
    Filter.Tendsto (fun α : ℝ ↦ (((1 - α : ℝ) : EReal) * c))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) := by
  -- Rewrite the finite modulus value through `toReal`, so the right-limit becomes an ordinary real
  -- continuity statement transported back to `EReal`.
  have hc_bot : c ≠ ⊥ := by
    intro hc_bot
    rw [hc_bot] at hc_nonneg
    simp at hc_nonneg
  have hreal :
      Filter.Tendsto (fun α : ℝ ↦ (1 - α) * c.toReal)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c.toReal) := by
    have hcont :
        ContinuousAt (fun α : ℝ ↦ (1 - α) * c.toReal) 0 :=
      ((continuous_const.sub continuous_id).mul continuous_const).continuousAt
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hcast :
      Filter.Tendsto (fun α : ℝ ↦ (((1 - α) * c.toReal : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((c.toReal : ℝ) : EReal))) := by
    exact (continuous_coe_real_ereal.tendsto _).comp hreal
  have hc_eq : (((c.toReal : ℝ) : EReal)) = c := EReal.coe_toReal hc_fin.ne hc_bot
  have hpointwise :
      (fun α : ℝ ↦ (((1 - α : ℝ) : EReal) * c)) =
        (fun α : ℝ ↦ (((1 - α) * c.toReal : ℝ) : EReal)) := by
    funext α
    calc
      (((1 - α : ℝ) : EReal) * c)
          = (((1 - α : ℝ) : EReal) * (((c.toReal : ℝ) : EReal))) := by
              simpa using congrArg (fun z : EReal ↦ (((1 - α : ℝ) : EReal) * z)) hc_eq.symm
      _ = (((1 - α) * c.toReal : ℝ) : EReal) := by rw [← EReal.coe_mul]
  simpa [hpointwise, hc_eq] using hcast

/-- Helper for Proposition 17.26: a global affine lower bound for `f` yields the midpoint lower
bound needed in the source `α = 1 / 2` argument. -/
private theorem linear_lower_bound_at_midpoint_of_affine_lower_bound
    {f : H → Set.Ioi (⊥ : EReal)} {x0 : H} {A C : ℝ}
    (hA : 0 ≤ A)
    (hlower : ∀ z : H, (((-A * ‖z‖ - C : ℝ) : EReal) ≤ (f z : EReal))) :
    ∀ y : H,
      (((-(A / 2) * ‖y‖ - (A * ‖x0‖ / 2 + C) : ℝ) : EReal) ≤
        (f ((1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0) : EReal)) := by
  intro y
  have hmid_norm :
      ‖(1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0‖ ≤ (‖x0‖ + ‖y‖) / 2 := by
    -- Estimate the convex-combination midpoint directly by the triangle inequality.
    calc
      ‖(1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0‖
          ≤ ‖(1 / 2 : ℝ) • y‖ + ‖(1 - 1 / 2 : ℝ) • x0‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖y‖ + (1 / 2 : ℝ) * ‖x0‖ := by
            norm_num [norm_smul]
      _ = (‖x0‖ + ‖y‖) / 2 := by ring
  have hreal :
      -(A / 2) * ‖y‖ - (A * ‖x0‖ / 2 + C) ≤
        -A * ‖(1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0‖ - C := by
    -- The midpoint norm estimate lets us absorb the fixed `x0` contribution into one constant.
    nlinarith [hmid_norm, hA]
  have hcast :
      (((-(A / 2) * ‖y‖ - (A * ‖x0‖ / 2 + C) : ℝ) : EReal)) ≤
        (((-A * ‖(1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0‖ - C : ℝ) : EReal)) := by
    exact_mod_cast hreal
  exact le_trans hcast (hlower ((1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0))

/-- Helper for Proposition 17.26: the midpoint specialization of uniform convexity for the exact
modulus can be rewritten entirely inside `ℝ` once both endpoints lie in the effective domain. -/
private theorem midpoint_exact_modulus_half_gap_toReal
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) {x0 y : H}
    (hx0 : x0 ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    let m := (1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0
    ((1 / 4 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal + (f m : EReal).toReal ≤
      (1 / 2 : ℝ) * (f y : EReal).toReal + (1 / 2 : ℝ) * (f x0 : EReal).toReal) := by
  let m := (1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0
  -- Route correction: extract the midpoint inequality directly from
  -- `UniformlyConvex f (exactModulusOfConvexity f)` and only then rewrite the finite `EReal`
  -- terms back to `ℝ`.
  have hexact : UniformlyConvex f (exactModulusOfConvexity f) := by
    refine (exactModulusOfConvexity_uniformlyConvex_iff huniform.convexOn).2 ?_
    exact UniformlyConvex.exactModulusOfConvexity_eq_zero_iff huniform
  have hm : m ∈ effectiveDomain f := by
    -- The effective domain is convex, so it contains the midpoint of `x0` and `y`.
    have hconv : Convex ℝ (effectiveDomain f) := huniform.convexOn.convex_effectiveDomain
    simpa [m, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add, smul_sub]
      using hconv.add_smul_sub_mem hx0 hy ⟨by norm_num, by norm_num⟩
  have hmidpoint :
      (f m : EReal) + (((1 / 4 : ℝ) : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) ≤
        ((((1 / 2 : ℝ)) : EReal) * (f y : EReal)) +
          ((((1 / 2 : ℝ)) : EReal) * (f x0 : EReal)) := by
    -- Specializing the exact-modulus Jensen inequality at `α = 1 / 2` gives the midpoint gap.
    have hhalf_pos : 0 < (1 / 2 : ℝ) := by norm_num
    have hhalf_lt_one : (1 / 2 : ℝ) < 1 := by norm_num
    have hhalf_sub :
        (1 - (((1 / 2 : ℝ)) : EReal)) = (((1 / 2 : ℝ)) : EReal) := by
      exact_mod_cast (show (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num)
    have hmidpoint_raw :
        (f m : EReal) +
            ((((1 / 2 : ℝ) * (1 - 1 / 2 : ℝ) : ℝ) : EReal) *
              exactModulusOfConvexity f ‖y - x0‖₊) ≤
          ((((1 / 2 : ℝ)) : EReal) * (f y : EReal)) +
            ((1 - (((1 / 2 : ℝ)) : EReal)) * (f x0 : EReal)) := by
      simpa [m, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hexact.ineq (x := y) (y := x0) hy hx0 hhalf_pos hhalf_lt_one
    norm_num at hmidpoint_raw
    calc
      (f m : EReal) + (((1 / 4 : ℝ) : EReal) * exactModulusOfConvexity f ‖y - x0‖₊)
          ≤ ((((1 / 2 : ℝ)) : EReal) * (f y : EReal)) +
              ((1 - (((1 / 2 : ℝ)) : EReal)) * (f x0 : EReal)) := hmidpoint_raw
      _ = ((((1 / 2 : ℝ)) : EReal) * (f y : EReal)) +
            ((((1 / 2 : ℝ)) : EReal) * (f x0 : EReal)) := by rw [hhalf_sub]
  have hm_top : (f m : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hm)
  have hm_bot : (f m : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f m : EReal) from (f m).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hx0_top : (f x0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx0)
  have hx0_bot : (f x0 : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x0 : EReal) from (f x0).2)
  have hφ_top : exactModulusOfConvexity f ‖y - x0‖₊ ≠ ⊤ :=
    (modulus_value_lt_top_of_uniformlyConvex hexact hx0 hy).ne
  have hφ_nonneg : 0 ≤ exactModulusOfConvexity f ‖y - x0‖₊ := by
    -- The exact modulus inherits monotonicity and the zero value at `0`.
    rw [← (hexact.modulus_eq_zero_iff 0).2 rfl]
    exact hexact.monotone bot_le
  have hφ_bot : exactModulusOfConvexity f ‖y - x0‖₊ ≠ ⊥ := by
    intro hφ_bot
    rw [hφ_bot] at hφ_nonneg
    simp at hφ_nonneg
  have hleft_eq :
      (f m : EReal) + (((1 / 4 : ℝ) : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) =
        ((((f m : EReal).toReal +
            (1 / 4 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal : ℝ)) : EReal) := by
    -- Rewrite the finite midpoint value and the finite exact modulus through `toReal`.
    rw [← EReal.coe_toReal hm_top hm_bot, ← EReal.coe_toReal hφ_top hφ_bot,
      ← EReal.coe_mul, ← EReal.coe_add]
    simp
  have hright_eq :
      ((((1 / 2 : ℝ)) : EReal) * (f y : EReal)) +
          ((((1 / 2 : ℝ)) : EReal) * (f x0 : EReal)) =
        ((((1 / 2 : ℝ) * (f y : EReal).toReal +
            (1 / 2 : ℝ) * (f x0 : EReal).toReal : ℝ)) : EReal) := by
    -- The weighted endpoint values are finite because both endpoints lie in the effective domain.
    rw [← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_toReal hx0_top hx0_bot,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  have hleft_bot :
      (f m : EReal) + (((1 / 4 : ℝ) : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) ≠ ⊥ := by
    rw [hleft_eq]
    exact EReal.coe_ne_bot _
  have hright_top :
      ((((1 / 2 : ℝ)) : EReal) * (f y : EReal)) +
          ((((1 / 2 : ℝ)) : EReal) * (f x0 : EReal)) ≠ ⊤ := by
    rw [hright_eq]
    exact ne_of_lt (EReal.coe_lt_top _)
  have hmidpoint_real :
      (f m : EReal).toReal +
          (1 / 4 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal ≤
        (1 / 2 : ℝ) * (f y : EReal).toReal + (1 / 2 : ℝ) * (f x0 : EReal).toReal := by
    have hmidpoint_toReal := EReal.toReal_le_toReal hmidpoint hleft_bot hright_top
    rw [hleft_eq, hright_eq, EReal.toReal_coe, EReal.toReal_coe] at hmidpoint_toReal
    exact hmidpoint_toReal
  simpa [m, add_comm, add_left_comm, add_assoc] using hmidpoint_real

/-- Helper for Proposition 17.26: outside the effective domain, a `]-∞,+∞]`-valued function takes
the value `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∉ effectiveDomain f) :
    (f y : EReal) = ⊤ := by
  -- Outside the effective domain, the codomain constraint leaves `⊤` as the only possible value.
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))

/-- Helper for Proposition 17.26: midpoint uniform convexity together with a global affine lower
bound produces the quantitative tail estimate needed for supercoercivity. -/
private theorem midpoint_exact_modulus_tail_lower_bound
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) :
    ∃ x0 : H, x0 ∈ effectiveDomain f ∧ ∃ A K : ℝ, 0 ≤ A ∧
      ∀ y : H,
        ((((-A * ‖y‖ - K : ℝ) : EReal) +
            ((1 / 2 : EReal) * exactModulusOfConvexity f ‖y - x0‖₊)) ≤
          (f y : EReal)) := by
  have hexact : UniformlyConvex f (exactModulusOfConvexity f) := by
    -- The exact modulus is the canonical source-faithful modulus for the midpoint route.
    refine (exactModulusOfConvexity_uniformlyConvex_iff huniform.convexOn).2 ?_
    exact UniformlyConvex.exactModulusOfConvexity_eq_zero_iff huniform
  rcases hf.2.nonempty with ⟨x0, hx0⟩
  rcases exists_linear_lower_bound_of_mem_gammaZero hf with ⟨A, C, hA, hlower⟩
  refine ⟨x0, hx0, A, A * ‖x0‖ + 2 * C + (f x0 : EReal).toReal, hA, ?_⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · let m : H := (1 / 2 : ℝ) • y + (1 - 1 / 2 : ℝ) • x0
    have hm : m ∈ effectiveDomain f := by
      -- Convexity keeps the source midpoint inside the effective domain.
      have hconv : Convex ℝ (effectiveDomain f) := huniform.convexOn.convex_effectiveDomain
      simpa [m, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add, smul_sub]
        using hconv.add_smul_sub_mem hx0 hy ⟨by norm_num, by norm_num⟩
    have hmidpoint_real :
        (1 / 4 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal + (f m : EReal).toReal ≤
          (1 / 2 : ℝ) * (f y : EReal).toReal + (1 / 2 : ℝ) * (f x0 : EReal).toReal := by
      -- The midpoint helper isolates the finite exact-modulus Jensen gap entirely in `ℝ`.
      simpa [m] using midpoint_exact_modulus_half_gap_toReal huniform hx0 hy
    have hmid_lower :
        -(A / 2) * ‖y‖ - (A * ‖x0‖ / 2 + C) ≤ (f m : EReal).toReal := by
      -- The affine lower bound at the midpoint is converted to `ℝ` using finiteness of `f m`.
      have hm_top : (f m : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hm)
      have hm_bot : (f m : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f m : EReal) from (f m).2)
      have hmid_lowerE :
          (((-(A / 2) * ‖y‖ - (A * ‖x0‖ / 2 + C) : ℝ) : EReal) ≤ (f m : EReal)) :=
        linear_lower_bound_at_midpoint_of_affine_lower_bound (x0 := x0) hA hlower y
      have hmid_lower_toReal :
          (((-(A / 2) * ‖y‖ - (A * ‖x0‖ / 2 + C) : ℝ) : EReal) ≤
            (((f m : EReal).toReal : ℝ) : EReal)) := by
        rw [EReal.coe_toReal hm_top hm_bot]
        exact hmid_lowerE
      exact_mod_cast hmid_lower_toReal
    have hcombined :
        (1 / 4 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal +
            (-(A / 2) * ‖y‖ - (A * ‖x0‖ / 2 + C)) ≤
          (1 / 2 : ℝ) * (f y : EReal).toReal + (1 / 2 : ℝ) * (f x0 : EReal).toReal := by
      -- Insert the midpoint affine lower bound into the midpoint Jensen-gap inequality.
      linarith
    have hfinal_real :
        -A * ‖y‖ - (A * ‖x0‖ + 2 * C + (f x0 : EReal).toReal) +
            (1 / 2 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal ≤
          (f y : EReal).toReal := by
      -- Multiplying by `2` and absorbing the fixed `x0` terms yields the global tail estimate.
      linarith
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hψ_top : exactModulusOfConvexity f ‖y - x0‖₊ ≠ ⊤ :=
      (modulus_value_lt_top_of_uniformlyConvex hexact hx0 hy).ne
    have hψ_nonneg : 0 ≤ exactModulusOfConvexity f ‖y - x0‖₊ :=
      exactModulusOfConvexity_nonneg f huniform.convexOn ‖y - x0‖₊
    have hψ_bot : exactModulusOfConvexity f ‖y - x0‖₊ ≠ ⊥ := by
      intro hψ_bot
      rw [hψ_bot] at hψ_nonneg
      simp at hψ_nonneg
    -- Cast the absorbed real inequality back to `EReal`.
    have hfinal_cast :
        (((-A * ‖y‖ - (A * ‖x0‖ + 2 * C + (f x0 : EReal).toReal) +
            (1 / 2 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal : ℝ) : EReal) ≤
          (f y : EReal)) := by
      rw [← EReal.coe_toReal hy_top hy_bot]
      exact_mod_cast hfinal_real
    have hhalf_eq :
        ((((1 / 2 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal : ℝ) : EReal)) =
          ((1 / 2 : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) := by
      calc
        ((((1 / 2 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal : ℝ) : EReal))
            = (((1 / 2 : ℝ) : EReal) *
                (((exactModulusOfConvexity f ‖y - x0‖₊).toReal : ℝ) : EReal)) := by
                  rw [← EReal.coe_mul]
        _ = (((1 / 2 : ℝ) : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) := by
              rw [EReal.coe_toReal hψ_top hψ_bot]
        _ = ((1 / 2 : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) := rfl
    have hfinal_cast' :
        (((-A * ‖y‖ - (A * ‖x0‖ + 2 * C + (f x0 : EReal).toReal) : ℝ) : EReal) +
            ((((1 / 2 : ℝ) * (exactModulusOfConvexity f ‖y - x0‖₊).toReal : ℝ) : EReal)) ≤
          (f y : EReal)) := by
      simpa [EReal.coe_add] using hfinal_cast
    rw [hhalf_eq] at hfinal_cast'
    exact hfinal_cast'
  · -- Outside the effective domain, the target value is `⊤`, so the tail estimate is immediate.
    rw [value_eq_top_of_not_mem_effectiveDomain (f := f) hy]
    exact le_top

/-- Helper for Proposition 17.26: on the norm-at-infinity filter, large points satisfy the fixed
geometric comparisons needed to turn the midpoint tail estimate into a quotient bound. -/
private theorem eventually_norm_geometry_for_midpoint_tail
    {x0 : H} :
    ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
      0 < ‖y‖ ∧ 1 ≤ ‖y - x0‖ ∧ ‖y‖ ≤ 2 * ‖y - x0‖ := by
  have hlarge :
      ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
        max 1 (2 * ‖x0‖ + 2) ≤ ‖y‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun y : H ↦ ‖y‖)
          (Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop) Filter.atTop).eventually_ge_atTop
        (max 1 (2 * ‖x0‖ + 2))
  filter_upwards [hlarge] with y hy
  have hy_pos : 0 < ‖y‖ := by
    have hy_one : (1 : ℝ) ≤ ‖y‖ := le_trans (le_max_left _ _) hy
    exact lt_of_lt_of_le zero_lt_one hy_one
  have hsub_lower : ‖y‖ - ‖x0‖ ≤ ‖y - x0‖ := norm_sub_norm_le y x0
  have hsub_one : 1 ≤ ‖y - x0‖ := by
    have hy_big : 2 * ‖x0‖ + 2 ≤ ‖y‖ := le_trans (le_max_right _ _) hy
    nlinarith
  have hsub_big : ‖x0‖ + 2 ≤ ‖y - x0‖ := by
    have hy_big : 2 * ‖x0‖ + 2 ≤ ‖y‖ := le_trans (le_max_right _ _) hy
    nlinarith
  have hy_le : ‖y‖ ≤ 2 * ‖y - x0‖ := by
    have hy_big : 2 * ‖x0‖ + 2 ≤ ‖y‖ := le_trans (le_max_right _ _) hy
    nlinarith
  exact ⟨hy_pos, hsub_one, hy_le⟩

/-- Helper for Proposition 17.26: if the exact modulus is already `⊤` at radius `1`, then every
sufficiently large tail radius also has exact modulus `⊤`. -/
private theorem exact_modulus_eventually_top_of_exact_modulus_one_top
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) {x0 : H}
    (h_top : exactModulusOfConvexity f 1 = ⊤) :
    ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
      exactModulusOfConvexity f ‖y - x0‖₊ = ⊤ := by
  filter_upwards [eventually_norm_geometry_for_midpoint_tail (x0 := x0)] with y hy
  rcases hy with ⟨hy_pos, hy_sub_one, hy_le⟩
  let γ : NNReal := ‖y - x0‖₊
  have hγ : (1 : NNReal) ≤ γ := by
    exact_mod_cast hy_sub_one
  have hscale :
      ((((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f 1) ≤
        exactModulusOfConvexity f γ := by
    simpa [γ, mul_comm] using
      exactModulusOfConvexity_mul_ge_sq_mul huniform.convexOn 1 γ hγ
  have hγsq_pos : 0 < (γ : ℝ) ^ (2 : ℕ) := by
    have hγ_pos : 0 < (γ : ℝ) := lt_of_lt_of_le zero_lt_one hγ
    positivity
  have htop_le : (⊤ : EReal) ≤ exactModulusOfConvexity f γ := by
    calc
      ⊤ = ((((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f 1) := by
        rw [h_top]
        simpa using (EReal.coe_mul_top_of_pos hγsq_pos).symm
      _ ≤ exactModulusOfConvexity f γ := hscale
  exact le_antisymm le_top htop_le

/-- Helper for Proposition 17.26: in the finite branch at radius `1`, the exact-modulus midpoint
term dominates a positive quadratic function of `‖y‖` along the norm tail. -/
private theorem half_exact_modulus_tail_ge_quadratic_of_finite_exact_modulus_one
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) {x0 : H}
    (hfin : exactModulusOfConvexity f 1 < ⊤) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
        (((c * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          (1 / 2 : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) := by
  let c : ℝ := (exactModulusOfConvexity f 1).toReal / 8
  have hψ_pos : 0 < exactModulusOfConvexity f 1 :=
    exact_modulus_one_pos_of_uniformlyConvex huniform
  have hψ_bot : exactModulusOfConvexity f 1 ≠ ⊥ := by
    intro hbot
    rw [hbot] at hψ_pos
    simp at hψ_pos
  have hψ_toReal_pos : 0 < (exactModulusOfConvexity f 1).toReal :=
    EReal.toReal_pos hψ_pos hfin.ne
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc_pos, ?_⟩
  filter_upwards [eventually_norm_geometry_for_midpoint_tail (x0 := x0)] with y hy
  rcases hy with ⟨hy_pos, hy_sub_one, hy_le⟩
  let γ : NNReal := ‖y - x0‖₊
  have hγ : (1 : NNReal) ≤ γ := by
    exact_mod_cast hy_sub_one
  have hscale :
      ((((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f 1) ≤
        exactModulusOfConvexity f γ := by
    simpa [γ, mul_comm] using
      exactModulusOfConvexity_mul_ge_sq_mul huniform.convexOn 1 γ hγ
  have hhalf_scale :
      (1 / 2 : EReal) *
          ((((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f 1) ≤
        (1 / 2 : EReal) * exactModulusOfConvexity f γ := by
    have hhalf_nonneg : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
      exact_mod_cast (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
    exact mul_le_mul_of_nonneg_left hscale hhalf_nonneg
  have hreal :
      c * ‖y‖ ^ (2 : ℕ) ≤
        (1 / 2 : ℝ) * (γ : ℝ) ^ (2 : ℕ) * (exactModulusOfConvexity f 1).toReal := by
    -- The tail geometry `‖y‖ ≤ 2 ‖y - x0‖` converts the exact-modulus scaling law into a
    -- quadratic lower bound in `‖y‖`.
    have hsq : ‖y‖ ^ (2 : ℕ) ≤ 4 * (γ : ℝ) ^ (2 : ℕ) := by
      have hγ_eq : (γ : ℝ) = ‖y - x0‖ := by
        rfl
      nlinarith [hy_le]
    dsimp [c]
    nlinarith
  have hcast_real :
      (((c * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
        ((((1 / 2 : ℝ) * (γ : ℝ) ^ (2 : ℕ) *
            (exactModulusOfConvexity f 1).toReal : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hcast :
      (((c * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
        (1 / 2 : EReal) *
          ((((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f 1) := by
    calc
      (((c * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal))
          ≤ ((((1 / 2 : ℝ) * (γ : ℝ) ^ (2 : ℕ) *
                (exactModulusOfConvexity f 1).toReal : ℝ) : EReal)) := hcast_real
      _ = (1 / 2 : EReal) * ((((γ : ℝ) ^ (2 : ℕ)) : EReal) * exactModulusOfConvexity f 1) := by
          rw [EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hfin.ne hψ_bot]
          rw [mul_assoc]
          rfl
  exact le_trans hcast hhalf_scale

/-- Helper for Proposition 17.26: the midpoint tail estimate implies the quotient
`(f y : EReal) / ‖y‖` eventually dominates every real level. -/
private theorem eventually_lt_div_norm_of_midpoint_exact_modulus_tail
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) :
    ∀ ξ : ℝ, ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
      (ξ : EReal) < (f y : EReal) / ‖y‖ := by
  intro ξ
  rcases midpoint_exact_modulus_tail_lower_bound hf huniform with
    ⟨x0, hx0, A, K, hA, htail⟩
  have hnorm :
      ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop, (1 : ℝ) ≤ ‖y‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun y : H ↦ ‖y‖)
          (Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop) Filter.atTop).eventually_ge_atTop 1
  by_cases htop : exactModulusOfConvexity f 1 = ⊤
  · have hexact_top :
        ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
          exactModulusOfConvexity f ‖y - x0‖₊ = ⊤ :=
      exact_modulus_eventually_top_of_exact_modulus_one_top huniform (x0 := x0) htop
    filter_upwards [hexact_top, hnorm] with y hy_exact hy_norm
    have hy_pos : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy_norm
    have hhalf_top :
        ((1 / 2 : EReal) * exactModulusOfConvexity f ‖y - x0‖₊) = ⊤ := by
      rw [hy_exact]
      simpa using (EReal.coe_mul_top_of_pos (by norm_num : 0 < (1 / 2 : ℝ)))
    have hsum_top :
        (((-A * ‖y‖ - K : ℝ) : EReal) +
            ((1 / 2 : EReal) * exactModulusOfConvexity f ‖y - x0‖₊)) = ⊤ := by
      rw [hhalf_top]
      exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
    have hfy_top : (f y : EReal) = ⊤ := by
      have htail_y := htail y
      rw [hsum_top] at htail_y
      exact le_antisymm le_top htail_y
    have hquot_top : (f y : EReal) / ‖y‖ = ⊤ := by
      rw [hfy_top]
      exact EReal.top_div_of_pos_ne_top (by exact_mod_cast hy_pos) (by simp)
    simpa [hquot_top] using (EReal.coe_lt_top ξ)
  · have hfin : exactModulusOfConvexity f 1 < ⊤ := lt_of_le_of_ne le_top htop
    rcases half_exact_modulus_tail_ge_quadratic_of_finite_exact_modulus_one huniform
        (x0 := x0) hfin with ⟨c, hc_pos, hquad⟩
    let R : ℝ := max 1 ((ξ + A + |K| + 1) / c)
    have hR :
        ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop, R ≤ ‖y‖ := by
      exact
        (Filter.tendsto_comap :
          Filter.Tendsto (fun y : H ↦ ‖y‖)
            (Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop) Filter.atTop).eventually_ge_atTop R
    filter_upwards [hquad, hR] with y hquad_y hyR
    have hy_one : (1 : ℝ) ≤ ‖y‖ := le_trans (le_max_left _ _) hyR
    have hy_pos : 0 < ‖y‖ := lt_of_lt_of_le zero_lt_one hy_one
    have hnorm_pos : (0 : EReal) < ‖y‖ := by
      exact_mod_cast hy_pos
    have hlower :
        (((-A * ‖y‖ - K : ℝ) : EReal) + ((c * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          (f y : EReal)) := by
      have hsum :
          (((-A * ‖y‖ - K : ℝ) : EReal) + ((c * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
            (((-A * ‖y‖ - K : ℝ) : EReal) +
              ((1 / 2 : EReal) * exactModulusOfConvexity f ‖y - x0‖₊)) := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left hquad_y (((-A * ‖y‖ - K : ℝ) : EReal))
      exact le_trans hsum (htail y)
    have hbound :
        (((-A * ‖y‖ - K + c * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤ (f y : EReal)) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hlower
    have hlinear : ξ + A + |K| + 1 ≤ c * ‖y‖ := by
      have hdiv : (ξ + A + |K| + 1) / c ≤ ‖y‖ := le_trans (le_max_right _ _) hyR
      simpa [mul_comm] using (div_le_iff₀ hc_pos).1 hdiv
    have hmul_linear :
        (ξ + A + |K| + 1) * ‖y‖ ≤ c * ‖y‖ ^ (2 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_right hlinear (le_of_lt hy_pos)
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hKnorm : K ≤ |K| * ‖y‖ := by
      have hKabs : K ≤ |K| := le_abs_self K
      have habs_mul : |K| ≤ |K| * ‖y‖ := by
        calc
          |K| = |K| * 1 := by ring
          _ ≤ |K| * ‖y‖ := by
            gcongr
      linarith
    have hreal :
        ξ * ‖y‖ < -A * ‖y‖ - K + c * ‖y‖ ^ (2 : ℕ) := by
      nlinarith [hmul_linear, hKnorm, hy_pos]
    have hmul :
        ((ξ : EReal) * ‖y‖) < (f y : EReal) := by
      exact lt_of_lt_of_le (by exact_mod_cast hreal) hbound
    exact (EReal.lt_div_iff hnorm_pos (by simp)).2 hmul

/-- Proposition 17.26 (1): if `f ∈ Γ₀(H)` is uniformly convex with modulus `φ`, then for every
`x, y ∈ effectiveDomain f` one has
`f'(x; y - x) + φ(‖y - x‖) + f(x) ≤ f(y)`. -/
theorem directionalDerivative_add_modulus_add_value_le_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    f′(x; y - x) + φ ‖y - x‖₊ + (f x : EReal) ≤ (f y : EReal) := by
  -- The `Γ₀` hypothesis is part of the source statement, although this step only needs the convex
  -- route already packaged by Proposition 17.21.
  let _ := hf
  -- Route correction: keep the textbook route `(17.32) + α ↓ 0` instead of replacing it by a
  -- different convex-analytic argument. The only extra input is that the modulus term is finite at
  -- the fixed radius `‖y - x‖`.
  let q : ℝ → EReal := fun α ↦ (((f (x + α • (y - x)) : EReal) - (f x : EReal)) / α) +
    (((1 - α : ℝ) : EReal) * φ ‖y - x‖₊)
  have hφ_fin : φ ‖y - x‖₊ < ⊤ :=
    modulus_value_lt_top_of_uniformlyConvex huniform hx hy
  have hφ_nonneg : 0 ≤ φ ‖y - x‖₊ := by
    -- A uniformly convex modulus is monotone and vanishes at `0`, hence is nonnegative.
    rw [← (huniform.modulus_eq_zero_iff 0).2 rfl]
    exact huniform.monotone bot_le
  have hφ_bot : φ ‖y - x‖₊ ≠ ⊥ := by
    intro hφ_bot
    rw [hφ_bot] at hφ_nonneg
    simp at hφ_nonneg
  have hquot_tendsto :
      Filter.Tendsto
        (fun α : ℝ ↦ (((f (x + α • (y - x)) : EReal) - (f x : EReal)) / α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; y - x))) :=
    (hasDirectionalDerivativeAt_directionalDerivative (f := f) huniform.convexOn hx (y - x)).2
  have hmod_tendsto :
      Filter.Tendsto (fun α : ℝ ↦ (((1 - α : ℝ) : EReal) * φ ‖y - x‖₊))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (φ ‖y - x‖₊)) :=
    tendsto_one_sub_mul_const_finite_ereal hφ_fin hφ_nonneg
  have hq_tendsto :
      Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (f′(x; y - x) + φ ‖y - x‖₊)) := by
    -- Addition on `EReal` is continuous at this pair because the modulus limit is finite.
    let addE : EReal × EReal → EReal := fun p ↦ p.1 + p.2
    have hadd :
        ContinuousAt addE (f′(x; y - x), φ ‖y - x‖₊) :=
      EReal.continuousAt_add (p := (f′(x; y - x), φ ‖y - x‖₊))
        (Or.inr hφ_bot) (Or.inr hφ_fin.ne)
    have hpair :
        Filter.Tendsto
          (fun α : ℝ ↦
            ((((f (x + α • (y - x)) : EReal) - (f x : EReal)) / α),
              (((1 - α : ℝ) : EReal) * φ ‖y - x‖₊)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f′(x; y - x), φ ‖y - x‖₊)) :=
      Filter.Tendsto.prodMk_nhds hquot_tendsto hmod_tendsto
    have hcomp := hadd.tendsto.comp hpair
    simpa [q, addE] using hcomp
  have hα_mem :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards
      [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with α hα0 hα1
    exact ⟨hα0, hα1⟩
  have hq_le :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), q α ≤ (f y : EReal) - (f x : EReal) := by
    filter_upwards [hα_mem] with α hα
    exact uniformlyConvex_secant_quotient_add_scaled_modulus_le huniform hx hy hα
  have hlimit_le :
      f′(x; y - x) + φ ‖y - x‖₊ ≤ (f y : EReal) - (f x : EReal) :=
    le_of_tendsto_of_tendsto hq_tendsto tendsto_const_nhds hq_le
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  -- Move the finite base value `f x` back across the difference to recover the source inequality.
  simpa [q, add_assoc] using
    (EReal.le_sub_iff_add_le (.inl hfx_bot) (.inl hfx_top)).1 hlimit_le

/-- Proposition 17.26 (2): if `f ∈ Γ₀(H)` is uniformly convex with modulus `φ`, then `f` is
supercoercive. -/
theorem supercoercive_of_mem_gammaZero_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) :
    Supercoercive f.asEReal := by
  -- Route correction: keep the source midpoint route and only split the exact-modulus endgame
  -- into the `⊤` branch and the finite quadratic-growth branch.
  rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
  exact eventually_lt_div_norm_of_midpoint_exact_modulus_tail hf huniform

end InnerProduct

section RealHilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 17.26 (3): if `f ∈ Γ₀(H)` is uniformly convex with modulus `φ`, then `f` has
exactly one minimizer over `H`. -/
theorem existsUnique_mem_argmin_of_mem_gammaZero_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {φ : NNReal → EReal}
    (huniform : UniformlyConvex f φ) :
    ∃! x : H, x ∈ Argmin f.asEReal := by
  have hargmin_nonempty : (Argmin f.asEReal).Nonempty := by
    -- Part (ii) upgrades the source hypothesis to the coercivity input of Proposition 11.15.
    simpa using
      argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded hf isClosed_univ convex_univ
        Set.univ_nonempty
        (Or.inl <|
          coercive_of_supercoercive
            (supercoercive_of_mem_gammaZero_of_uniformlyConvex hf huniform))
  have hargmin_subsingleton : (Argmin f.asEReal).Subsingleton :=
    argmin_subsingleton_of_nonempty_effectiveDomain_of_strictlyConvex hf.2.nonempty
      huniform.strictlyConvex
  rcases hargmin_nonempty with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hargmin_subsingleton hy hx

end RealHilbert

end ERealFunction
