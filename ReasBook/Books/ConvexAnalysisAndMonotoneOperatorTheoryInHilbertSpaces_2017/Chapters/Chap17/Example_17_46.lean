import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap02.Fact_2_35
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap09.Proposition_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open InnerProductSpace
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private noncomputable def affineInnerSupremumEReal (u : ℕ → H) (α : ℕ → ℝ) : H → EReal :=
  fun x ↦ ⨆ n : ℕ, ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)

-- Proof sketch: every affine term is a finite real number, hence strictly above `⊥`; the supremum
-- of such terms is again strictly above `⊥`.
private theorem affineInnerSupremum_value_mem_Ioi_bot (u : ℕ → H) (α : ℕ → ℝ) (x : H) :
    affineInnerSupremumEReal u α x ∈ Set.Ioi (⊥ : EReal) := by
  -- Every individual affine branch is a finite real number, so it lies strictly above `⊥`.
  rw [affineInnerSupremumEReal]
  refine lt_of_lt_of_le ?_ (le_iSup (fun n : ℕ ↦ ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)) 0)
  exact EReal.bot_lt_coe _

/-- Helper for Example 17 46: the scalar affine map `t ↦ t - c`, viewed in `EReal`, lies in
`Γ(ℝ)`. -/
private theorem real_shift_mem_gamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ Γ(ℝ) := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- Affine scalar maps satisfy Jensen's inequality with equality.
    intro x y a ha0 ha1
    have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
      ring
    have hcoeff :
        (1 - (a : EReal)) = (((1 - a : ℝ) : EReal)) := by
      norm_num
    change (((a * x + (1 - a) * y - c : ℝ) : EReal)) ≤
      (a : EReal) * (((x - c : ℝ) : EReal)) +
        (1 - a : EReal) * (((y - c : ℝ) : EReal))
    rw [hcoeff, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal |>.le
  · -- Continuity of the scalar affine map gives lower semicontinuity after coercion to `EReal`.
    simpa [Function.comp] using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

/-- Helper for Example 17 46: each affine branch of the supremum belongs to `Γ(H)`. -/
private theorem affine_inner_branch_mem_gamma (u : ℕ → H) (α : ℕ → ℝ) (n : ℕ) :
    (fun x : H ↦ ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)) ∈ Γ(H) := by
  -- Precompose the scalar affine map with the continuous linear inner-product functional.
  have hcomp :
      (fun t : ℝ ↦ ((t - α n : ℝ) : EReal)) ∘ innerSL ℝ (u n) ∈ Γ(H) :=
    mem_gamma_comp_continuousLinearMap
      (fun t : ℝ ↦ ((t - α n : ℝ) : EReal))
      (innerSL ℝ (u n))
      (real_shift_mem_gamma (α n))
  simpa [Function.comp, innerSL_apply_apply, real_inner_comm] using hcomp

/-- Helper for Example 17 46: the raw extended-real supremum belongs to `Γ(H)` and is proper when
the offsets are positive. -/
private theorem affineInnerSupremumEReal_mem_gamma_and_proper (u : ℕ → H) (α : ℕ → ℝ)
    (hα_pos : ∀ n : ℕ, 0 < α n) :
    affineInnerSupremumEReal u α ∈ Γ(H) ∧ IsProper (affineInnerSupremumEReal u α) := by
  constructor
  · -- Proposition 9.3 closes `Γ(H)` under countable pointwise suprema.
    simpa [affineInnerSupremumEReal] using
      iSup_mem_gamma
        (fun n x ↦ ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal))
        (affine_inner_branch_mem_gamma u α)
  · -- Properness is the combination of never attaining `⊥` and having a finite value at `0`.
    refine ⟨?_, ?_⟩
    · intro x
      exact ne_of_gt (affineInnerSupremum_value_mem_Ioi_bot u α x)
    · refine ⟨0, ?_⟩
      rw [mem_dom_iff, affineInnerSupremumEReal]
      refine lt_of_le_of_lt ?_ (EReal.coe_lt_top 0)
      refine iSup_le fun n ↦ ?_
      have hneg : -α n ≤ 0 := by
        linarith [hα_pos n]
      simpa using (show (((-α n : ℝ) : EReal)) ≤ (0 : EReal) by
        exact_mod_cast hneg)

/-- Example 17 46: the function `x ↦ supₙ (⟪x, uₙ⟫_ℝ - αₙ)` associated with a sequence of vectors
and real offsets. -/
noncomputable def affineInnerSupremum (u : ℕ → H) (α : ℕ → ℝ) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨affineInnerSupremumEReal u α x, affineInnerSupremum_value_mem_Ioi_bot u α x⟩

/-- Coercing `affineInnerSupremum u α` to `EReal` recovers the defining supremum formula. -/
@[simp] theorem affineInnerSupremum_apply (u : ℕ → H) (α : ℕ → ℝ) (x : H) :
    (affineInnerSupremum u α x : EReal) = ⨆ n : ℕ, ((⟪x, u n⟫_ℝ - α n : ℝ) : EReal) :=
  rfl

-- Proof sketch: each map `x ↦ ⟪x, uₙ⟫ - αₙ` is continuous and convex, so Proposition 9.3 applies
-- to their pointwise supremum. Positivity of the offsets gives a finite value at `0`, hence
-- properness.
/-- The supremum of the affine functionals `x ↦ ⟪x, uₙ⟫_ℝ - αₙ` belongs to `Γ₀(H)` when all
offsets are strictly positive. -/
theorem affineInnerSupremum_mem_gammaZero (u : ℕ → H) (α : ℕ → ℝ)
    (hα_pos : ∀ n : ℕ, 0 < α n) :
    affineInnerSupremum u α ∈ Γ₀(H) := by
  -- Package the raw `Γ(H)` owner through `properIoi`.
  rcases affineInnerSupremumEReal_mem_gamma_and_proper u α hα_pos with ⟨hgamma, hproper⟩
  simpa [affineInnerSupremum, ERealFunction.properIoi] using
    properIoi_mem_gammaZero_of_mem_gamma hproper hgamma

/-- Helper for Example 17 46: under the unit-ball and positivity hypotheses, the affine supremum
is finite everywhere. -/
private theorem affineInnerSupremum_finite (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1) (hα_pos : ∀ n : ℕ, 0 < α n) :
    ∀ x : H, (affineInnerSupremum u α x : EReal) < ⊤ := by
  intro x
  -- Each branch is bounded above by `‖x‖`, so the supremum is finite.
  rw [affineInnerSupremum_apply]
  refine lt_of_le_of_lt ?_ (EReal.coe_lt_top ‖x‖)
  refine iSup_le fun n ↦ ?_
  have hu_le : ‖u n‖ ≤ 1 := le_of_lt (hu_ball n)
  have hinner_le : ⟪x, u n⟫_ℝ ≤ ‖x‖ * ‖u n‖ := real_inner_le_norm x (u n)
  have hmul_le : ‖x‖ * ‖u n‖ ≤ ‖x‖ := by
    nlinarith [norm_nonneg x, hu_le]
  have hbranch_le : ⟪x, u n⟫_ℝ - α n ≤ ‖x‖ := by
    nlinarith [hinner_le, hmul_le, hα_pos n]
  exact_mod_cast hbranch_le

/-- Helper for Example 17 46: each affine branch at `x` is bounded by the full supremum at `y`
plus the displacement norm `‖x - y‖`. -/
private theorem affineInnerSupremum_branch_le_sup_add_norm
    (u : ℕ → H) (α : ℕ → ℝ) (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (n : ℕ) (x y : H) :
    (((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)) ≤
      (affineInnerSupremum u α y : EReal) + ‖x - y‖ := by
  have hu_le : ‖u n‖ ≤ 1 := le_of_lt (hu_ball n)
  have hdiff_le : ⟪x, u n⟫_ℝ - ⟪y, u n⟫_ℝ ≤ ‖x - y‖ := by
    -- Compare the branch increment to the inner product along `x - y` and apply Cauchy-Schwarz.
    calc
      ⟪x, u n⟫_ℝ - ⟪y, u n⟫_ℝ = ⟪x - y, u n⟫_ℝ := by
        simpa using (inner_sub_left x y (u n)).symm
      _ ≤ ‖x - y‖ * ‖u n‖ := real_inner_le_norm (x - y) (u n)
      _ ≤ ‖x - y‖ := by
        nlinarith [norm_nonneg (x - y), hu_le]
  have hbranch_le :
      ⟪x, u n⟫_ℝ - α n ≤ (⟪y, u n⟫_ℝ - α n) + ‖x - y‖ := by
    linarith
  have hbranch_le' :
      (((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)) ≤
        (((⟪y, u n⟫_ℝ - α n + ‖x - y‖ : ℝ) : EReal)) := by
    exact_mod_cast hbranch_le
  calc
    (((⟪x, u n⟫_ℝ - α n : ℝ) : EReal)) ≤
        (((⟪y, u n⟫_ℝ - α n + ‖x - y‖ : ℝ) : EReal)) :=
      hbranch_le'
    _ = (((⟪y, u n⟫_ℝ - α n : ℝ) : EReal)) + ‖x - y‖ := by
      rw [EReal.coe_add]
    _ ≤ (affineInnerSupremum u α y : EReal) + ‖x - y‖ := by
      have hbranch_sup :
          (((⟪y, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ (affineInnerSupremum u α y : EReal) := by
        rw [affineInnerSupremum_apply]
        exact le_iSup (fun k : ℕ ↦ (((⟪y, u k⟫_ℝ - α k : ℝ) : EReal))) n
      simpa [add_comm] using add_le_add_right hbranch_sup ‖x - y‖

/-- Helper for Example 17 46: the one-sided `EReal` comparison upgrades to a real comparison after
coercing with `toReal`. -/
private theorem affineInnerSupremum_toReal_le_toReal_add_norm
    (u : ℕ → H) (α : ℕ → ℝ) (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hα_pos : ∀ n : ℕ, 0 < α n) (x y : H) :
    (affineInnerSupremum u α x : EReal).toReal ≤
      (affineInnerSupremum u α y : EReal).toReal + ‖x - y‖ := by
  have hupper :
      (affineInnerSupremum u α x : EReal) ≤ (affineInnerSupremum u α y : EReal) + ‖x - y‖ := by
    -- Bound each branch at `x` by the full supremum at `y` plus the displacement norm.
    rw [affineInnerSupremum_apply]
    refine iSup_le fun n ↦ ?_
    exact affineInnerSupremum_branch_le_sup_add_norm u α hu_ball n x y
  have hx_bot : (affineInnerSupremum u α x : EReal) ≠ ⊥ := by
    -- The packaged affine supremum never attains `⊥`.
    exact ne_of_gt (affineInnerSupremum_value_mem_Ioi_bot u α x)
  have hy_bot : (affineInnerSupremum u α y : EReal) ≠ ⊥ := by
    exact ne_of_gt (affineInnerSupremum_value_mem_Ioi_bot u α y)
  have hy_top : (affineInnerSupremum u α y : EReal) ≠ ⊤ := by
    exact ne_of_lt (affineInnerSupremum_finite u α hu_ball hα_pos y)
  have hsum_top :
      (affineInnerSupremum u α y : EReal) + ‖x - y‖ ≠ ⊤ := by
    -- Rewrite the sum as a finite real coefficient to show it is not `⊤`.
    rw [← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_add]
    exact EReal.coe_ne_top _
  have hreal :
      (affineInnerSupremum u α x : EReal).toReal ≤
        ((affineInnerSupremum u α y : EReal) + ‖x - y‖).toReal :=
    EReal.toReal_le_toReal hupper hx_bot hsum_top
  rw [EReal.toReal_add hy_top hy_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hreal
  simpa using hreal

/-- Helper for Example 17 46: weak convergence of `uₙ` to `0` and `αₙ → 0` force each scalar
branch `⟪x, uₙ⟫_ℝ - αₙ` to converge to `0`. -/
private theorem tendsto_affine_inner_branch_of_weak_and_null
    (u : ℕ → H) (α : ℕ → ℝ) (x : H)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_zero : Tendsto α atTop (𝓝 0)) :
    Tendsto (fun n ↦ ⟪x, u n⟫_ℝ - α n) atTop (𝓝 0) := by
  have hweak' :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop
        (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa using hweak
  have hinner :
      Tendsto (fun n ↦ ⟪u n, x⟫_ℝ) atTop (𝓝 0) := by
    -- Compose weak convergence with the defining weak-coordinate evaluation at `innerSL ℝ x`.
    have hcoord :
        Continuous fun z : WeakSpace ℝ H ↦
          StrongDual.toWeakDual (innerSL ℝ x) ((toWeakSpace ℝ H).symm z) :=
      WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
        (StrongDual.toWeakDual (innerSL ℝ x))
    simpa [StrongDual.toWeakDual_apply, innerSL_apply_apply, real_inner_comm] using
      (hcoord.tendsto (toWeakSpace ℝ H (0 : H))).comp hweak'
  have hinner' :
      Tendsto (fun n ↦ ⟪x, u n⟫_ℝ) atTop (𝓝 0) := by
    simpa [real_inner_comm] using hinner
  have hneg_alpha :
      Tendsto (fun n ↦ -α n) atTop (𝓝 0) := by
    -- Negation preserves convergence of the null sequence `α`.
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).sub hα_zero
  simpa [sub_eq_add_neg] using hinner'.add hneg_alpha

-- Proof sketch: the unit-ball bound gives
-- `⟪x, uₙ⟫_ℝ - αₙ ≤ ‖x‖ * ‖uₙ‖ < ‖x‖` for every `n`, while positivity of `αₙ` keeps the value at
-- `0` finite. Hence the supremum is finite at every point.
/-- If every `uₙ` lies in the open unit ball and every `αₙ` is positive, then the affine supremum
is finite everywhere. -/
theorem affineInnerSupremum_effectiveDomain_eq_univ (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1) (hα_pos : ∀ n : ℕ, 0 < α n) :
    effectiveDomain (affineInnerSupremum u α) = Set.univ := by
  have hfinite := affineInnerSupremum_finite u α hu_ball hα_pos
  -- Finiteness at every point is exactly full effective domain.
  ext x
  constructor
  · intro _
    simp
  · intro _
    exact mem_effectiveDomain_iff.mpr (hfinite x)

-- Proof sketch: for each `n`, the increment
-- `⟪x, uₙ⟫_ℝ - αₙ - (⟪y, uₙ⟫_ℝ - αₙ) = ⟪x - y, uₙ⟫_ℝ` is bounded by `‖x - y‖ ‖uₙ‖ ≤ ‖x - y‖`.
-- Taking suprema in both directions gives the `1`-Lipschitz estimate.
/-- If every `uₙ` lies in the open unit ball and every `αₙ` is positive, then the real-valued
representative of the affine supremum is `1`-Lipschitz. -/
theorem affineInnerSupremum_lipschitz (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1) (hα_pos : ∀ n : ℕ, 0 < α n) :
    LipschitzWith 1 (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) := by
  -- Convert the one-sided supremum comparison in both directions and then bound the absolute
  -- difference by `‖x - y‖`.
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hxy :
      (affineInnerSupremum u α x : EReal).toReal ≤
        (affineInnerSupremum u α y : EReal).toReal + ‖x - y‖ :=
    affineInnerSupremum_toReal_le_toReal_add_norm u α hu_ball hα_pos x y
  have hyx :
      (affineInnerSupremum u α y : EReal).toReal ≤
        (affineInnerSupremum u α x : EReal).toReal + ‖x - y‖ := by
    -- Swap the roles of `x` and `y`, then use symmetry of the norm.
    have hyx' :=
      affineInnerSupremum_toReal_le_toReal_add_norm u α hu_ball hα_pos y x
    have hnorm : ‖y - x‖ = ‖x - y‖ := by
      simpa [sub_eq_add_neg, add_comm] using norm_neg (x - y)
    simpa [hnorm, add_comm, add_left_comm, add_assoc] using hyx'
  have hupper :
      (affineInnerSupremum u α x : EReal).toReal -
          (affineInnerSupremum u α y : EReal).toReal ≤ ‖x - y‖ := by
    linarith
  have hlower :
      -‖x - y‖ ≤
        (affineInnerSupremum u α x : EReal).toReal -
          (affineInnerSupremum u α y : EReal).toReal := by
    linarith
  have habs :
      |(affineInnerSupremum u α x : EReal).toReal -
          (affineInnerSupremum u α y : EReal).toReal| ≤ ‖x - y‖ :=
    abs_le.mpr ⟨hlower, hupper⟩
  simpa [Real.dist_eq, dist_eq_norm] using habs

-- Proof sketch: at `x = 0`, positivity gives `-αₙ ≤ 0` for every `n`, while `αₙ → 0` shows that
-- the supremum of the values `-αₙ` is at least `0`.
/-- Positive offsets tending to `0` force the affine supremum to vanish at the origin. -/
theorem affineInnerSupremum_zero (u : ℕ → H) (α : ℕ → ℝ)
    (hα_pos : ∀ n : ℕ, 0 < α n) (hα_zero : Tendsto α atTop (𝓝 0)) :
    (affineInnerSupremum u α 0 : EReal) = 0 := by
  have hupper :
      (affineInnerSupremum u α 0 : EReal) ≤ 0 := by
    -- At the origin every branch is `-α n`, hence nonpositive.
    rw [affineInnerSupremum_apply]
    refine iSup_le fun n ↦ ?_
    have hneg : -α n ≤ 0 := by
      linarith [hα_pos n]
    simpa using (show (((-α n : ℝ) : EReal)) ≤ (0 : EReal) by
      exact_mod_cast hneg)
  have hlower : 0 ≤ (affineInnerSupremum u α 0 : EReal) := by
    -- The null-sequence hypothesis forces the branch values `-α n` to approach `0`.
    by_contra hlt
    have hstrict : (affineInnerSupremum u α 0 : EReal) < 0 := lt_of_not_ge hlt
    obtain ⟨ξ, hξ_sup, hξ_zero⟩ := EReal.lt_iff_exists_real_btwn.mp hstrict
    have hξ_neg : ξ < 0 := by
      exact_mod_cast hξ_zero
    have hξ_pos : 0 < -ξ := by
      linarith
    have hneg_alpha_tendsto : Tendsto (fun n ↦ -α n) atTop (𝓝 0) := by
      have hsub :
          Tendsto (fun n ↦ (0 : ℝ) - α n) atTop (𝓝 (0 - 0)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).sub hα_zero
      simpa using hsub
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hneg_alpha_tendsto (-ξ) hξ_pos
    have hNdist : dist (-α N) 0 < -ξ := hN N le_rfl
    have habs : |(-α N : ℝ)| < -ξ := by
      simpa [Real.dist_eq] using hNdist
    have hξ_branch : ξ < -α N := by
      have habs_split := abs_lt.mp habs
      linarith
    have hbranch_le :
        (((-α N : ℝ) : EReal)) ≤ (affineInnerSupremum u α 0 : EReal) := by
      rw [affineInnerSupremum_apply]
      simpa using le_iSup (fun n : ℕ ↦ (((-α n : ℝ) : EReal))) N
    have hξ_le :
        (ξ : EReal) ≤ (affineInnerSupremum u α 0 : EReal) := by
      exact le_trans (by exact_mod_cast hξ_branch.le) hbranch_le
    exact (not_le_of_gt hξ_sup) hξ_le
  exact le_antisymm hupper hlower

-- Proof sketch: weak convergence of `uₙ` to `0` gives
-- `⟪x, uₙ⟫_ℝ - αₙ → 0` whenever `αₙ → 0`, so the supremum is at least this limit.
/-- If `uₙ ⇀ 0` and `αₙ → 0`, then the affine supremum is nonnegative everywhere. -/
theorem affineInnerSupremum_nonneg (u : ℕ → H) (α : ℕ → ℝ)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_zero : Tendsto α atTop (𝓝 0)) :
    ∀ x : H, 0 ≤ (affineInnerSupremum u α x : EReal) := by
  intro x
  have hbranch_tendsto :=
    tendsto_affine_inner_branch_of_weak_and_null u α x hweak hα_zero
  by_contra hlt
  have hstrict : (affineInnerSupremum u α x : EReal) < 0 := lt_of_not_ge hlt
  obtain ⟨ξ, hξ_sup, hξ_zero⟩ := EReal.lt_iff_exists_real_btwn.mp hstrict
  have hξ_neg : ξ < 0 := by
    exact_mod_cast hξ_zero
  have hξ_pos : 0 < -ξ := by
    linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hbranch_tendsto (-ξ) hξ_pos
  have hNdist : dist (⟪x, u N⟫_ℝ - α N) 0 < -ξ := hN N le_rfl
  have habs : |(⟪x, u N⟫_ℝ - α N : ℝ)| < -ξ := by
    simpa [Real.dist_eq] using hNdist
  have hξ_branch : ξ < ⟪x, u N⟫_ℝ - α N := by
    have habs_split := abs_lt.mp habs
    linarith
  have hbranch_le :
      (((⟪x, u N⟫_ℝ - α N : ℝ) : EReal)) ≤ (affineInnerSupremum u α x : EReal) := by
    rw [affineInnerSupremum_apply]
    exact le_iSup (fun n : ℕ ↦ (((⟪x, u n⟫_ℝ - α n : ℝ) : EReal))) N
  have hξ_le : (ξ : EReal) ≤ (affineInnerSupremum u α x : EReal) := by
    exact le_trans (by exact_mod_cast hξ_branch.le) hbranch_le
  exact (not_le_of_gt hξ_sup) hξ_le

/-- Helper for Example 17 46: every finite head of affine branches is eventually nonpositive near
the origin. -/
private theorem affineInnerSupremum_head_eventually_nonpos
    (u : ℕ → H) (α : ℕ → ℝ) (hα_pos : ∀ n : ℕ, 0 < α n) (s : Finset ℕ) :
    ∀ᶠ h in 𝓝 (0 : H), ∀ n ∈ s, (((⟪h, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ 0 := by
  induction s using Finset.induction_on with
  | empty =>
      exact Filter.Eventually.of_forall fun _ _ hn ↦ False.elim (Finset.notMem_empty _ hn)
  | @insert a s ha hs =>
      have ha_eventually :
          ∀ᶠ h in 𝓝 (0 : H), (((⟪h, u a⟫_ℝ - α a : ℝ) : EReal)) ≤ 0 := by
        have hcont : ContinuousAt (fun h : H ↦ ⟪h, u a⟫_ℝ - α a) (0 : H) := by
          -- Each fixed affine branch is continuous, so its negative value at `0` persists nearby.
          simpa [innerSL_apply_apply, real_inner_comm] using
            (((innerSL ℝ (u a)).continuous.continuousAt).sub continuousAt_const)
        have hlt :
            ∀ᶠ h in 𝓝 (0 : H), ⟪h, u a⟫_ℝ - α a < 0 := by
          have hneg : ⟪(0 : H), u a⟫_ℝ - α a < 0 := by
            have : -(α a) < 0 := by
              linarith [hα_pos a]
            simpa using this
          simpa [Set.preimage] using
            hcont.preimage_mem_nhds (Iio_mem_nhds hneg)
        filter_upwards [hlt] with h hh
        exact_mod_cast hh.le
      filter_upwards [ha_eventually, hs] with h hha hhs n hn
      rw [Finset.mem_insert] at hn
      rcases hn with rfl | hn
      · exact hha
      · exact hhs n hn

/-- Helper for Example 17 46: a tail bound on the weak coordinate `⟪y, uₙ⟫` turns the
corresponding affine branch along `t • y` into an `ε t` bound. -/
private theorem affine_inner_branch_directional_le_of_inner_le
    (u : ℕ → H) (α : ℕ → ℝ) (hα_pos : ∀ n : ℕ, 0 < α n)
    {y : H} {ε t : ℝ} {n : ℕ} (ht : 0 < t) (hinner : ⟪y, u n⟫_ℝ ≤ ε) :
    (((⟪t • y, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ (((ε * t : ℝ) : EReal)) := by
  -- Rewrite the branch on the ray `t • y`, then use positivity of `α n` to discard the offset.
  have hmul : t * ⟪y, u n⟫_ℝ ≤ t * ε := by
    nlinarith [hinner, ht]
  have hbranch_le : ⟪t • y, u n⟫_ℝ - α n ≤ ε * t := by
    rw [real_inner_smul_left]
    linarith [hmul, hα_pos n]
  exact_mod_cast hbranch_le

/-- Helper for Example 17 46: weak tail control and finite-head negativity give the source
directional `EReal` upper bound along rays `t • y`. -/
private theorem affineInnerSupremum_directional_head_tail_eventually_le
    (u : ℕ → H) (α : ℕ → ℝ)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n) :
    ∀ y : H, ∀ ε > 0,
      ∀ᶠ t : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
        (affineInnerSupremum u α (t • y) : EReal) ≤ (((ε * t : ℝ) : EReal)) := by
  intro y ε hε
  have hinner_tendsto : Tendsto (fun n ↦ ⟪y, u n⟫_ℝ) atTop (𝓝 0) := by
    -- Weak convergence controls each fixed scalar coordinate.
    simpa using
      (tendsto_affine_inner_branch_of_weak_and_null u (fun _ : ℕ ↦ 0) y hweak
        tendsto_const_nhds)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hinner_tendsto ε hε
  have htail : ∀ n ≥ N, ⟪y, u n⟫_ℝ ≤ ε := by
    intro n hn
    have hdist : dist (⟪y, u n⟫_ℝ) 0 < ε := hN n hn
    have habs : |⟪y, u n⟫_ℝ| < ε := by
      simpa [Real.dist_eq] using hdist
    exact (abs_lt.mp habs).2.le
  have hhead :
      ∀ᶠ h in 𝓝 (0 : H),
        ∀ n ∈ Finset.range N, (((⟪h, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ 0 :=
    affineInnerSupremum_head_eventually_nonpos u α hα_pos (Finset.range N)
  have hline :
      Tendsto (fun t : ℝ ↦ t • y) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (0 : H)) := by
    -- Pull the head estimate back along the ray `t ↦ t • y`.
    have hline_cont : ContinuousAt (fun t : ℝ ↦ t • y) 0 := by
      simpa using
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ y)).continuousAt
    simpa using hline_cont.continuousWithinAt.tendsto
  have hhead_line :
      ∀ᶠ t : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
        ∀ n ∈ Finset.range N, (((⟪t • y, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ 0 :=
    hline.eventually hhead
  filter_upwards [self_mem_nhdsWithin, hhead_line] with t ht hhead_t
  -- Split the supremum into a finite head, killed near `0`, and a weakly controlled tail.
  rw [affineInnerSupremum_apply]
  refine iSup_le fun n ↦ ?_
  by_cases hn : n < N
  · have hbranch_nonpos :
        (((⟪t • y, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ 0 :=
      hhead_t n (Finset.mem_range.2 hn)
    have htpos : 0 < t := ht
    have hzero_le :
        (0 : EReal) ≤ (((ε * t : ℝ) : EReal)) := by
      have hmul_nonneg : 0 ≤ ε * t := by
        nlinarith [hε, htpos]
      exact_mod_cast hmul_nonneg
    exact le_trans hbranch_nonpos hzero_le
  · exact
      affine_inner_branch_directional_le_of_inner_le u α hα_pos (show 0 < t from ht)
        (htail n (Nat.le_of_not_lt hn))

/-- Helper for Example 17 46: strong convergence of `uₙ` gives the source head/tail `EReal`
estimate with slope `ε ‖h‖` near the origin. -/
private theorem affineInnerSupremum_head_tail_eventually_le_eps_norm_of_tendsto
    (u : ℕ → H) (α : ℕ → ℝ) (hα_pos : ∀ n : ℕ, 0 < α n)
    (hstrong : Tendsto u atTop (𝓝 (0 : H))) :
    ∀ ε > 0,
      ∀ᶠ h in 𝓝 (0 : H),
        (affineInnerSupremum u α h : EReal) ≤ (((ε * ‖h‖ : ℝ) : EReal)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hstrong ε hε
  have htail : ∀ n ≥ N, ‖u n‖ ≤ ε := by
    intro n hn
    have hdist : dist (u n) 0 < ε := hN n hn
    have hnorm : ‖u n‖ < ε := by
      simpa [dist_eq_norm] using hdist
    exact hnorm.le
  have hhead :
      ∀ᶠ h in 𝓝 (0 : H),
        ∀ n ∈ Finset.range N, (((⟪h, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ 0 :=
    affineInnerSupremum_head_eventually_nonpos u α hα_pos (Finset.range N)
  filter_upwards [hhead] with h hhead_h
  -- The strong tail estimate is the norm analogue of the directional head/tail split above.
  rw [affineInnerSupremum_apply]
  refine iSup_le fun n ↦ ?_
  by_cases hn : n < N
  · have hbranch_nonpos :
        (((⟪h, u n⟫_ℝ - α n : ℝ) : EReal)) ≤ 0 :=
      hhead_h n (Finset.mem_range.2 hn)
    have hzero_le :
        (0 : EReal) ≤ (((ε * ‖h‖ : ℝ) : EReal)) := by
      have hmul_nonneg : 0 ≤ ε * ‖h‖ := by
        positivity
      exact_mod_cast hmul_nonneg
    exact le_trans hbranch_nonpos hzero_le
  · have hu_le : ‖u n‖ ≤ ε := htail n (Nat.le_of_not_lt hn)
    have hmul_le : ‖h‖ * ‖u n‖ ≤ ε * ‖h‖ := by
      nlinarith [norm_nonneg h, hu_le]
    have hbranch_le : ⟪h, u n⟫_ℝ - α n ≤ ε * ‖h‖ := by
      -- The tail branches are controlled by Cauchy-Schwarz and the norm-small tail of `uₙ`.
      linarith [real_inner_le_norm h (u n), hα_pos n, hmul_le]
    exact_mod_cast hbranch_le

/-- Helper for Example 17 46: the source directional head/tail estimate gives a real directional
difference quotient tending to `0`. -/
private theorem affineInnerSupremum_directional_quotient_tendsto_zero
    (u : ℕ → H) (α : ℕ → ℝ)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n) (hα_zero : Tendsto α atTop (𝓝 0))
    (y : H) :
    Tendsto
      (fun t : ℝ ↦
        (((affineInnerSupremum u α (t • y) : EReal).toReal -
            (affineInnerSupremum u α 0 : EReal).toReal) / t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hzero : (affineInnerSupremum u α 0 : EReal) = 0 :=
    affineInnerSupremum_zero u α hα_pos hα_zero
  have hzeroReal : (affineInnerSupremum u α 0 : EReal).toReal = 0 := by
    simpa using congrArg EReal.toReal hzero
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hhead :=
    affineInnerSupremum_directional_head_tail_eventually_le u α hweak hα_pos y (ε / 2) hhalf
  filter_upwards [self_mem_nhdsWithin, hhead] with t ht hupper
  have htpos : 0 < t := ht
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hnonnegE : 0 ≤ (affineInnerSupremum u α (t • y) : EReal) :=
    affineInnerSupremum_nonneg u α hweak hα_zero (t • y)
  have hreal_nonneg : 0 ≤ (affineInnerSupremum u α (t • y) : EReal).toReal :=
    EReal.toReal_nonneg hnonnegE
  have hreal_le :
      (affineInnerSupremum u α (t • y) : EReal).toReal ≤ (ε / 2) * t := by
    -- Convert the raw `EReal` ray estimate to a real estimate before dividing by `t`.
    exact
      EReal.toReal_le_toReal hupper
        (ne_of_gt (affineInnerSupremum_value_mem_Ioi_bot u α (t • y)))
        (EReal.coe_ne_top _)
  have hquot_nonneg :
      0 ≤
        (((affineInnerSupremum u α (t • y) : EReal).toReal -
            (affineInnerSupremum u α 0 : EReal).toReal) / t) := by
    rw [hzeroReal, sub_zero]
    exact div_nonneg hreal_nonneg htpos.le
  have hquot_le :
      (((affineInnerSupremum u α (t • y) : EReal).toReal -
            (affineInnerSupremum u α 0 : EReal).toReal) / t) ≤ ε / 2 := by
    rw [hzeroReal, sub_zero]
    exact (div_le_iff₀ htpos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hreal_le)
  let q : ℝ :=
    (((affineInnerSupremum u α (t • y) : EReal).toReal -
        (affineInnerSupremum u α 0 : EReal).toReal) / t)
  have habs_lt :
      |q| < ε := by
    have habs_le : |q| ≤ ε / 2 := by
      rw [abs_of_nonneg hquot_nonneg]
      exact hquot_le
    exact lt_of_le_of_lt habs_le (by linarith)
  simpa [q, Real.dist_eq, abs_div, abs_of_pos htpos] using habs_lt

/-- Helper for Example 17 46: the source head/tail estimate under strong convergence gives the
little-`o` remainder needed for Fréchet differentiability at the origin. -/
private theorem affineInnerSupremum_isLittleO_norm_at_zero_of_tendsto
    (u : ℕ → H) (α : ℕ → ℝ)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n) (hα_zero : Tendsto α atTop (𝓝 0))
    (hstrong : Tendsto u atTop (𝓝 (0 : H))) :
    (fun h : H ↦ (affineInnerSupremum u α h : EReal).toReal) =o[𝓝 (0 : H)] fun h : H ↦ ‖h‖ := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hhead :=
    affineInnerSupremum_head_tail_eventually_le_eps_norm_of_tendsto u α hα_pos hstrong
      (ε / 2) hhalf
  filter_upwards [hhead] with h hupper
  have hnonnegE : 0 ≤ (affineInnerSupremum u α h : EReal) :=
    affineInnerSupremum_nonneg u α hweak hα_zero h
  have hreal_nonneg : 0 ≤ (affineInnerSupremum u α h : EReal).toReal :=
    EReal.toReal_nonneg hnonnegE
  have hreal_le : (affineInnerSupremum u α h : EReal).toReal ≤ (ε / 2) * ‖h‖ := by
    -- The raw `EReal` bound becomes a real bound because the right-hand side is finite.
    exact
      EReal.toReal_le_toReal hupper
        (ne_of_gt (affineInnerSupremum_value_mem_Ioi_bot u α h))
        (EReal.coe_ne_top _)
  rw [Real.norm_of_nonneg hreal_nonneg]
  calc
    (affineInnerSupremum u α h : EReal).toReal ≤ (ε / 2) * ‖h‖ := hreal_le
    _ ≤ ε * ‖‖h‖‖ := by
      simpa [Real.norm_of_nonneg (norm_nonneg h)] using
        (show (ε / 2) * ‖h‖ ≤ ε * ‖h‖ by nlinarith [norm_nonneg h, hε])

-- Proof sketch: positivity of the offsets makes the finitely many low-index terms eventually
-- negative in every fixed direction, the null-sequence hypothesis forces those offsets to vanish
-- along the weakly controlled tail, and weak convergence controls the corresponding inner
-- products. This forces every directional derivative at `0` to vanish.
/-- If `uₙ` lies in the open unit ball, `uₙ ⇀ 0`, and `αₙ` is a positive null sequence, then the
affine supremum is Gâteaux differentiable at `0` with derivative `0`. -/
theorem affineInnerSupremum_hasGateauxDerivativeAt_zero (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n) (hα_zero : Tendsto α atTop (𝓝 0)) :
    HasGateauxDerivativeAt
      (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
      (0 : H →L[ℝ] ℝ) (0 : H) := by
  -- Route correction: the source proof first builds the raw `EReal` head/tail ray bound
  -- `affineInnerSupremum_directional_head_tail_eventually_le`, and only then converts it to
  -- real directional quotients with `toReal` and the nonnegativity squeeze.
  have _hball0 : ‖u 0‖ < 1 := hu_ball 0
  rw [hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient]
  intro y
  -- The directional quotient bridge above is already stated in the exact scalar form needed here.
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    affineInnerSupremum_directional_quotient_tendsto_zero u α hweak hα_pos hα_zero y

/-- Helper for Example 17 46: failure of strong convergence gives a subsequence whose norms stay
uniformly away from `0`. -/
private theorem exists_strictMono_subseq_norm_ge_of_not_tendsto_zero
    (u : ℕ → H) (hnot : ¬ Tendsto u atTop (𝓝 (0 : H))) :
    ∃ c > 0, ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ n, c ≤ ‖u (k n)‖ := by
  let _ : InnerProductSpace ℝ H := inferInstance
  rcases Filter.not_tendsto_iff_exists_frequently_notMem.1 hnot with ⟨s, hs0, hfreq⟩
  obtain ⟨c, hcpos, hcball⟩ := Metric.mem_nhds_iff.1 hs0
  rcases Filter.extraction_of_frequently_atTop hfreq with ⟨k, hkmono, hkout⟩
  refine ⟨c, hcpos, k, hkmono, ?_⟩
  intro n
  have hnot_ball : u (k n) ∉ Metric.ball (0 : H) c := by
    intro hkball
    exact hkout n (hcball hkball)
  have hdist : c ≤ dist (u (k n)) 0 := by
    by_contra hlt
    exact hnot_ball (by simpa [Metric.mem_ball, dist_eq_norm] using hlt)
  simpa [dist_eq_norm] using hdist

/-- Helper for Example 17 46: the normalized bad-subsequence test vectors contradict the
little-`o` criterion when `uₙ` does not converge strongly to `0`. -/
private theorem affineInnerSupremum_not_hasFDerivAt_zero_of_not_tendsto
    (u : ℕ → H) (α : ℕ → ℝ) (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hα_pos : ∀ n : ℕ, 0 < α n) (hα_zero : Tendsto α atTop (𝓝 0))
    (hnot : ¬ Tendsto u atTop (𝓝 (0 : H))) :
    ¬ HasFDerivAt (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
      (0 : H →L[ℝ] ℝ) (0 : H) := by
  rcases exists_strictMono_subseq_norm_ge_of_not_tendsto_zero u hnot with
    ⟨c, hcpos, k, hkmono, hkbound⟩
  have hkα_zero : Tendsto (fun n ↦ α (k n)) atTop (𝓝 0) :=
    hα_zero.comp hkmono.tendsto_atTop
  have hsqrt_zero : Tendsto (fun n ↦ Real.sqrt (α (k n))) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hkα_zero
  let y : ℕ → H :=
    fun n ↦ Real.sqrt (α (k n)) • ((‖u (k n)‖)⁻¹ • u (k n))
  have hy_norm : ∀ n, ‖y n‖ = Real.sqrt (α (k n)) := by
    intro n
    have hnorm_pos : 0 < ‖u (k n)‖ := lt_of_lt_of_le hcpos (hkbound n)
    -- The test vectors are normalized so that their norm is exactly `√(α (k n))`.
    calc
      ‖y n‖ = ‖Real.sqrt (α (k n))‖ * ‖((‖u (k n)‖)⁻¹ • u (k n))‖ := by
        simp [y, norm_smul]
      _ = Real.sqrt (α (k n)) * (‖(‖u (k n)‖)⁻¹‖ * ‖u (k n)‖) := by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_smul]
      _ = Real.sqrt (α (k n)) * (((‖u (k n)‖)⁻¹) * ‖u (k n)‖) := by
        rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
      _ = Real.sqrt (α (k n)) * 1 := by rw [inv_mul_cancel₀ hnorm_pos.ne']
      _ = Real.sqrt (α (k n)) := by ring
  have hy_tendsto : Tendsto y atTop (𝓝 (0 : H)) := by
    -- Norm convergence of `y n` to `0` is exactly convergence of `√(α (k n))` to `0`.
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [hy_norm] using hsqrt_zero
  intro hF
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at hF
  have hzero : (affineInnerSupremum u α 0 : EReal) = 0 :=
    affineInnerSupremum_zero u α hα_pos hα_zero
  have hquarter : 0 < c / 4 := by positivity
  have hsmall_raw := hF hquarter
  have hsmall :
      ∀ᶠ h in 𝓝 (0 : H),
        ‖(affineInnerSupremum u α h : EReal).toReal‖ ≤ (c / 4) * ‖h‖ := by
    have hzeroReal : (affineInnerSupremum u α 0 : EReal).toReal = 0 := by
      simpa using congrArg EReal.toReal hzero
    filter_upwards [hsmall_raw] with h hh
    have hh' := hh
    rw [hzeroReal, sub_zero] at hh'
    simpa using hh'
  have hsmall_y :
      ∀ᶠ n in atTop,
        ‖(affineInnerSupremum u α (y n) : EReal).toReal‖ ≤ (c / 4) * ‖y n‖ :=
    hy_tendsto.eventually hsmall
  have hhalf_y :
      ∀ᶠ n in atTop, Real.sqrt (α (k n)) ≤ c / 2 := by
    have hhalf : 0 < c / 2 := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hsqrt_zero (c / 2) hhalf
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hdist : dist (Real.sqrt (α (k n))) 0 < c / 2 := hN n hn
    have hsqrt_lt : Real.sqrt (α (k n)) < c / 2 := by
      simpa [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg _)] using hdist
    exact hsqrt_lt.le
  have hbranch_lower :
      ∀ n,
        Real.sqrt (α (k n)) * ‖u (k n)‖ - α (k n) ≤
          (affineInnerSupremum u α (y n) : EReal).toReal := by
    intro n
    have hnorm_pos : 0 < ‖u (k n)‖ := lt_of_lt_of_le hcpos (hkbound n)
    have hbranch :
        (((⟪y n, u (k n)⟫_ℝ - α (k n) : ℝ) : EReal)) ≤
          (affineInnerSupremum u α (y n) : EReal) := by
      rw [affineInnerSupremum_apply]
      exact le_iSup (fun m : ℕ ↦ (((⟪y n, u m⟫_ℝ - α m : ℝ) : EReal))) (k n)
    have hreal :
        (((⟪y n, u (k n)⟫_ℝ - α (k n) : ℝ) : EReal)).toReal ≤
          (affineInnerSupremum u α (y n) : EReal).toReal :=
      EReal.toReal_le_toReal hbranch (EReal.coe_ne_bot _) <|
        ne_of_lt (affineInnerSupremum_finite u α hu_ball hα_pos (y n))
    have hinner :
        ⟪y n, u (k n)⟫_ℝ = Real.sqrt (α (k n)) * ‖u (k n)‖ := by
      calc
        ⟪y n, u (k n)⟫_ℝ
            = Real.sqrt (α (k n)) * ⟪((‖u (k n)‖)⁻¹ • u (k n)), u (k n)⟫_ℝ := by
                simp [y, real_inner_smul_left]
        _ = Real.sqrt (α (k n)) * (((‖u (k n)‖)⁻¹) * ⟪u (k n), u (k n)⟫_ℝ) := by
              rw [real_inner_smul_left]
        _ = Real.sqrt (α (k n)) * (((‖u (k n)‖)⁻¹) * ‖u (k n)‖ ^ 2) := by
              rw [real_inner_self_eq_norm_sq]
        _ = Real.sqrt (α (k n)) * ‖u (k n)‖ := by
              field_simp [hnorm_pos.ne']
    have hreal_sub_ereal :
        (((⟪y n, u (k n)⟫_ℝ - α (k n) : ℝ) : EReal)).toReal ≤
          (affineInnerSupremum u α (y n) : EReal).toReal :=
      hreal
    have hreal_sub :
        ⟪y n, u (k n)⟫_ℝ - α (k n) ≤ (affineInnerSupremum u α (y n) : EReal).toReal := by
      calc
        ⟪y n, u (k n)⟫_ℝ - α (k n) =
            (((⟪y n, u (k n)⟫_ℝ - α (k n) : ℝ) : EReal)).toReal := by
              rw [EReal.toReal_coe]
        _ ≤ (affineInnerSupremum u α (y n) : EReal).toReal := hreal_sub_ereal
    linarith [hinner, hreal_sub]
  have hlower_y :
      ∀ᶠ n in atTop, (c / 2) * ‖y n‖ ≤ (affineInnerSupremum u α (y n) : EReal).toReal := by
    filter_upwards [hhalf_y] with n hsqrt_le
    let s := Real.sqrt (α (k n))
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      exact Real.sqrt_nonneg _
    have hs_sq : α (k n) = s ^ 2 := by
      dsimp [s]
      rw [Real.sq_sqrt (le_of_lt (hα_pos (k n)))]
    have hbranch_ge : (c / 2) * s ≤ s * ‖u (k n)‖ - α (k n) := by
      nlinarith [hkbound n, hsqrt_le, hs_nonneg, hs_sq]
    calc
      (c / 2) * ‖y n‖ = (c / 2) * s := by
        simpa [s] using congrArg (fun r : ℝ ↦ (c / 2) * r) (hy_norm n)
      _ ≤ s * ‖u (k n)‖ - α (k n) := hbranch_ge
      _ ≤ (affineInnerSupremum u α (y n) : EReal).toReal := hbranch_lower n
  rcases (hsmall_y.and hlower_y).exists with ⟨n, hsmall_n, hlower_n⟩
  have hy_pos : 0 < ‖y n‖ := by
    rw [hy_norm n]
    exact Real.sqrt_pos.2 (hα_pos (k n))
  have hupper_n :
      (affineInnerSupremum u α (y n) : EReal).toReal ≤ (c / 4) * ‖y n‖ := by
    calc
      (affineInnerSupremum u α (y n) : EReal).toReal ≤
          |(affineInnerSupremum u α (y n) : EReal).toReal| := by
            exact le_abs_self _
      _ ≤ (c / 4) * ‖y n‖ := hsmall_n
  nlinarith [hlower_n, hupper_n, hcpos, hy_pos]

-- Proof sketch: if `uₙ` does not converge strongly to `0`, choose a subsequence with norms bounded
-- away from `0` and test the affine supremum on the normalized vectors
-- `√(α_{kₙ}) • u_{kₙ} / ‖u_{kₙ}‖` to violate the little-o criterion. Conversely, if `uₙ → 0`,
-- split the supremum into finitely many initial terms and a small tail to obtain
-- `f(y) = o(‖y‖)` at the origin.
/-- If `uₙ` lies in the open unit ball, `uₙ ⇀ 0`, and `αₙ` is a positive null sequence, then the
affine supremum is Fréchet differentiable at `0` exactly when `uₙ → 0` strongly. -/
theorem affineInnerSupremum_differentiableAt_zero_iff (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n)
    (hα_zero : Tendsto α atTop (𝓝 0)) :
    DifferentiableAt ℝ (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) (0 : H) ↔
      Tendsto u atTop (𝓝 (0 : H)) := by
  -- Route correction: the reverse implication should now start from the raw `EReal` estimate
  -- `affineInnerSupremum_head_tail_eventually_le_eps_norm_of_tendsto` and only afterward pass to
  -- the little-o Fréchet criterion; the forward implication remains the textbook bad-subsequence
  -- obstruction.
  constructor
  · intro hdiff
    let A :
        H →L[ℝ] ℝ :=
      fderiv ℝ (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) (0 : H)
    have hA :
        HasFDerivAt (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) A (0 : H) :=
      hdiff.hasFDerivAt
    have hA_gateaux :
        HasGateauxDerivativeAt
          (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) A (0 : H) :=
      hA.hasGateauxDerivativeAt
    have hzero_gateaux :
        HasGateauxDerivativeAt
          (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
          (0 : H →L[ℝ] ℝ) (0 : H) :=
      affineInnerSupremum_hasGateauxDerivativeAt_zero u α hu_ball hweak hα_pos hα_zero
    have hA_zero : A = 0 := by
      -- The one-sided directional quotient has a unique limit, so every Fréchet derivative agrees
      -- with the already identified zero Gâteaux derivative.
      ext y
      exact tendsto_nhds_unique
        (hA_gateaux.tendsto_directionalDifferenceQuotient y)
        (hzero_gateaux.tendsto_directionalDifferenceQuotient y)
    have hF_zero :
        HasFDerivAt (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
          (0 : H →L[ℝ] ℝ) (0 : H) := by
      simpa [A, hA_zero] using hA
    by_cases hstrong : Tendsto u atTop (𝓝 (0 : H))
    · exact hstrong
    · exact False.elim <|
        (affineInnerSupremum_not_hasFDerivAt_zero_of_not_tendsto u α hu_ball hα_pos hα_zero
          hstrong) hF_zero
  · intro hstrong
    have hlittle :
        (fun h : H ↦ (affineInnerSupremum u α h : EReal).toReal) =o[𝓝 (0 : H)] fun h : H ↦ ‖h‖ :=
      affineInnerSupremum_isLittleO_norm_at_zero_of_tendsto u α hweak hα_pos hα_zero hstrong
    have hF :
        HasFDerivAt (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
          (0 : H →L[ℝ] ℝ) (0 : H) := by
      -- Convert the norm-based little-`o` statement to the canonical `fun h ↦ h` remainder.
      have hzero : (affineInnerSupremum u α 0 : EReal) = 0 :=
        affineInnerSupremum_zero u α hα_pos hα_zero
      have hzeroReal : (affineInnerSupremum u α 0 : EReal).toReal = 0 := by
        simpa using congrArg EReal.toReal hzero
      have hlittle' :
          (fun h : H ↦
            (affineInnerSupremum u α h : EReal).toReal -
              (affineInnerSupremum u α 0 : EReal).toReal) =o[𝓝 (0 : H)] fun h : H ↦ h := by
        convert hlittle.of_norm_right using 1
        ext h
        change
          (affineInnerSupremum u α h : EReal).toReal -
              (affineInnerSupremum u α 0 : EReal).toReal =
            (affineInnerSupremum u α h : EReal).toReal
        rw [hzeroReal, sub_zero]
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      simpa using hlittle'
    exact hF.differentiableAt

/-- Companion zero-derivative formulation of Example 17.46 (iii): under the same weak-convergence
hypothesis, Fréchet differentiability at `0` is equivalent to having Fréchet derivative `0`, hence
to strong convergence of `uₙ`. -/
theorem affineInnerSupremum_hasFDerivAt_zero_iff (u : ℕ → H) (α : ℕ → ℝ)
    (hu_ball : ∀ n : ℕ, ‖u n‖ < 1)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (0 : WeakSpace ℝ H)))
    (hα_pos : ∀ n : ℕ, 0 < α n)
    (hα_zero : Tendsto α atTop (𝓝 0)) :
    HasFDerivAt (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
      (0 : H →L[ℝ] ℝ) (0 : H) ↔
      Tendsto u atTop (𝓝 (0 : H)) := by
  constructor
  · intro hF
    -- A Fréchet derivative at the origin gives differentiability there, so the earlier iff closes
    -- the forward implication immediately.
    exact
      (affineInnerSupremum_differentiableAt_zero_iff u α hu_ball hweak hα_pos hα_zero).1
        hF.differentiableAt
  · intro hstrong
    -- Route correction: the owner proof should first recover an arbitrary Fréchet derivative from
    -- the differentiability iff, then identify it with `0` by comparing directional quotients to
    -- the already-proved zero Gâteaux derivative.
    have hdiff :
        DifferentiableAt ℝ (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) (0 : H) :=
      (affineInnerSupremum_differentiableAt_zero_iff u α hu_ball hweak hα_pos hα_zero).2 hstrong
    let A : H →L[ℝ] ℝ :=
      fderiv ℝ (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) (0 : H)
    have hA :
        HasFDerivAt (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) A (0 : H) :=
      hdiff.hasFDerivAt
    have hA_gateaux :
        HasGateauxDerivativeAt
          (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal) A (0 : H) :=
      hA.hasGateauxDerivativeAt
    have hzero_gateaux :
        HasGateauxDerivativeAt
          (fun x : H ↦ (affineInnerSupremum u α x : EReal).toReal)
          (0 : H →L[ℝ] ℝ) (0 : H) :=
      affineInnerSupremum_hasGateauxDerivativeAt_zero u α hu_ball hweak hα_pos hα_zero
    have hA_zero : A = 0 := by
      -- Each directional quotient has a unique limit, so the Fréchet derivative must agree with
      -- the zero Gâteaux derivative on every direction.
      ext y
      exact tendsto_nhds_unique
        (hA_gateaux.tendsto_directionalDifferenceQuotient y)
        (hzero_gateaux.tendsto_directionalDifferenceQuotient y)
    simpa [hA_zero] using hA

end ERealFunction
