import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
variable {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
variable
  (hgrad :
    HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x)
include hconv hx hgrad

omit gradf hgrad in
/-- Helper for Proposition 17 6: if `y` is in the effective domain, then every convex combination
of `x` and `y` along the secant segment stays in the effective domain. -/
private theorem segment_sub_mem_effectiveDomain
    {y : H} (hy : y ∈ effectiveDomain f) :
    ∀ {α : ℝ}, 0 ≤ α → α ≤ 1 → x + α • (y - x) ∈ effectiveDomain f := by
  -- Convexity of the effective domain gives the source proof's segment argument directly.
  intro α hα0 hα1
  have hconvex : Convex ℝ (effectiveDomain f) := hconv.convex_effectiveDomain
  exact hconvex.add_smul_sub_mem hx hy ⟨hα0, hα1⟩

omit hconv gradf hgrad in
/-- Helper for Proposition 17 6: along points where both function values are finite, the Chapter 17
extended-real quotient is the coercion of the real quotient for `toReal`. -/
private theorem quotient_eq_coe_toReal_of_mem_effectiveDomain
    {d : H} {α : ℝ} (hα : 0 < α) (hαdom : x + α • d ∈ effectiveDomain f) :
    ((f (x + α • d) : EReal) - (f x : EReal)) / α =
      ((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
  -- Rewrite both finite `EReal` values through `toReal`, then the quotient is purely real.
  have _ : α ≠ 0 := hα.ne'
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hαdom_top : (f (x + α • d) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
  have hαdom_bot : (f (x + α • d) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + α • d) : EReal) from (f (x + α • d)).2)
  rw [← EReal.coe_toReal hαdom_top hαdom_bot, ← EReal.coe_toReal hx_top hx_bot,
    ← EReal.coe_sub, ← EReal.coe_div]
  simp

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] hconv hx gradf hgrad in
/-- Helper for Proposition 17 6: outside the effective domain, a `]-∞,+∞]`-valued function takes
the value `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {y : H} (hy : y ∉ effectiveDomain f) :
    (f y : EReal) = ⊤ := by
  -- Negating the strict-upper-bound characterization of the effective domain forces the top value.
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))

omit hconv in
/-- Helper for Proposition 17 6: once the secant ray stays eventually inside the effective domain,
the real Gâteaux derivative of `toReal` becomes the Chapter 17 directional derivative of `f`. -/
private theorem hasDirectionalDerivativeAt_toDualMap_of_eventually_mem_effectiveDomain
    (d : H)
    (hevent : ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ effectiveDomain f) :
    HasDirectionalDerivativeAt f x d ((((toDualMap ℝ H gradf) d : ℝ) : EReal)) := by
  -- First obtain the real-valued quotient limit from the Gâteaux derivative hypothesis.
  have hreal :
      Filter.Tendsto
        (fun α : ℝ ↦ (((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((toDualMap ℝ H gradf) d)) := by
    simpa [one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hgrad.tendsto_directionalDifferenceQuotient d
  -- Then coerce that real limit to `EReal` and rewrite the source quotient eventually.
  have hcoe :
      Filter.Tendsto
        (fun α : ℝ ↦
          (((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((((toDualMap ℝ H gradf) d : ℝ) : EReal))) :=
    EReal.tendsto_coe.2 hreal
  have hEq :
      (fun α : ℝ ↦ ((f (x + α • d) : EReal) - (f x : EReal)) / α) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun α : ℝ ↦
          (((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal))) := by
    filter_upwards [hevent, self_mem_nhdsWithin] with α hαdom hα
    simpa using
      quotient_eq_coe_toReal_of_mem_effectiveDomain f hx hα hαdom
  exact ⟨hx, Filter.Tendsto.congr' hEq.symm hcoe⟩

-- Proof sketch: identify the directional derivative of `f` at `x` in the direction `y - x` with
-- the derivative functional `toDualMap ℝ H gradf (y - x) = ⟪gradf, y - x⟫_ℝ` using the Gâteaux
-- differentiability hypothesis, and compare the resulting limit with the convex secant slopes.
/-- Proposition 17 6: at an effective-domain point of a convex extended-real-valued function, a
Gâteaux gradient defines a supporting hyperplane to `f` at `x`. -/
theorem gateauxGradient_add_value_le
    (y : H) :
    (⟪y - x, gradf⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := by
  -- Split by whether the endpoint has a finite value; outside the effective domain the claim is
  -- trivial because `f y = ⊤`.
  by_cases hy : y ∈ effectiveDomain f
  · have hquot_tendsto :
        Filter.Tendsto
          (fun α : ℝ ↦
            (((f (x + α • (y - x)) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪y - x, gradf⟫_ℝ) := by
      -- The Gâteaux derivative is the limit of the one-sided secant quotients in direction `y - x`.
      simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, real_inner_comm]
        using hgrad.tendsto_directionalDifferenceQuotient (y - x)
    have hquot_le :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (((f (x + α • (y - x)) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) ≤
            (f y : EReal).toReal - (f x : EReal).toReal := by
      have hα_mem :
          ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Ioo (0 : ℝ) 1 := by
        filter_upwards
          [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with α
            hα0 hα1
        exact ⟨hα0, hα1⟩
      filter_upwards [hα_mem] with α hα
      have hineq :
          (f (x + α • (y - x)) : EReal).toReal ≤
            α * (f y : EReal).toReal + (1 - α) * (f x : EReal).toReal := by
        -- Convexity of `toReal` on the effective domain bounds interior segment values.
        simpa [sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm,
          mul_comm, mul_left_comm, mul_assoc] using
          hconv.toReal_convexOn_effectiveDomain.2 hy hx hα.1.le (sub_nonneg.mpr hα.2.le)
            (by ring)
      have hsub :
          (f (x + α • (y - x)) : EReal).toReal - (f x : EReal).toReal ≤
            α * ((f y : EReal).toReal - (f x : EReal).toReal) := by
        nlinarith
      exact (div_le_iff₀ hα.1).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hsub)
    have hinner_le :
        ⟪y - x, gradf⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      exact le_of_tendsto_of_tendsto hquot_tendsto tendsto_const_nhds hquot_le
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hreal : ⟪y - x, gradf⟫_ℝ + (f x : EReal).toReal ≤ (f y : EReal).toReal := by
      linarith
    have hcast :
        (((⟪y - x, gradf⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
          (((f y : EReal).toReal : ℝ) : EReal) := by
      exact_mod_cast hreal
    have hcast' :
        (⟪y - x, gradf⟫_ℝ : EReal) + (((f x : EReal).toReal : ℝ) : EReal) ≤
          (((f y : EReal).toReal : ℝ) : EReal) := by
      simpa [← EReal.coe_add] using hcast
    simpa [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot] using hcast'
  · have hfy_top : (f y : EReal) = ⊤ := by
      exact value_eq_top_of_not_mem_effectiveDomain f hy
    rw [hfy_top]
    exact le_top

/-- Canonical Chapter 16 companion to Proposition 17 6: the supporting-hyperplane inequality says
exactly that the Gâteaux gradient is a subgradient at `x`. -/
theorem gateauxGradient_mem_subdifferential
    :
    gradf ∈ (∂ f) x := by
  exact (mem_subdifferential_iff f x gradf).2 (gateauxGradient_add_value_le f hconv hx gradf hgrad)

end DifferentiabilityOfConvexFunctions

end ERealFunction
