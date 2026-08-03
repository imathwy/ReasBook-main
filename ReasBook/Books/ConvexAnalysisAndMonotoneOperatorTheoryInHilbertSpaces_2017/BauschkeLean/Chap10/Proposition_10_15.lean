import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap10.Definition_10_11
import BauschkeLean.Chap10.Proposition_10_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace EReal

/-- The nonnegative real power of an extended real, computed through its canonical
`ℝ≥0∞` representative. This is the bridge/view used when a source-facing nonnegative quantity is
expressed in the `EReal` owner API. -/
noncomputable def nnrpow (x : EReal) (p : ℝ) : EReal :=
  ENNReal.toEReal (x.toENNReal ^ p)

end EReal

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (g : H → NNReal) (p : ℝ)

local notation "gE" => Function.toEReal (fun x : H ↦ (g x : ℝ))
local notation "gPow" => Function.toEReal (fun x : H ↦ (g x : ℝ) ^ p)

-- Semantic recall: `lean_leansearch` only surfaced the real-valued mathlib owner
-- `UniformConvexOn`, so this item stays in the repo's `ERealFunction.UniformlyConvex` owner API,
-- while the exact modulus remains the canonical Chapter 10 owner used in the theorem surface.

-- Proof sketch: apply the midpoint Jensen-gap estimate from the textbook proof to the finite
-- `EReal` models `(fun x ↦ (g x : ℝ)).toEReal` and `(fun x ↦ (g x : ℝ) ^ p).toEReal`, then use
-- Proposition 10.14 to pass from midpoint gaps to the exact modulus of convexity. The owner
-- modulus is `EReal`-valued, while the textbook lower bound uses the nonnegative power
-- `exactModulusOfConvexity gE t ^ p`; `EReal.nnrpow` is the thin bridge/view that keeps the
-- theorem surface at the exact-modulus level and hides the `toENNReal`/`toEReal` bookkeeping.

/-- Helper for Proposition 10.15: coercing a nonnegative real through `EReal.nnrpow` recovers the
usual real `rpow`. -/
private theorem ereal_nnrpow_coe_eq_coe_rpow {r : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    (r : EReal).nnrpow p = (((r ^ p : ℝ)) : EReal) := by
  -- Unfold `EReal.nnrpow` and compute the power on the `ℝ≥0∞` side once.
  rw [EReal.nnrpow, EReal.real_coe_toENNReal, ENNReal.ofReal_rpow_of_nonneg hr hp]
  simp [EReal.coe_ennreal_ofReal, Real.rpow_nonneg hr]

/-- Helper for Proposition 10.15: a finite exact modulus value is the coercion of its real part. -/
private theorem exactModulusOfConvexity_eq_coe_toReal
    (hconv : ConvexOn gE (effectiveDomain gE)) {t : NNReal}
    (hfin : exactModulusOfConvexity gE t < ⊤) :
    (((exactModulusOfConvexity gE t).toReal : ℝ) : EReal) = exactModulusOfConvexity gE t := by
  -- Combine finiteness with nonnegativity to rule out both infinities before applying
  -- `EReal.coe_toReal`.
  have hnonneg : 0 ≤ exactModulusOfConvexity gE t :=
    exactModulusOfConvexity_nonneg gE hconv t
  have hnot_bot : exactModulusOfConvexity gE t ≠ ⊥ := by
    intro hbot
    rw [hbot] at hnonneg
    simp at hnonneg
  exact EReal.coe_toReal (ne_of_lt hfin) hnot_bot

/-- Helper for Proposition 10.15: once the exact modulus is finite, its `nnrpow` is just the
usual real power of its real part. -/
private theorem exactModulusOfConvexity_nnrpow_eq_coe_rpow
    (hp : 1 ≤ p) (hconv : ConvexOn gE (effectiveDomain gE)) {t : NNReal}
    (hfin : exactModulusOfConvexity gE t < ⊤) :
    (exactModulusOfConvexity gE t).nnrpow p =
      ((((exactModulusOfConvexity gE t).toReal ^ p : ℝ)) : EReal) := by
  -- Rewrite the finite exact modulus through its real representative before taking the power.
  rw [← exactModulusOfConvexity_eq_coe_toReal (g := g) hconv hfin]
  simpa using
    (ereal_nnrpow_coe_eq_coe_rpow (p := p)
      (r := (exactModulusOfConvexity gE t).toReal)
      (EReal.toReal_nonneg (exactModulusOfConvexity_nonneg gE hconv t))
      (le_trans zero_le_one hp))

/-- Helper for Proposition 10.15: the everywhere-finite midpoint Jensen gap of `h.toEReal` is the
coercion of the usual real midpoint gap. -/
private theorem midpointGap_toEReal_eq_coe (h : H → ℝ) (x y : H) :
    jensenGap (Function.toEReal h) (1 / 2 : ℝ) x y =
      ((((h x + h y) / 2 - h ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : ℝ)) : EReal) := by
  -- Expand the `toEReal` wrapper and normalize the midpoint coefficients in real arithmetic.
  change
    ((((1 / 2 : ℝ) * h x + (1 - (1 / 2 : ℝ)) * h y -
        h ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : ℝ)) : EReal) =
      ((((h x + h y) / 2 -
          h ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : ℝ)) : EReal)
  congr 1
  ring

/-- Helper for Proposition 10.15: the normalized midpoint Jensen gap of `h.toEReal` is the
coercion of four times the usual real midpoint gap. -/
private theorem normalizedMidpointGap_toEReal_eq_coe (h : H → ℝ) (x y : H) :
    jensenGap (Function.toEReal h) (1 / 2 : ℝ) x y /
        (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) =
      ((((4 * (((h x + h y) / 2) -
          h ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y)) : ℝ)) : ℝ) : EReal) := by
  -- Rewrite the midpoint gap as a real coercion, then clear the fixed denominator in `ℝ`.
  rw [midpointGap_toEReal_eq_coe (h := h) x y]
  let r : ℝ := ((h x + h y) / 2) - h ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y)
  have hcalc : (r / (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))) : ℝ)) = 4 * r := by
    field_simp [r]
    ring
  simpa [r, EReal.coe_div, EReal.coe_mul] using congrArg (fun z : ℝ ↦ (z : EReal)) hcalc

/-- Helper for Proposition 10.15: if `g.toEReal` is convex, then `(fun x ↦ (g x : ℝ) ^ p).toEReal`
is convex for `p ≥ 1`. -/
private theorem convexOnToERealNnrpow
    (hp : 1 ≤ p) (hconvG : ConvexOn gE (effectiveDomain gE)) :
    ConvexOn gPow (effectiveDomain gPow) := by
  -- Move to the real-valued representative of `g`, prove the powered Jensen inequality there,
  -- and cast the result back through `Function.toEReal`.
  have hconvReal : _root_.ConvexOn ℝ Set.univ (fun x : H ↦ (g x : ℝ)) := by
    simpa [Function.effectiveDomain_toEReal] using hconvG.toReal_convexOn_effectiveDomain
  refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
  intro x _hx y _hy α hα0 hα1
  have hβ0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
  have hreal :
      (g (α • x + (1 - α) • y) : ℝ) ^ p ≤
        α * (g x : ℝ) ^ p + (1 - α) * (g y : ℝ) ^ p := by
    have hbase :
        (g (α • x + (1 - α) • y) : ℝ) ≤
          α * (g x : ℝ) + (1 - α) * (g y : ℝ) := by
      simpa [smul_eq_mul] using hconvReal.2 (by simp) (by simp) hα0.le hβ0 (by ring)
    have hpowMonotone :
        (g (α • x + (1 - α) • y) : ℝ) ^ p ≤
          (α * (g x : ℝ) + (1 - α) * (g y : ℝ)) ^ p := by
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) hbase (le_trans zero_le_one hp)
    have hpowConvex :
        (α * (g x : ℝ) + (1 - α) * (g y : ℝ)) ^ p ≤
          α * (g x : ℝ) ^ p + (1 - α) * (g y : ℝ) ^ p := by
      simpa [smul_eq_mul] using
        (convexOn_rpow hp).2 (by simp [NNReal.coe_nonneg]) (by simp [NNReal.coe_nonneg])
          hα0.le hβ0 (by ring)
    exact hpowMonotone.trans hpowConvex
  simpa [Function.toEReal_apply] using
    (show ((((g (α • x + (1 - α) • y) : ℝ) ^ p : ℝ)) : EReal) ≤
        (α : EReal) * ((((g x : ℝ) ^ p : ℝ)) : EReal) +
          ((1 - α : ℝ) : EReal) * ((((g y : ℝ) ^ p : ℝ)) : EReal) from by
      exact_mod_cast hreal)

/-- Helper for Proposition 10.15: the exact modulus at radius `t`, divided by `4`, is bounded by
the real midpoint gap of `g` at every witness pair of distance `t`. -/
private theorem exactModulusQuarterLeMidpointGapReal
    (hg : UniformlyConvex gE (exactModulusOfConvexity gE)) {t : NNReal} {x y : H}
    (hxy : ‖x - y‖₊ = t) :
    (exactModulusOfConvexity gE t).toReal / 4 ≤
      ((g x : ℝ) + (g y : ℝ)) / 2 -
        (g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : ℝ) := by
  -- Route correction: keep the midpoint witness on the real surface and divide by `4` only after
  -- rewriting the normalized gap through a single `EReal`-to-real bridge.
  have hconvG : ConvexOn gE (effectiveDomain gE) := UniformlyConvex.convexOn hg
  have hxE : x ∈ effectiveDomain gE := by
    simpa [Function.effectiveDomain_toEReal]
  have hyE : y ∈ effectiveDomain gE := by
    simpa [Function.effectiveDomain_toEReal]
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  have hgap :
      exactModulusOfConvexity gE t ≤
        jensenGap gE (1 / 2 : ℝ) x y /
          (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) :=
    exactModulusOfConvexity_le_normalizedGap gE hxE hyE hxy hhalf
  have hnormalized :
      jensenGap gE (1 / 2 : ℝ) x y /
          (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) =
        ((((4 *
            ((((g x : ℝ) + (g y : ℝ)) / 2) -
              g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y)) : ℝ)) : ℝ) : EReal) := by
    simpa using normalizedMidpointGap_toEReal_eq_coe (h := fun z : H ↦ (g z : ℝ)) x y
  have hfin : exactModulusOfConvexity gE t < ⊤ := by
    calc
      exactModulusOfConvexity gE t
          ≤ jensenGap gE (1 / 2 : ℝ) x y /
              (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) := hgap
      _ = ((((4 *
            ((((g x : ℝ) + (g y : ℝ)) / 2) -
              g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y)) : ℝ)) : ℝ) : EReal) :=
        hnormalized
      _ < ⊤ := EReal.coe_lt_top _
  have hgapReal :
      (exactModulusOfConvexity gE t).toReal ≤
        4 *
          ((((g x : ℝ) + (g y : ℝ)) / 2) -
            g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y)) := by
    have hgapE :
        (((exactModulusOfConvexity gE t).toReal : ℝ) : EReal) ≤
          ((((4 *
              ((((g x : ℝ) + (g y : ℝ)) / 2) -
                g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y)) : ℝ)) : ℝ) : EReal) := by
      calc
        (((exactModulusOfConvexity gE t).toReal : ℝ) : EReal) = exactModulusOfConvexity gE t := by
          exact exactModulusOfConvexity_eq_coe_toReal (g := g) hconvG hfin
        _ ≤ jensenGap gE (1 / 2 : ℝ) x y /
              (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) := hgap
        _ = ((((4 *
              ((((g x : ℝ) + (g y : ℝ)) / 2) -
                g ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y)) : ℝ)) : ℝ) : EReal) :=
          hnormalized
    exact_mod_cast hgapE
  linarith

/-- Helper for Proposition 10.15: the scalar midpoint-gap estimate from the source proof. -/
private theorem scalarRpowGapLowerBound
    (hp : 1 ≤ p) {a b γ : ℝ}
    (hb : 0 ≤ b) (hγ : 0 ≤ γ) (hγab : γ ≤ a - b) :
    γ ^ p * min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p)) ≤ a ^ p - b ^ p := by
  -- Route correction: use the source proof's two branches, but take the high branch from the
  -- convex secant/derivative inequality for `x ↦ x ^ p` instead of carrying an extra MVT witness.
  let coeff : ℝ := min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hba : b + γ ≤ a := by
    linarith
  have hmain :
      (b + γ) ^ p - b ^ p ≤ a ^ p - b ^ p := by
    have hpow :
        (b + γ) ^ p ≤ a ^ p := by
      exact Real.rpow_le_rpow (add_nonneg hb hγ) hba hp0
    linarith
  by_cases hbhalf : b ≤ γ / 2
  · -- On the low branch, `b^p` is controlled by `(γ / 2)^p` and `(b + γ)^p` dominates `γ^p`.
    have hγpow : γ ^ p ≤ (b + γ) ^ p := by
      exact Real.rpow_le_rpow hγ (by linarith) hp0
    have hbpow : b ^ p ≤ (γ / 2) ^ p := by
      exact Real.rpow_le_rpow hb hbhalf hp0
    have hhalfpow : (γ / 2) ^ p = γ ^ p * (2 : ℝ) ^ (-p) := by
      calc
        (γ / 2) ^ p = γ ^ p / (2 : ℝ) ^ p := by
          rw [Real.div_rpow hγ (by norm_num : 0 ≤ (2 : ℝ)) p]
        _ = γ ^ p * ((2 : ℝ) ^ p)⁻¹ := by
          rw [div_eq_mul_inv]
        _ = γ ^ p * (2 : ℝ) ^ (-p) := by
          rw [← Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) p]
    have hbpow' : b ^ p ≤ γ ^ p * (2 : ℝ) ^ (-p) := by
      simpa [hhalfpow] using hbpow
    have hbranch :
        γ ^ p * (1 - (2 : ℝ) ^ (-p)) ≤ (b + γ) ^ p - b ^ p := by
      linarith
    calc
      γ ^ p * coeff ≤ γ ^ p * (1 - (2 : ℝ) ^ (-p)) := by
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hγ _)
      _ ≤ (b + γ) ^ p - b ^ p := hbranch
      _ ≤ a ^ p - b ^ p := hmain
  · -- On the high branch, the secant slope dominates the left derivative at `b`.
    have hhalf_lt : γ / 2 < b := lt_of_not_ge hbhalf
    by_cases hγzero : γ = 0
    · have hab : b ≤ a := by
        linarith [hγab, hγzero]
      have hpow : b ^ p ≤ a ^ p := by
        exact Real.rpow_le_rpow hb hab hp0
      have hnonneg : 0 ≤ a ^ p - b ^ p := by
        linarith
      have hpne : p ≠ 0 := by linarith
      simpa [hγzero, hpne] using hnonneg
    have hγ_ne : (0 : ℝ) ≠ γ := by
      intro hzero
      exact hγzero hzero.symm
    have hγ_pos : 0 < γ := lt_of_le_of_ne hγ hγ_ne
    have hconvPow : _root_.ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ p) := convexOn_rpow hp
    have hslope :
        p * b ^ (p - 1) ≤ slope (fun x : ℝ ↦ x ^ p) b (b + γ) := by
      simpa [Real.deriv_rpow_const] using
        hconvPow.deriv_le_slope (by simpa using hb) (by simpa using add_nonneg hb hγ)
          (by linarith) (Real.differentiable_rpow_const hp b)
    have hslopeMul :
        γ * (p * b ^ (p - 1)) ≤ γ * slope (fun x : ℝ ↦ x ^ p) b (b + γ) := by
      exact mul_le_mul_of_nonneg_left hslope hγ
    have hslopeEq :
        γ * slope (fun x : ℝ ↦ x ^ p) b (b + γ) = (b + γ) ^ p - b ^ p := by
      simpa using (sub_smul_slope (fun x : ℝ ↦ x ^ p) b (b + γ))
    have hpow :
        (γ / 2) ^ (p - 1) ≤ b ^ (p - 1) := by
      exact Real.rpow_le_rpow (by linarith) hhalf_lt.le (sub_nonneg.mpr hp)
    have hscale :
        γ ^ p * (p * (2 : ℝ) ^ (1 - p)) = γ * (p * (γ / 2) ^ (p - 1)) := by
      calc
        γ ^ p * (p * (2 : ℝ) ^ (1 - p))
            = p * (γ ^ p * (2 : ℝ) ^ (1 - p)) := by ring
        _ = p * (γ * (γ / 2) ^ (p - 1)) := by
          congr 1
          calc
            γ ^ p * (2 : ℝ) ^ (1 - p)
                = γ ^ p * (2 : ℝ) ^ (-(p - 1)) := by
                    congr 2
                    ring
            _ = γ ^ p * (((2 : ℝ) ^ (p - 1))⁻¹) := by
                    rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]
            _ = γ ^ p / (2 : ℝ) ^ (p - 1) := by
                    rw [div_eq_mul_inv]
            _ = γ * (γ ^ (p - 1) / (2 : ℝ) ^ (p - 1)) := by
                    rw [show γ ^ p = γ * γ ^ (p - 1) by
                      calc
                        γ ^ p = γ ^ ((1 : ℝ) + (p - 1)) := by congr 1; ring
                        _ = γ ^ (1 : ℝ) * γ ^ (p - 1) := by
                          rw [Real.rpow_add hγ_pos]
                        _ = γ * γ ^ (p - 1) := by
                          rw [Real.rpow_one]]
                    ring
            _ = γ * (γ / 2) ^ (p - 1) := by
                    rw [Real.div_rpow hγ (by norm_num : 0 ≤ (2 : ℝ)) (p - 1)]
        _ = γ * (p * (γ / 2) ^ (p - 1)) := by ring
    have hbranch :
        γ ^ p * (p * (2 : ℝ) ^ (1 - p)) ≤ (b + γ) ^ p - b ^ p := by
      calc
        γ ^ p * (p * (2 : ℝ) ^ (1 - p)) = γ * (p * (γ / 2) ^ (p - 1)) := hscale
        _ ≤ γ * (p * b ^ (p - 1)) := by
          have hinner :
              p * (γ / 2) ^ (p - 1) ≤ p * b ^ (p - 1) := by
            exact mul_le_mul_of_nonneg_left hpow hp0
          exact mul_le_mul_of_nonneg_left hinner hγ
        _ ≤ γ * slope (fun x : ℝ ↦ x ^ p) b (b + γ) := hslopeMul
        _ = (b + γ) ^ p - b ^ p := hslopeEq
    calc
      γ ^ p * coeff ≤ γ ^ p * (p * (2 : ℝ) ^ (1 - p)) := by
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg hγ _)
      _ ≤ (b + γ) ^ p - b ^ p := hbranch
      _ ≤ a ^ p - b ^ p := hmain

/-- Helper for Proposition 10.15: the textbook midpoint estimate gives the announced lower bound
for the midpoint modulus of the powered function. -/
private theorem midpointModulusNnrpowLowerBound
    (hp : 1 ≤ p) (hg : UniformlyConvex gE (exactModulusOfConvexity gE)) (t : NNReal) :
    ((((2 : ℝ) ^ (-2 * p) *
        min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal) *
      (exactModulusOfConvexity gE t).nnrpow p ≤
      midpointModulusOfConvexity gPow t := by
  let mCoeff : ℝ := (2 : ℝ) ^ (-2 * p) *
    min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))
  have hconvG : ConvexOn gE (effectiveDomain gE) := UniformlyConvex.convexOn hg
  rw [midpointModulusOfConvexity]
  refine le_sInf ?_
  intro δ hδ
  rcases hδ with ⟨x, hx, y, hy, hxy, rfl⟩
  let m : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  let gap : ℝ := (((g x : ℝ) ^ p + (g y : ℝ) ^ p) / 2) - (g m : ℝ) ^ p
  let rawGap : ℝ := ((g x : ℝ) + (g y : ℝ)) / 2 - (g m : ℝ)
  have hxE : x ∈ effectiveDomain gE := by
    simpa [Function.effectiveDomain_toEReal]
  have hyE : y ∈ effectiveDomain gE := by
    simpa [Function.effectiveDomain_toEReal]
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  have hbound :
      exactModulusOfConvexity gE t ≤
        jensenGap gE (1 / 2 : ℝ) x y /
          (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) :=
    exactModulusOfConvexity_le_normalizedGap gE hxE hyE hxy hhalf
  have hnormalized :
      jensenGap gE (1 / 2 : ℝ) x y /
          (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) =
        ((((4 * rawGap : ℝ)) : ℝ) : EReal) := by
    simpa [rawGap, m] using
      normalizedMidpointGap_toEReal_eq_coe (h := fun z : H ↦ (g z : ℝ)) x y
  have hfin : exactModulusOfConvexity gE t < ⊤ := by
    calc
      exactModulusOfConvexity gE t
          ≤ jensenGap gE (1 / 2 : ℝ) x y /
              (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ)) := hbound
      _ = ((((4 * rawGap : ℝ)) : ℝ) : EReal) := hnormalized
      _ < ⊤ := EReal.coe_lt_top _
  have hquarter :
      (exactModulusOfConvexity gE t).toReal / 4 ≤ rawGap :=
    exactModulusQuarterLeMidpointGapReal (g := g) hg hxy
  -- Finish on the real surface, then cast the final midpoint-gap estimate back to `EReal`.
  have hconvPow : ConvexOn gPow (effectiveDomain gPow) :=
    convexOnToERealNnrpow (g := g) (p := p) hp hconvG
  let γ : ℝ := (exactModulusOfConvexity gE t).toReal / 4
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    exact div_nonneg
      (EReal.toReal_nonneg (exactModulusOfConvexity_nonneg gE hconvG t)) (by norm_num)
  have hscalar :
      γ ^ p *
          min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p)) ≤
        (((g x : ℝ) + (g y : ℝ)) / 2) ^ p - (g m : ℝ) ^ p :=
    scalarRpowGapLowerBound (p := p) hp (b := (g m : ℝ)) (γ := γ)
      (a := ((g x : ℝ) + (g y : ℝ)) / 2) (NNReal.coe_nonneg _) hγ_nonneg (by simpa [γ] using hquarter)
  have hpowConvexHalf :
      (((1 / 2 : ℝ) * (g x : ℝ) + (1 / 2 : ℝ) * (g y : ℝ)) ^ p) ≤
        ((1 / 2 : ℝ) * (g x : ℝ) ^ p + (1 / 2 : ℝ) * (g y : ℝ) ^ p) := by
    simpa [smul_eq_mul] using
      (convexOn_rpow hp).2
        (show (g x : ℝ) ∈ Set.Ici (0 : ℝ) from NNReal.coe_nonneg _)
        (show (g y : ℝ) ∈ Set.Ici (0 : ℝ) from NNReal.coe_nonneg _)
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by ring)
  have hpowConvex :
      (((g x : ℝ) + (g y : ℝ)) / 2) ^ p ≤
        (((g x : ℝ) ^ p + (g y : ℝ) ^ p) / 2) := by
    simpa [div_eq_mul_inv, one_div, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
      hpowConvexHalf
  have hgapLower :
      (((g x : ℝ) + (g y : ℝ)) / 2) ^ p - (g m : ℝ) ^ p ≤ gap := by
    dsimp [gap]
    linarith
  have hmu_nonneg : 0 ≤ (exactModulusOfConvexity gE t).toReal :=
    EReal.toReal_nonneg (exactModulusOfConvexity_nonneg gE hconvG t)
  have hfourpow (q : ℝ) : (4 : ℝ) ^ q = (2 : ℝ) ^ (2 * q) := by
    calc
      (4 : ℝ) ^ q = (((2 : ℝ) ^ (2 : ℕ)) : ℝ) ^ q := by norm_num
      _ = (2 : ℝ) ^ (2 * q) := by
        symm
        simpa [mul_comm] using (Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) 2 q)
      _ = (2 : ℝ) ^ (2 * q) := by ring_nf
  have hγpow :
      γ ^ p = (2 : ℝ) ^ (-2 * p) * (exactModulusOfConvexity gE t).toReal ^ p := by
    calc
      γ ^ p = ((exactModulusOfConvexity gE t).toReal / 4) ^ p := by rfl
      _ = (exactModulusOfConvexity gE t).toReal ^ p / (4 : ℝ) ^ p := by
        rw [Real.div_rpow hmu_nonneg (by norm_num : 0 ≤ (4 : ℝ)) p]
      _ = (exactModulusOfConvexity gE t).toReal ^ p * (4 : ℝ) ^ (-p) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)) p]
      _ = (exactModulusOfConvexity gE t).toReal ^ p * (2 : ℝ) ^ (2 * (-p)) := by
        rw [hfourpow (-p)]
      _ = (exactModulusOfConvexity gE t).toReal ^ p * (2 : ℝ) ^ (-2 * p) := by
        congr 2
        ring
      _ = (2 : ℝ) ^ (-2 * p) * (exactModulusOfConvexity gE t).toReal ^ p := by
        ring
  have hrealFinal :
      mCoeff * (exactModulusOfConvexity gE t).toReal ^ p ≤ gap := by
    calc
      mCoeff * (exactModulusOfConvexity gE t).toReal ^ p
          = ((2 : ℝ) ^ (-2 * p) * (exactModulusOfConvexity gE t).toReal ^ p) *
              min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p)) := by
                dsimp [mCoeff]
                ring
      _ = γ ^ p * min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p)) := by
        rw [hγpow]
      _ ≤ (((g x : ℝ) + (g y : ℝ)) / 2) ^ p - (g m : ℝ) ^ p := hscalar
      _ ≤ gap := hgapLower
  have hpowRewrite :
      (exactModulusOfConvexity gE t).nnrpow p =
        (((exactModulusOfConvexity gE t).toReal ^ p : ℝ) : EReal) :=
    exactModulusOfConvexity_nnrpow_eq_coe_rpow (g := g) (p := p) hp hconvG hfin
  calc
    ((((mCoeff : ℝ)) : EReal) * (exactModulusOfConvexity gE t).nnrpow p)
        = (((mCoeff * (exactModulusOfConvexity gE t).toReal ^ p : ℝ)) : EReal) := by
            rw [hpowRewrite, ← EReal.coe_mul]
    _ ≤ (((gap : ℝ)) : EReal) := by
          exact_mod_cast hrealFinal
    _ = jensenGap gPow (1 / 2 : ℝ) x y := by
          symm
          simpa [gap, m] using midpointGap_toEReal_eq_coe
            (h := fun z : H ↦ (g z : ℝ) ^ p) x y
/-- Proposition 10.15 (1): for a uniformly convex nonnegative real-valued function `g`, the exact
modulus of convexity of the pointwise power `g^p` is bounded below by
`2^(1 - 2p) * min (p * 2^(1 - p)) (1 - 2^(-p)) *
  (exactModulusOfConvexity g.toEReal)^p`. -/
theorem exactModulusOfConvexity_nnreal_rpow_lower_bound
    (hp : 1 ≤ p) (hg : UniformlyConvex gE (exactModulusOfConvexity gE)) (t : NNReal) :
    ((((2 : ℝ) ^ (1 - 2 * p) *
        min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal) *
      (exactModulusOfConvexity gE t).nnrpow p ≤
      exactModulusOfConvexity gPow t := by
  -- Convert the midpoint lower bound to the exact modulus using Proposition 10.14.
  have hconvG : ConvexOn gE (effectiveDomain gE) := UniformlyConvex.convexOn hg
  have hconvPow : ConvexOn gPow (effectiveDomain gPow) :=
    convexOnToERealNnrpow (g := g) (p := p) hp hconvG
  have hmid := midpointModulusNnrpowLowerBound (g := g) (p := p) hp hg t
  have htwo :
      2 * midpointModulusOfConvexity gPow t ≤ exactModulusOfConvexity gPow t :=
    two_mul_midpointModulusOfConvexity_le_exactModulusOfConvexity (f := gPow) hconvPow t
  have hcoeff :
      (2 : ℝ) ^ (1 - 2 * p) =
        2 * (2 : ℝ) ^ (-2 * p) := by
    calc
      (2 : ℝ) ^ (1 - 2 * p) = (2 : ℝ) ^ (1 + (-2 * p)) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-2 * p) := by
        rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      _ = 2 * (2 : ℝ) ^ (-2 * p) := by
        rw [Real.rpow_one]
  have hcoeffE :
      ((((2 : ℝ) ^ (1 - 2 * p) *
          min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal) =
        ((2 : EReal) *
          ((((2 : ℝ) ^ (-2 * p) *
              min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal)) := by
    change ((((2 : ℝ) ^ (1 - 2 * p) *
        min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal) =
      ((((2 : ℝ) * ((2 : ℝ) ^ (-2 * p) *
          min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p)))) : ℝ) : EReal)
    congr 1
    calc
      (2 : ℝ) ^ (1 - 2 * p) * min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))
          = (2 * (2 : ℝ) ^ (-2 * p)) * min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p)) := by
              rw [hcoeff]
      _ = (2 : ℝ) * ((2 : ℝ) ^ (-2 * p) *
            min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) := by
              ring
  rw [hcoeffE]
  calc
    (2 : EReal) * ((((2 : ℝ) ^ (-2 * p) *
        min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal) *
          (exactModulusOfConvexity gE t).nnrpow p
        = (2 : EReal) *
            (((((2 : ℝ) ^ (-2 * p) *
                min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal) *
              (exactModulusOfConvexity gE t).nnrpow p) := by
                rw [mul_assoc]
    _ 
        ≤ (2 : EReal) * midpointModulusOfConvexity gPow t := by
            exact mul_le_mul_of_nonneg_left hmid (by norm_num)
    _ ≤ exactModulusOfConvexity gPow t := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using htwo

-- Proof sketch: use the lower bound on the exact modulus from
-- `exactModulusOfConvexity_nnreal_rpow_lower_bound`; the exact modulus of `g` vanishes only at
-- `0` by `hg`, so the lower bound shows the exact modulus of `g^p` also vanishes only at `0`,
-- and then Corollary 10.13 gives uniform convexity with the exact modulus.
/-- Proposition 10.15 (2): the pointwise `p`-power of a uniformly convex nonnegative real-valued
function is uniformly convex with its exact modulus. -/
theorem uniformlyConvex_nnreal_rpow
    (hp : 1 ≤ p) (hg : UniformlyConvex gE (exactModulusOfConvexity gE)) :
    UniformlyConvex gPow (exactModulusOfConvexity gPow) := by
  -- Read uniform convexity off the zero set of the exact modulus for the powered function.
  have hconvG : ConvexOn gE (effectiveDomain gE) := UniformlyConvex.convexOn hg
  have hconvPow : ConvexOn gPow (effectiveDomain gPow) :=
    convexOnToERealNnrpow (g := g) (p := p) hp hconvG
  refine (exactModulusOfConvexity_uniformlyConvex_iff (f := gPow) hconvPow).2 ?_
  intro t
  constructor
  · intro hpowZero
    let coeff : ℝ :=
      (2 : ℝ) ^ (1 - 2 * p) *
        min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))
    have hcoeffPos : 0 < coeff := by
      have hpPos : 0 < p := lt_of_lt_of_le zero_lt_one hp
      have hleftPos : 0 < p * (2 : ℝ) ^ (1 - p) := by
        positivity
      have hrightPow : (2 : ℝ) ^ (-p) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
      have hrightPos : 0 < 1 - (2 : ℝ) ^ (-p) := by
        linarith
      have hminPos :
          0 <
            min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p)) :=
        lt_min hleftPos hrightPos
      have hpowPos : 0 < (2 : ℝ) ^ (1 - 2 * p) :=
        Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _
      exact mul_pos hpowPos hminPos
    have hcoeffNe : (((coeff : ℝ)) : EReal) ≠ 0 := by
      simpa [EReal.coe_eq_zero] using hcoeffPos.ne'
    have hnnrpowNonneg : 0 ≤ (exactModulusOfConvexity gE t).nnrpow p := by
      rw [EReal.nnrpow]
      exact EReal.coe_ennreal_nonneg _
    have hbound :
        (((coeff : ℝ)) : EReal) * (exactModulusOfConvexity gE t).nnrpow p ≤ 0 := by
      simpa [coeff, hpowZero] using
        exactModulusOfConvexity_nnreal_rpow_lower_bound (g := g) (p := p) hp hg t
    have hprodNonneg :
        0 ≤ (((coeff : ℝ)) : EReal) * (exactModulusOfConvexity gE t).nnrpow p := by
      exact mul_nonneg (by exact_mod_cast hcoeffPos.le) hnnrpowNonneg
    have hprodZero :
        (((coeff : ℝ)) : EReal) * (exactModulusOfConvexity gE t).nnrpow p = 0 :=
      le_antisymm hbound hprodNonneg
    have hnnrpowZero : (exactModulusOfConvexity gE t).nnrpow p = 0 := by
      exact (mul_eq_zero.mp hprodZero).resolve_left hcoeffNe
    have hexact_le_zero : exactModulusOfConvexity gE t ≤ 0 := by
      rw [EReal.nnrpow, EReal.coe_ennreal_eq_zero] at hnnrpowZero
      have hpPos : 0 < p := lt_of_lt_of_le zero_lt_one hp
      rw [ENNReal.rpow_eq_zero_iff_of_pos hpPos, EReal.toENNReal_eq_zero_iff] at hnnrpowZero
      exact hnnrpowZero
    have hexact_nonneg : 0 ≤ exactModulusOfConvexity gE t :=
      exactModulusOfConvexity_nonneg gE hconvG t
    have hexactZero : exactModulusOfConvexity gE t = 0 :=
      le_antisymm hexact_le_zero hexact_nonneg
    exact (UniformlyConvex.exactModulusOfConvexity_eq_zero_iff hg t).1 hexactZero
  · intro ht
    simpa [ht] using exactModulusOfConvexity_zero (f := gPow) hconvPow

end ERealFunction
