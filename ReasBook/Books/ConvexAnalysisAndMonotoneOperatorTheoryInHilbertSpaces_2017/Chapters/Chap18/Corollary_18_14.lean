import Mathlib
import BauschkeLean.Chap08.Example_8_23
import BauschkeLean.Chap13.Example_13_2
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap18.Theorem_18_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction Gradient InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section StrongerDifferentiabilityBounds

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f : H → ℝ} {β p : ℝ}

/- Source/core/bridge triage:
- `source-facing`: Corollary 18.14 records the five power-law implications in the textbook smooth
  convex chain.
- `core/canonical`: Theorem 18.13 is the chapter owner for these implications, and mathlib's
  canonical gradient owner is `∇ f`. On the scalar side, the owner abstractions are the control
  function `φ`, its remainder `θ`, and its recovery modulus `ϱ`; on the conjugate side, the
  project owner for a real-valued function is `f.asEReal∗`.
- `bridge/view`: this file should therefore remain only the source-facing specialization to the
  power control `φ(s) = β * |s|^(p + 1)`, with the explicit power remainder and conjugate-power
  terms treated as derived API from that owner layer rather than as new local owners.
-/
-- Semantic recall: `lean_leansearch` only surfaced generic Hölder APIs, so the owner/API choice
-- here stays the local specialization of Theorem 18.13 and nearby Chapter 18 precedent.

local notation "powerSlope" => fun s : ℝ ↦ β * s ^ p
local notation "powerControl" => fun s : ℝ ↦ β * s ^ (p + 1)
local notation "powerRemainder" => fun s : ℝ ↦ β / (p + 1) * s ^ (p + 1)
local notation "conjugatePower" => fun s : ℝ ↦ β ^ (-1 / p) * p / (p + 1) * s ^ (1 + 1 / p)
local notation "powerRecovery" => fun s : ℝ ↦ β * ((p + 1) / (2 * p)) ^ p * s ^ p

/-- Helper for Corollary 18.14: the scalar power owner `s ↦ β * |s|^(p + 1)` is even. -/
lemma powerControl_even :
    Function.Even (fun s : ℝ ↦ β * |s| ^ (p + 1)) := by
  intro s
  simp

/-- Helper for Corollary 18.14: the scalar power owner is convex once `β ≥ 0` and `p + 1 > 1`. -/
lemma powerControl_convexOn
    (hβ : 0 ≤ β) (hp₁ : 1 < p + 1) :
    _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ β * |s| ^ (p + 1)) := by
  -- Start from the canonical strict convexity of `s ↦ ‖s‖^(p + 1)` on `ℝ`.
  have hbase :
      _root_.ConvexOn ℝ Set.univ (fun s : ℝ ↦ ‖s‖ ^ (p + 1)) :=
    (strictConvexOn_norm_rpow (H := ℝ) (p := p + 1) hp₁).convexOn
  simpa [Real.norm_eq_abs, smul_eq_mul] using hbase.smul hβ

/-- Helper for Corollary 18.14: the scalar power owner vanishes exactly at `0`. -/
lemma powerControl_zero_iff
    (hβ : 0 < β) (hp₀ : 0 < p) :
    ∀ s : ℝ, β * |s| ^ (p + 1) = 0 ↔ s = 0 := by
  intro s
  have hp1_ne : p + 1 ≠ 0 := by linarith
  constructor
  · intro hs
    have habs_pow : |s| ^ (p + 1) = 0 := by
      exact (mul_eq_zero.mp hs).resolve_left hβ.ne'
    have habs : |s| = 0 := (Real.rpow_eq_zero (abs_nonneg s) hp1_ne).1 habs_pow
    exact abs_eq_zero.mp habs
  · intro hs
    simp [hs, Real.zero_rpow hp1_ne]

section

variable [CompleteSpace H]

/-- Helper for Corollary 18 14: away from the origin, the owner-side modulus `ψ` of the even
power control `s ↦ β * |s|^(p + 1)` simplifies to the displayed power slope `β * s^p` on
nonnegative inputs. -/
lemma psi_power_control_eq_powerSlope_of_nonneg_ne
    {s : ℝ} (hs_nonneg : 0 ≤ s) (hs : s ≠ 0) :
    ψ (fun t : ℝ ↦ β * |t| ^ (p + 1)) s = powerSlope s := by
  have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg hs.symm
  have hsplit : s ^ (p + 1) = s ^ p * s := by
    rw [Real.rpow_add hs_pos p 1]
    simp
  -- On nonzero nonnegative inputs, the quotient formula for `ψ` reduces to one power of `s`.
  rw [psi_eq_div_abs_of_ne _ hs, abs_of_nonneg hs_nonneg, hsplit]
  field_simp [hs]

/-- Helper for Corollary 18 14: the hypothesis of clause (1) is exactly the `ψ`-bound required by
Theorem 18.13 once the power control is viewed through its even owner `s ↦ β * |s|^(p + 1)`. -/
lemma gradient_norm_le_psi_power_control_on_norm
    (hi : ∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ powerSlope ‖x - y‖) :
    ∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ ψ (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖x - y‖ := by
  intro x y
  by_cases hxy : ‖x - y‖ = 0
  · -- At the origin, `ψ` vanishes by definition, so the hypothesis already forces equality.
    have hxy_eq : x = y := sub_eq_zero.mp (norm_eq_zero.mp hxy)
    simp [hxy_eq, psi_zero]
  · -- Away from the origin, the `ψ`-surface is exactly the displayed power slope.
    rw [psi_power_control_eq_powerSlope_of_nonneg_ne (norm_nonneg _) hxy]
    exact hi x y

/-- Helper for Corollary 18 14: clause (1) is Theorem 18.13 specialized to the power owner once
the missing owner-side origin condition is supplied explicitly. -/
theorem gradient_inner_le_power_bound_of_gradient_norm_le_power_bound_of_powerControl_zero_nonneg
    (h0 : 0 ≤ powerControl 0)
    (hi : ∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ powerSlope ‖x - y‖) (x y : H) :
    ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ powerControl ‖x - y‖ := by
  -- First bound the inner product by the norm product.
  have hinner :
      ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ ‖x - y‖ * ‖∇ f x - ∇ f y‖ := by
    simpa [mul_comm] using real_inner_le_norm (x - y) (∇ f x - ∇ f y)
  have hgrad :
      ‖x - y‖ * ‖∇ f x - ∇ f y‖ ≤ ‖x - y‖ * powerSlope ‖x - y‖ := by
    exact mul_le_mul_of_nonneg_left (hi x y) (norm_nonneg _)
  have hmodel :
      ‖x - y‖ * powerSlope ‖x - y‖ ≤ powerControl ‖x - y‖ := by
    by_cases hxy : ‖x - y‖ = 0
    · simpa [hxy] using h0
    · have hxy_nonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
      have hxy_pos : 0 < ‖x - y‖ := lt_of_le_of_ne hxy_nonneg (Ne.symm hxy)
      have hsplit : ‖x - y‖ ^ (p + 1) = ‖x - y‖ ^ p * ‖x - y‖ := by
        rw [Real.rpow_add hxy_pos p 1]
        simp
      have hEq : ‖x - y‖ * powerSlope ‖x - y‖ = powerControl ‖x - y‖ := by
        calc
          ‖x - y‖ * powerSlope ‖x - y‖ = ‖x - y‖ * (β * ‖x - y‖ ^ p) := by rfl
          _ = β * (‖x - y‖ ^ p * ‖x - y‖) := by ring
          _ = β * ‖x - y‖ ^ (p + 1) := by rw [← hsplit]
          _ = powerControl ‖x - y‖ := by rfl
      exact le_of_eq hEq
  exact hinner.trans <| hgrad.trans hmodel

-- Proof sketch: specialize Theorem 18.13 (1) to the power control
-- `φ(s) = β * |s|^(p + 1)`. Its owner-side auxiliary modulus `ψ φ` is the expected
-- `β * |s|^p` away from the origin, so the Cauchy--Schwarz reduction built into Theorem 18.13
-- gives the stated power-law inner-product bound.
/-- Clause (i) of Corollary 18.14: the power-law gradient bound implies the corresponding
inner-product
bound. -/
theorem gradient_inner_le_power_bound_of_gradient_norm_le_power_bound
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hi : ∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ powerSlope ‖x - y‖) (x y : H) :
    ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ powerControl ‖x - y‖ := by
  let _ := hdiff
  let _ := hconv
  let _ := hβ
  let _ := hp₁
  have h0 : 0 ≤ powerControl 0 := by
    have hp1_ne : p + 1 ≠ 0 := by linarith
    change 0 ≤ β * (0 : ℝ) ^ (p + 1)
    simp [Real.zero_rpow hp1_ne]
  -- The public theorem is just the source-facing wrapper around the norm-product estimate.
  exact
    gradient_inner_le_power_bound_of_gradient_norm_le_power_bound_of_powerControl_zero_nonneg
      (β := β) (p := p) h0 hi x y

section

variable [CompleteSpace H]

/-- Helper for Corollary 18.14: on nonnegative inputs, the integral remainder `θ` of the power
owner is the displayed power remainder `β / (p + 1) * s^(p + 1)`. -/
lemma theta_power_control_eq_powerRemainder_of_nonneg
    (hβ : 0 < β) (hp₀ : 0 < p) {s : ℝ} (hs : 0 ≤ s) :
    θ (fun t : ℝ ↦ β * |t| ^ (p + 1)) s = powerRemainder s := by
  let _ := hβ
  rw [theta_apply]
  have hintegral :
      ∫ t in (0 : ℝ)..1, (β * |s * t| ^ (p + 1)) / t =
        ∫ t in (0 : ℝ)..1, t ^ p * (β * s ^ (p + 1)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t
    intro ht
    have ht_mem : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa using ht
    have ht_pos : 0 < t := ht_mem.1
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have hst_nonneg : 0 ≤ s * t := mul_nonneg hs ht_nonneg
    have ht_split : t ^ (p + 1) = t ^ p * t := by
      rw [Real.rpow_add ht_pos p 1]
      simp
    calc
      (β * |s * t| ^ (p + 1)) / t
          = (β * (s ^ (p + 1) * t ^ (p + 1))) / t := by
              rw [abs_of_nonneg hst_nonneg, Real.mul_rpow hs ht_nonneg]
      _ = (β * (s ^ (p + 1) * (t ^ p * t))) / t := by rw [ht_split]
      _ = t ^ p * (β * s ^ (p + 1)) := by field_simp [ht_pos.ne']
  -- Rewrite the integral into the model scalar integral `∫_0^1 t^p`.
  rw [hintegral, intervalIntegral.integral_mul_const]
  have hrpow :
      ∫ t in (0 : ℝ)..1, t ^ p = 1 / (p + 1) := by
    have hp1_ne : p + 1 ≠ 0 := by linarith
    rw [integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (r := p) (Or.inl (by linarith : -1 < p))]
    simp [Real.zero_rpow hp1_ne]
  calc
    (∫ t in (0 : ℝ)..1, t ^ p) * (β * s ^ (p + 1))
        = (1 / (p + 1)) * (β * s ^ (p + 1)) := by rw [hrpow]
    _ = β / (p + 1) * s ^ (p + 1) := by ring

/-- Helper for Corollary 18.14: the integral remainder of the power owner is the even scalar
function `s ↦ β * |s|^(p + 1) / (p + 1)`. -/
lemma theta_power_control_eq_scaledAbsRpowDivided
    (hβ : 0 < β) (hp₀ : 0 < p) (s : ℝ) :
    θ (fun t : ℝ ↦ β * |t| ^ (p + 1)) s = β * |s| ^ (p + 1) / (p + 1) := by
  by_cases hs : 0 ≤ s
  · -- On the nonnegative branch, the power remainder is already the displayed formula.
    rw [theta_power_control_eq_powerRemainder_of_nonneg (β := β) (p := p) hβ hp₀ hs,
      abs_of_nonneg hs]
    ring
  · have hs_neg : s < 0 := lt_of_not_ge hs
    have hs_nonneg : 0 ≤ -s := by linarith
    have htheta_even :
        Function.Even (θ (fun t : ℝ ↦ β * |t| ^ (p + 1))) :=
      theta_even (φ := fun t : ℝ ↦ β * |t| ^ (p + 1)) (powerControl_even (β := β) (p := p))
    -- On the negative branch, reduce to the positive point `-s` via evenness.
    rw [← htheta_even s,
      theta_power_control_eq_powerRemainder_of_nonneg (β := β) (p := p) hβ hp₀ hs_nonneg,
      abs_of_neg hs_neg]
    ring

end

end

-- Proof sketch: specialize Theorem 18.13 (2) to the same power control
-- `φ(s) = β * |s|^(p + 1)`. The owner remainder `θ φ` is exactly
-- `s ↦ β / (p + 1) * |s|^(p + 1)`.
/-- Clause (ii) of Corollary 18.14: the bound
`⟪x - y, ∇f(x) - ∇f(y)⟫ ≤ β ‖x - y‖^(p+1)` implies the descent estimate
`f(y) ≤ f(x) + ⟪y - x, ∇f(x)⟫ + β/(p+1) ‖x - y‖^(p+1)`. -/
theorem descent_le_linearization_add_power_bound_of_gradient_inner_le_power_bound
    [CompleteSpace H]
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hii : ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ powerControl ‖x - y‖)
    (x y : H) :
    f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + powerRemainder ‖x - y‖ := by
  let _ := hp₁
  have hp1 : 1 < p + 1 := by linarith
  have hφ_even := powerControl_even (β := β) (p := p)
  have hφ_conv := powerControl_convexOn (β := β) (p := p) hβ.le hp1
  have hφ_zero := powerControl_zero_iff (β := β) (p := p) hβ hp₀
  have hii' :
      ∀ a b : H,
        ⟪a - b, ∇ f a - ∇ f b⟫_ℝ ≤ (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖a - b‖ := by
    intro a b
    simpa [abs_of_nonneg (norm_nonneg _)] using hii a b
  have hdescent :=
    descent_le_linearization_add_theta_of_gradient_inner_le_phi
      (φ := fun s : ℝ ↦ β * |s| ^ (p + 1))
      (f := f) hdiff hconv hφ_even hφ_conv hφ_zero hii' x y
  have htheta :
      θ (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖x - y‖ = powerRemainder ‖x - y‖ :=
    theta_power_control_eq_powerRemainder_of_nonneg (β := β) (p := p) hβ hp₀ (norm_nonneg _)
  -- Replace the abstract remainder `θ` by its closed power formula on the norm argument.
  rw [htheta] at hdescent
  exact hdescent

section

variable [CompleteSpace H]

/-- Helper for Corollary 18.14: on nonnegative inputs, the conjugate remainder `θ*` of the power
owner is the explicit conjugate power `β^(-1/p) * p/(p + 1) * s^(1 + 1/p)`. -/
lemma thetaStar_power_control_eq_conjugatePower_of_nonneg
    (hβ : 0 < β) (hp₀ : 0 < p) {r : ℝ} (hr : 0 ≤ r) :
    thetaStar (fun s : ℝ ↦ β * |s| ^ (p + 1)) r = (conjugatePower r : EReal) := by
  let q : ℝ := Real.conjExponent (p + 1)
  let g : ℝ → EReal := (fun x : ℝ ↦ |x| ^ (p + 1) / (p + 1)).toEReal.asEReal
  have hp1 : 1 < p + 1 := by linarith
  have hφ_even := powerControl_even (β := β) (p := p)
  have hφ_conv := powerControl_convexOn (β := β) (p := p) hβ.le hp1
  have hφ_zero := powerControl_zero_iff (β := β) (p := p) hβ hp₀
  have hasEReal :=
    thetaStar_asEReal_of_nonneg
      (φ := fun s : ℝ ↦ β * |s| ^ (p + 1)) hφ_even hφ_conv hφ_zero hr
  have htheta :
      ((θ (fun s : ℝ ↦ β * |s| ^ (p + 1))).toEReal.asEReal) =
        fun x : ℝ ↦ ((β : ℝ) : EReal) * g x := by
    funext x
    rw [Function.asEReal_apply, Function.toEReal_apply,
      theta_power_control_eq_scaledAbsRpowDivided (β := β) (p := p) hβ hp₀ x]
    simp [g, div_eq_mul_inv, mul_assoc]
  have hscaled :
      thetaConj (fun s : ℝ ↦ β * |s| ^ (p + 1)) r =
        ((β : ℝ) : EReal) * g∗ (((β : ℝ)⁻¹) * r) := by
    rw [thetaConj, htheta]
    simpa [g, smul_eq_mul] using
      congrFun (conjugate_pos_smul (f := g) ⟨β, hβ⟩) r
  have hbase :
      g∗ (((β : ℝ)⁻¹) * r) =
        (((|((β : ℝ)⁻¹ * r)| ^ q / q : ℝ) : EReal)) := by
    simpa [g, q] using conjugate_absRpowDivided (p + 1) hp1 (((β : ℝ)⁻¹) * r)
  have hpq : (p + 1).HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp1
  have hq_formula : q = 1 + 1 / p := by
    calc
      q = (p + 1) / ((p + 1) - 1) := hpq.conjugate_eq
      _ = 1 + 1 / p := by
        field_simp [hp₀.ne']
        ring
  have hbeta_pow :
      β * (β⁻¹ * r) ^ (1 + 1 / p) = β ^ (-1 / p) * r ^ (1 + 1 / p) := by
    have hmul :
        (β⁻¹ * r) ^ (1 + 1 / p) = (β⁻¹) ^ (1 + 1 / p) * r ^ (1 + 1 / p) := by
      exact Real.mul_rpow (inv_nonneg.2 hβ.le) hr
    calc
      β * (β⁻¹ * r) ^ (1 + 1 / p)
          = β * ((β⁻¹) ^ (1 + 1 / p) * r ^ (1 + 1 / p)) := by rw [hmul]
      _ = (β * (β⁻¹) ^ (1 + 1 / p)) * r ^ (1 + 1 / p) := by ring
      _ = β ^ (-1 / p) * r ^ (1 + 1 / p) := by
            congr 1
            calc
              β * (β⁻¹) ^ (1 + 1 / p) = β ^ (1 : ℝ) * (β⁻¹) ^ (1 + 1 / p) := by
                rw [Real.rpow_one]
              _ = β ^ (1 : ℝ) * (β ^ (1 + 1 / p))⁻¹ := by rw [Real.inv_rpow hβ.le]
              _ = β ^ (1 : ℝ) * β ^ (-(1 + 1 / p)) := by rw [Real.rpow_neg hβ.le]
              _ = β ^ ((1 : ℝ) - (1 + 1 / p)) := by
                    rw [← Real.rpow_add hβ 1 (-(1 + 1 / p))]
                    ring
              _ = β ^ (-1 / p) := by congr 1; ring
  have hreal :
      β * (|((β : ℝ)⁻¹ * r)| ^ q / q) = conjugatePower r := by
    have habs : |((β : ℝ)⁻¹ * r)| = (β : ℝ)⁻¹ * r := by
      rw [abs_of_nonneg]
      positivity
    rw [habs, hq_formula]
    calc
      β * (((β : ℝ)⁻¹ * r) ^ (1 + 1 / p) / (1 + 1 / p))
          = (β * ((β : ℝ)⁻¹ * r) ^ (1 + 1 / p)) / (1 + 1 / p) := by ring
      _ = (β ^ (-1 / p) * r ^ (1 + 1 / p)) / (1 + 1 / p) := by rw [hbeta_pow]
      _ = β ^ (-1 / p) * p / (p + 1) * r ^ (1 + 1 / p) := by field_simp [hp₀.ne']
  have hconj :
      thetaConj (fun s : ℝ ↦ β * |s| ^ (p + 1)) r = (conjugatePower r : EReal) := by
    rw [hscaled, hbase, EReal.coe_mul]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  -- The source-facing `θ*` is definitionally the same conjugate owner on nonnegative inputs.
  calc
    thetaStar (fun s : ℝ ↦ β * |s| ^ (p + 1)) r
        = thetaConj (fun s : ℝ ↦ β * |s| ^ (p + 1)) r := hasEReal
    _ = (conjugatePower r : EReal) := hconj

/-- Helper for Corollary 18.14: the scalar inequality
`2 * conjugatePower ν ≤ ν * s` forces the recovery bound
`ν ≤ β * ((p + 1) / (2p))^p * s^p`. -/
lemma conjugatePower_bound_yields_powerRecovery
    (hβ : 0 < β) (hp₀ : 0 < p) {ν s : ℝ}
    (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hbound : 2 * conjugatePower ν ≤ ν * s) :
    ν ≤ powerRecovery s := by
  by_cases hν0 : ν = 0
  · subst hν0
    change 0 ≤ powerRecovery s
    positivity
  · have hν_pos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
    have hsplit : ν ^ (1 + 1 / p) = ν * ν ^ (1 / p) := by
      rw [Real.rpow_add hν_pos 1 (1 / p), Real.rpow_one, mul_comm]
    have hroot_scaled :
        ν * (2 * β ^ (-1 / p) * p / (p + 1) * ν ^ (1 / p)) ≤ ν * s := by
      calc
        ν * (2 * β ^ (-1 / p) * p / (p + 1) * ν ^ (1 / p))
            = 2 * conjugatePower ν := by
                rw [show conjugatePower ν = β ^ (-1 / p) * p / (p + 1) * ν ^ (1 + 1 / p) by rfl,
                  hsplit]
                ring
        _ ≤ ν * s := hbound
    have hroot :
        2 * β ^ (-1 / p) * p / (p + 1) * ν ^ (1 / p) ≤ s :=
      le_of_mul_le_mul_left hroot_scaled hν_pos
    have hmult :
        β ^ (1 / p) * ((p + 1) / (2 * p)) *
          (2 * β ^ (-1 / p) * p / (p + 1)) = 1 := by
      have hbeta_cancel : β ^ (1 / p) * β ^ (-1 / p) = 1 := by
        calc
          β ^ (1 / p) * β ^ (-1 / p) = β ^ ((1 / p) + (-1 / p)) := by
            symm
            exact Real.rpow_add hβ (1 / p) (-1 / p)
          _ = β ^ (0 : ℝ) := by congr 1; ring
          _ = 1 := by simp
      calc
        β ^ (1 / p) * ((p + 1) / (2 * p)) *
            (2 * β ^ (-1 / p) * p / (p + 1))
            = (β ^ (1 / p) * β ^ (-1 / p)) *
                (((p + 1) / (2 * p)) * (2 * p / (p + 1))) := by ring
        _ = 1 := by
              rw [hbeta_cancel]
              field_simp [hp₀.ne']
    have hroot_le :
        ν ^ (1 / p) ≤ β ^ (1 / p) * ((p + 1) / (2 * p)) * s := by
      have hmul_nonneg : 0 ≤ β ^ (1 / p) * ((p + 1) / (2 * p)) := by positivity
      have hscaled :=
        mul_le_mul_of_nonneg_left hroot hmul_nonneg
      have hscaled' :
          (β ^ (1 / p) * ((p + 1) / (2 * p)) *
              (2 * β ^ (-1 / p) * p / (p + 1))) * ν ^ (1 / p) ≤
            β ^ (1 / p) * ((p + 1) / (2 * p)) * s := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
      rw [hmult, one_mul] at hscaled'
      exact hscaled'
    have htarget :
        ν ≤ (β ^ (1 / p) * ((p + 1) / (2 * p)) * s) ^ p := by
      exact
        (Real.rpow_inv_le_iff_of_pos hν (by positivity) hp₀).1
          (by simpa [one_div] using hroot_le)
    have hratio_nonneg : 0 ≤ (p + 1) / (2 * p) := by positivity
    calc
      ν ≤ (β ^ (1 / p) * ((p + 1) / (2 * p)) * s) ^ p := htarget
      _ = (β ^ (1 / p)) ^ p * (((p + 1) / (2 * p) * s) ^ p) := by
            rw [show β ^ (1 / p) * ((p + 1) / (2 * p)) * s =
                (β ^ (1 / p)) * (((p + 1) / (2 * p)) * s) by ring]
            rw [Real.mul_rpow (by positivity) (mul_nonneg hratio_nonneg hs)]
      _ = β * (((p + 1) / (2 * p) * s) ^ p) := by
            have hbeta_pow : (β ^ (1 / p)) ^ p = β := by
              calc
                (β ^ (1 / p)) ^ p = β ^ ((1 / p) * p) := by rw [Real.rpow_mul hβ.le]
                _ = β ^ (1 : ℝ) := by
                      congr 1
                      field_simp [hp₀.ne']
                _ = β := by rw [Real.rpow_one]
            rw [hbeta_pow]
      _ = β * (((p + 1) / (2 * p)) ^ p * s ^ p) := by
            rw [Real.mul_rpow hratio_nonneg hs]
      _ = powerRecovery s := by ring

-- Proof sketch: specialize Theorem 18.13 (3) to the same `φ`, so the owner-side remainder is
-- `θ φ(s) = β / (p + 1) * |s|^(p + 1)`. Then compute the scalar conjugate
-- `(θ φ).toEReal.asEReal∗` using Example 13.2(i) together with the positive-scaling formula from
-- Proposition 13.23(i).
/-- Clause (iii) of Corollary 18.14: the descent estimate with remainder
`β/(p+1) ‖x - y‖^(p+1)` implies the lower bound for the Fenchel conjugate
`f*` along the gradient image, with conjugate power exponent `1 + 1/p`. -/
theorem
    conjugate_gradient_ge_affine_add_conjugate_power_of_descent_power_bound
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hiii :
      ∀ x y : H,
        f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + powerRemainder ‖x - y‖)
    (x y : H) :
    f.toEReal.asEReal∗ (∇ f y) ≥
      f.toEReal.asEReal∗ (∇ f x) +
        (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
          (conjugatePower ‖∇ f x - ∇ f y‖ : EReal) := by
  let _ := hp₁
  have hp1 : 1 < p + 1 := by linarith
  have hφ_even := powerControl_even (β := β) (p := p)
  have hφ_conv := powerControl_convexOn (β := β) (p := p) hβ.le hp1
  have hφ_zero := powerControl_zero_iff (β := β) (p := p) hβ hp₀
  have hiii' :
      ∀ a b : H,
        f b ≤ f a + ⟪b - a, ∇ f a⟫_ℝ +
          θ (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖a - b‖ := by
    intro a b
    have htheta :
        θ (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖a - b‖ = powerRemainder ‖a - b‖ :=
      theta_power_control_eq_powerRemainder_of_nonneg
        (β := β) (p := p) hβ hp₀ (norm_nonneg _)
    -- Repackage clause (iii) into the owner surface required by Theorem 18.13.
    calc
      f b ≤ f a + ⟪b - a, ∇ f a⟫_ℝ + powerRemainder ‖a - b‖ := hiii a b
      _ = f a + ⟪b - a, ∇ f a⟫_ℝ +
            θ (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖a - b‖ := by rw [htheta]
  have hconj :=
    conjugate_gradient_ge_affine_add_thetaConjugate_of_descent_le_linearization_add_theta
      (φ := fun s : ℝ ↦ β * |s| ^ (p + 1))
      (f := f) hdiff hconv hφ_even hφ_conv hφ_zero hiii' x y
  have hthetaStar :
      thetaStar (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖∇ f x - ∇ f y‖ =
        (conjugatePower ‖∇ f x - ∇ f y‖ : EReal) :=
    thetaStar_power_control_eq_conjugatePower_of_nonneg
      (β := β) (p := p) hβ hp₀ (norm_nonneg _)
  -- Replace the abstract conjugate owner by the explicit scalar power.
  simpa [hthetaStar] using hconj

-- Proof sketch: apply Theorem 18.13 (4) to the owner-side conjugate term from clause (iii), then
-- simplify that specialized scalar conjugate to the explicit power
-- `β^(-1 / p) * p / (p + 1) * |s|^(1 + 1 / p)`.
/-- Clause (iv) of Corollary 18.14: the Fenchel-conjugate lower bound from clause (iv) implies the
lower
coercivity estimate
`⟪x - y, ∇f(x) - ∇f(y)⟫ ≥ 2 β^(-1/p) p/(p+1) ‖∇f(x) - ∇f(y)‖^(1 + 1/p)`. -/
theorem
    gradient_inner_ge_two_conjugate_power_of_conjugate_gradient_bound
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hiv :
      ∀ x y : H,
        f.toEReal.asEReal∗ (∇ f y) ≥
        f.toEReal.asEReal∗ (∇ f x) +
            (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
              (conjugatePower ‖∇ f x - ∇ f y‖ : EReal))
    (x y : H) :
    ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≥
      2 * conjugatePower ‖∇ f x - ∇ f y‖ := by
  let _ := hp₁
  have hp1 : 1 < p + 1 := by linarith
  have hφ_even := powerControl_even (β := β) (p := p)
  have hφ_conv := powerControl_convexOn (β := β) (p := p) hβ.le hp1
  have hφ_zero := powerControl_zero_iff (β := β) (p := p) hβ hp₀
  have hiv' :
      ∀ a b : H,
        f.toEReal.asEReal∗ (∇ f b) ≥
          f.toEReal.asEReal∗ (∇ f a) +
            (⟪a, ∇ f b - ∇ f a⟫_ℝ : EReal) +
              thetaStar (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖∇ f a - ∇ f b‖ := by
    intro a b
    have hthetaStar :
        thetaStar (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖∇ f a - ∇ f b‖ =
          (conjugatePower ‖∇ f a - ∇ f b‖ : EReal) :=
      thetaStar_power_control_eq_conjugatePower_of_nonneg
        (β := β) (p := p) hβ hp₀ (norm_nonneg _)
    -- Rewrite the source-facing assumption onto the abstract `θ*` owner.
    simpa [hthetaStar] using hiv a b
  have hpair :=
    gradient_inner_ge_two_thetaConjugate_of_conjugate_gradient_ge_affine_add_thetaConjugate
      (φ := fun s : ℝ ↦ β * |s| ^ (p + 1))
      (f := f) hdiff hconv hφ_even hφ_conv hφ_zero hiv' x y
  have hthetaStar :
      thetaStar (fun s : ℝ ↦ β * |s| ^ (p + 1)) ‖∇ f x - ∇ f y‖ =
        (conjugatePower ‖∇ f x - ∇ f y‖ : EReal) :=
    thetaStar_power_control_eq_conjugatePower_of_nonneg
      (β := β) (p := p) hβ hp₀ (norm_nonneg _)
  -- Turn the `EReal` estimate back into the displayed real inequality.
  rw [hthetaStar, EReal.coe_mul] at hpair
  have hpair' :
      ((⟪x - y, ∇ f x - ∇ f y⟫_ℝ : ℝ) : EReal) ≥
        (((2 * conjugatePower ‖∇ f x - ∇ f y‖ : ℝ)) : EReal) := by
    simpa using hpair
  exact_mod_cast hpair'

-- Proof sketch: combine the lower bound from clause (iv) with Cauchy--Schwarz and solve the
-- resulting scalar inequality for `‖∇f(x) - ∇f(y)‖`. On the owner side, this is exactly the
-- `ϱ`-bound from Theorem 18.13 specialized to `φ(s) = β * |s|^(p + 1)`, which simplifies to the
-- displayed recovery modulus.
/-- Clause (v) of Corollary 18.14: the coercivity estimate from clause (v) implies the Hölder
bound
`‖∇f(x) - ∇f(y)‖ ≤ β ((p+1)/(2p))^p ‖x - y‖^p`. -/
theorem gradient_norm_le_scaled_power_bound_of_gradient_inner_ge_two_conjugate_power_bound
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hv :
      ∀ x y : H,
        ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≥
          2 * conjugatePower ‖∇ f x - ∇ f y‖)
    (x y : H) :
    ‖∇ f x - ∇ f y‖ ≤ powerRecovery ‖x - y‖ := by
  let _ := hdiff
  let _ := hconv
  let _ := hp₁
  let ν : ℝ := ‖∇ f x - ∇ f y‖
  let s : ℝ := ‖x - y‖
  have hinner :
      ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ ν * s := by
    -- Cauchy--Schwarz turns the geometric estimate into the scalar admissibility inequality.
    simpa [ν, s, mul_comm] using real_inner_le_norm (x - y) (∇ f x - ∇ f y)
  have hbound : 2 * conjugatePower ν ≤ ν * s := by
    exact le_trans (by simpa [ν] using hv x y) hinner
  exact
    conjugatePower_bound_yields_powerRecovery
      (β := β) (p := p) hβ hp₀ (ν := ν) (s := s)
      (norm_nonneg _) (norm_nonneg _) hbound

-- Proof sketch: the source-facing corollary is just the conjunction of the five already-proved
-- clause implications above, all under the same standing hypotheses on `f`, `β`, and `p`.
/-- Helper for Corollary 18.14: package the five displayed clause implications into one proved
conjunction. -/
theorem powerImplicationChain
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    ((∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ powerSlope ‖x - y‖) →
      ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ powerControl ‖x - y‖) ∧
    ((∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ powerControl ‖x - y‖) →
      ∀ x y : H, f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + powerRemainder ‖x - y‖) ∧
    ((∀ x y : H, f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + powerRemainder ‖x - y‖) →
      ∀ x y : H,
        f.toEReal.asEReal∗ (∇ f y) ≥
          f.toEReal.asEReal∗ (∇ f x) +
            (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
              (conjugatePower ‖∇ f x - ∇ f y‖ : EReal)) ∧
    ((∀ x y : H,
        f.toEReal.asEReal∗ (∇ f y) ≥
          f.toEReal.asEReal∗ (∇ f x) +
            (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
              (conjugatePower ‖∇ f x - ∇ f y‖ : EReal)) →
      ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≥ 2 * conjugatePower ‖∇ f x - ∇ f y‖) ∧
    ((∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≥ 2 * conjugatePower ‖∇ f x - ∇ f y‖) →
      ∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ powerRecovery ‖x - y‖) := by
  constructor
  · intro hi x y
    exact
      gradient_inner_le_power_bound_of_gradient_norm_le_power_bound
        (f := f) (β := β) (p := p) hdiff hconv hβ hp₀ hp₁ hi x y
  constructor
  · intro hii x y
    exact
      descent_le_linearization_add_power_bound_of_gradient_inner_le_power_bound
        (f := f) (β := β) (p := p) hdiff hconv hβ hp₀ hp₁ hii x y
  constructor
  · intro hiii x y
    exact
      conjugate_gradient_ge_affine_add_conjugate_power_of_descent_power_bound
        (f := f) (β := β) (p := p) hdiff hconv hβ hp₀ hp₁ hiii x y
  constructor
  · intro hiv x y
    exact
      gradient_inner_ge_two_conjugate_power_of_conjugate_gradient_bound
        (f := f) (β := β) (p := p) hdiff hconv hβ hp₀ hp₁ hiv x y
  · intro hv x y
    exact
      gradient_norm_le_scaled_power_bound_of_gradient_inner_ge_two_conjugate_power_bound
        (f := f) (β := β) (p := p) hdiff hconv hβ hp₀ hp₁ hv x y

/-- Corollary 18.14: under the standing differentiability and convexity hypotheses, the power-law
conditions (i)-(vi) form the implication chain `(i) → (ii) → (iii) → (iv) → (v) → (vi)`. -/
theorem corollary_18_14
    (hdiff : Differentiable ℝ f) (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hβ : 0 < β) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    ((∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ powerSlope ‖x - y‖) →
      ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ powerControl ‖x - y‖) ∧
    ((∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ powerControl ‖x - y‖) →
      ∀ x y : H, f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + powerRemainder ‖x - y‖) ∧
    ((∀ x y : H, f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + powerRemainder ‖x - y‖) →
      ∀ x y : H,
        f.toEReal.asEReal∗ (∇ f y) ≥
          f.toEReal.asEReal∗ (∇ f x) +
            (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
              (conjugatePower ‖∇ f x - ∇ f y‖ : EReal)) ∧
    ((∀ x y : H,
        f.toEReal.asEReal∗ (∇ f y) ≥
          f.toEReal.asEReal∗ (∇ f x) +
            (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
              (conjugatePower ‖∇ f x - ∇ f y‖ : EReal)) →
      ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≥ 2 * conjugatePower ‖∇ f x - ∇ f y‖) ∧
    ((∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≥ 2 * conjugatePower ‖∇ f x - ∇ f y‖) →
      ∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ powerRecovery ‖x - y‖) := by
  exact powerImplicationChain (f := f) (β := β) (p := p) hdiff hconv hβ hp₀ hp₁

end

end StrongerDifferentiabilityBounds

end

end ERealFunction
