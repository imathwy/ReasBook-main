import Mathlib
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_40
import BauschkeLean.Chap13.Proposition_13_50

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ERealFunction
open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section FenchelMoreau

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

private theorem absPowerDivided_zero (p : ℝ) (hp : 1 < p) :
    |(0 : ℝ)| ^ p / p = 0 := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  simp [Real.zero_rpow hp_pos.ne']

private theorem absPowerDivided_nonneg (p : ℝ) (hp : 1 < p) (t : ℝ) :
    0 ≤ |t| ^ p / p := by
  exact div_nonneg (Real.rpow_nonneg (abs_nonneg t) p) (le_of_lt (lt_trans zero_lt_one hp))

private theorem toEReal_absPowerDivided_zero (p : ℝ) (hp : 1 < p) :
    (((fun t : ℝ ↦ |t| ^ p / p).toEReal) 0 : EReal) = 0 := by
  have hzero : (((|(0 : ℝ)| ^ p / p : ℝ)) : EReal) = 0 := by
    exact_mod_cast absPowerDivided_zero p hp
  simpa [Function.toEReal_apply] using hzero

private theorem toEReal_absPowerDivided_nonneg (p : ℝ) (hp : 1 < p) (t : ℝ) :
    (((fun s : ℝ ↦ |s| ^ p / p).toEReal) 0 : EReal) ≤
      (((fun s : ℝ ↦ |s| ^ p / p).toEReal) t : EReal) := by
  have hnonneg : (0 : EReal) ≤ (((|t| ^ p / p : ℝ)) : EReal) := by
    exact_mod_cast absPowerDivided_nonneg p hp t
  have hzero : (0 : ℝ) ^ p / p = 0 := by
    simpa using absPowerDivided_zero p hp
  simpa [Function.toEReal_apply, hzero] using hnonneg

/-- Helper for Example 13 51: on `ℝ`, the Fenchel conjugate supremum rewrites to the scalar
formula `sup_x (ux - f(x))`. -/
@[simp] private theorem conjugate_apply_real (f : ℝ → EReal) (u : ℝ) :
    conjugate f u = sSup (Set.range fun x : ℝ ↦ ((u * x : ℝ) : EReal) - f x) := by
  -- Rewrite the inner product on `ℝ` as multiplication and package the indexed supremum as an
  -- `sSup` over the range.
  rw [conjugate_apply, ← sSup_range]
  congr with x

/-- Helper for Example 13 51: an `sSup` is identified by a global upper bound together with
witnesses above every strict lower bound. -/
private theorem supremum_eq_of_pointwise_le_and_dense_lower_bounds
    (g : ℝ → EReal) (a : EReal) (h_upper : ∀ x, g x ≤ a)
    (h_lower : ∀ z, z < a → ∃ x, z < g x) :
    sSup (Set.range g) = a := by
  -- Apply the complete-lattice characterization of `sSup`.
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact h_upper x
  · intro z hz
    rcases h_lower z hz with ⟨x, hx⟩
    exact ⟨g x, ⟨x, rfl⟩, hx⟩

/-- Helper for Example 13 51: the usual Hölder-conjugate maximizer
`sign(u) * |u|^(p* - 1)` attains the scalar value `|u|^(p*) / p*`. -/
private theorem power_conjugate_maximizer_value
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    let q := Real.conjExponent p
    let x0 := Real.sign u * |u| ^ (q - 1)
    u * x0 - |x0| ^ p / p = |u| ^ q / q := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  have hp_ne : p ≠ 0 := hpq.ne_zero
  have hq_ne : q ≠ 0 := hpq.symm.ne_zero
  have hcoeff : 1 - 1 / p = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hqp : (q - 1) * p = q := by
    calc
      (q - 1) * p = (q / p) * p := by rw [hpq.symm.div_conj_eq_sub_one]
      _ = q := by field_simp [hp_ne]
  rcases eq_or_ne u 0 with rfl | hu0
  · have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hpq.symm.sub_one_pos
    -- At the origin, both the extremizing point and the optimal value vanish.
    simp [q, hp_ne, hq_ne, hq_sub_ne]
  · have hu_abs_pos : 0 < |u| := abs_pos.mpr hu0
    have hu_abs_nonneg : 0 ≤ |u| := abs_nonneg u
    have husign : u * Real.sign u = |u| := by
      rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
      · simp [Real.sign_of_neg hu_neg, abs_of_neg hu_neg]
      · simp [Real.sign_of_pos hu_pos, abs_of_pos hu_pos]
    have hsign_abs : |Real.sign u| = 1 := by
      rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
      · simp [Real.sign_of_neg hu_neg]
      · simp [Real.sign_of_pos hu_pos]
    have hx0_abs : |x0| = |u| ^ (q - 1) := by
      -- The sign contributes only an absolute value of `1`.
      simp [x0, abs_mul, hsign_abs, abs_of_nonneg (Real.rpow_nonneg hu_abs_nonneg _)]
    have hux0 : u * x0 = |u| ^ q := by
      -- First recover `|u|` from the sign, then combine the powers additively.
      calc
        u * x0 = (u * Real.sign u) * |u| ^ (q - 1) := by simp [x0, mul_assoc]
        _ = |u| * |u| ^ (q - 1) := by rw [husign]
        _ = |u| ^ (1 : ℝ) * |u| ^ (q - 1) := by simp
        _ = |u| ^ ((1 : ℝ) + (q - 1)) := by
          symm
          exact Real.rpow_add hu_abs_pos 1 (q - 1)
        _ = |u| ^ q := by congr 1; ring
    have hx0_pow : |x0| ^ p = |u| ^ q := by
      -- The Hölder-conjugate identity turns `(q - 1) * p` into `q`.
      rw [hx0_abs, ← Real.rpow_mul hu_abs_nonneg (q - 1) p, hqp]
    -- Substitute the maximizing value and simplify `1 - 1 / p = 1 / q`.
    calc
      u * x0 - |x0| ^ p / p = |u| ^ q - |u| ^ q / p := by rw [hux0, hx0_pow]
      _ = |u| ^ q * (1 - 1 / p) := by ring
      _ = |u| ^ q * (1 / q) := by rw [hcoeff]
      _ = |u| ^ q / q := by ring

/-- Helper for Example 13 51: the scalar conjugate of `x ↦ |x|^p / p` is the conjugate-power
kernel `u ↦ |u|^(p*) / p*`. -/
private theorem conjugate_absRpowDivided
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    conjugate ((fun x : ℝ ↦ |x| ^ p / p).toEReal.asEReal) u =
      ((fun x : ℝ ↦ |x| ^ Real.conjExponent p / Real.conjExponent p).toEReal.asEReal) u := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  rw [conjugate_apply_real]
  simp only [Function.asEReal_apply, Function.toEReal_apply]
  -- Bound the scalar affine defect by Young's inequality and then realize equality at `x0`.
  refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
      (fun x : ℝ ↦ ((u * x : ℝ) : EReal) - ((|x| ^ p / p : ℝ) : EReal))
      ((|u| ^ q / q : ℝ) : EReal) ?_ ?_
  · intro x
    have hmul : u * x ≤ |x| * |u| := by
      calc
        u * x ≤ |u * x| := le_abs_self (u * x)
        _ = |u| * |x| := by rw [abs_mul]
        _ = |x| * |u| := by ring
    have hyoung :
        |x| * |u| ≤ |x| ^ p / p + |u| ^ q / q := by
      simpa [q, abs_abs] using Real.young_inequality_of_nonneg (abs_nonneg x) (abs_nonneg u) hpq
    have hreal : u * x - |x| ^ p / p ≤ |u| ^ q / q := by
      linarith
    have hEReal :
        ((u * x - |x| ^ p / p : ℝ) : EReal) ≤ ((|u| ^ q / q : ℝ) : EReal) :=
      EReal.coe_le_coe hreal
    simpa [sub_eq_add_neg, ← EReal.coe_sub] using hEReal
  · intro z hz
    have hvalue_real : u * x0 - |x0| ^ p / p = |u| ^ q / q := by
      simpa [q, x0] using power_conjugate_maximizer_value p hp u
    have hvalue :
        (((u * x0 : ℝ) : EReal) - ((|x0| ^ p / p : ℝ) : EReal)) =
          ((|u| ^ q / q : ℝ) : EReal) := by
      simpa [sub_eq_add_neg, ← EReal.coe_sub] using
        congrArg (fun t : ℝ ↦ (t : EReal)) hvalue_real
    exact ⟨x0, hz.trans_eq hvalue.symm⟩


-- Proof sketch: start from Example 9.36, which places `t ↦ |t|^p` in `Γ₀(ℝ)` for `p > 1`, then
-- apply the positive scalar-multiplication stability of `Γ₀(ℝ)` to divide by the positive number
-- `p`.
/-- The scalar integrand `t ↦ |t|^p / p` belongs to `Γ₀(ℝ)` for every exponent `p > 1`. -/
theorem absPowerDivided_mem_gammaZero
    (p : ℝ) (hp : 1 < p) :
    (fun t : ℝ ↦ |t| ^ p / p).toEReal ∈ Γ₀(ℝ) := by
  -- Follow the source route through the stable Chapter 9 API: first move `|t|^p` from `Γ₀(ℝ)`
  -- to `Γ(ℝ)`, then scale by the nonnegative real `1 / p`, and finally repackage the real-valued
  -- kernel back into `Γ₀(ℝ)`.
  have habsPower_gamma : (fun t : ℝ ↦ ((|t| ^ p : ℝ) : EReal)) ∈ Γ(ℝ) := by
    simpa [Function.asEReal_apply, Function.toEReal_apply] using
      asEReal_mem_gamma_of_mem_gammaZero (H := ℝ) (absPower_mem_gammaZero p hp)
  have hdiv_gamma : (fun t : ℝ ↦ ((|t| ^ p / p : ℝ) : EReal)) ∈ Γ(ℝ) := by
    simpa [div_eq_mul_inv, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using
      const_mul_mem_gamma_of_nonneg habsPower_gamma (show 0 ≤ 1 / p by positivity)
  exact toEReal_mem_gammaZero_of_mem_gamma hdiv_gamma

-- Proof sketch: apply Proposition 9.40(ii) to the scalar `Γ₀(ℝ)` integrand
-- `t ↦ |t|^p / p`, using that it vanishes at `0` and is everywhere nonnegative.
/-- On any measure space, the integral functional
`X ↦ ∫ ω, |X ω|^p / p ∂P` belongs to `Γ₀(L²((Ω,\mathcal F,P);\mathbb R))` for `p > 1`. -/
theorem integralFunctional_absPowerDivided_mem_gammaZero
    (p : ℝ) (hp : 1 < p) :
    integralFunctional P ((fun t : ℝ ↦ |t| ^ p / p).toEReal) ∈ Γ₀(Ω →₂[P] ℝ) := by
  simpa using
    integralFunctional_mem_gammaZero P ((fun t : ℝ ↦ |t| ^ p / p).toEReal)
      (absPowerDivided_mem_gammaZero p hp)
      (Or.inr ⟨toEReal_absPowerDivided_zero p hp, toEReal_absPowerDivided_nonneg p hp⟩)

variable [P.IsComplete] [SigmaFinite P]

/-- Helper for Example 13 51: local bridge replacing the broken Proposition 13.50 import path for
the scalar integrand `t ↦ |t|^p / p`. -/
private theorem
    conjugate_integralFunctional_absPowerDivided_eq_integralFunctional_gammaZeroConjugate
    (p : ℝ) (hp : 1 < p) :
    ((integralFunctional P ((fun t : ℝ ↦ |t| ^ p / p).toEReal)).asEReal)∗ =
      (integralFunctional P
        (gammaZeroConjugate ((fun t : ℝ ↦ |t| ^ p / p).toEReal)
          (absPowerDivided_mem_gammaZero p hp))).asEReal := by
  -- Specialize the established Chapter 13 integral-conjugation bridge to the scalar power kernel.
  simpa using
    ERealFunction.conjugate_integralFunctional_eq_integralFunctional_gammaZeroConjugate
      (μ := P) (φ := (fun t : ℝ ↦ |t| ^ p / p).toEReal)
      (absPowerDivided_mem_gammaZero p hp)
      (Or.inr ⟨toEReal_absPowerDivided_zero p hp, toEReal_absPowerDivided_nonneg p hp⟩)

-- Proof sketch: rewrite the canonical packaged conjugate `gammaZeroConjugate` of the scalar
-- integrand via Example 13.2(i).
/-- The canonical `Γ₀(ℝ)`-valued conjugate of `t ↦ |t|^p / p` is the concrete conjugate-power
integrand `u ↦ |u|^(p*) / p*`. -/
@[simp] theorem gammaZeroConjugate_absPowerDivided
    (p : ℝ) (hp : 1 < p) :
    gammaZeroConjugate ((fun t : ℝ ↦ |t| ^ p / p).toEReal) (absPowerDivided_mem_gammaZero p hp) =
      (fun t : ℝ ↦ |t| ^ p.conjExponent / p.conjExponent).toEReal := by
  ext u
  simpa [gammaZeroConjugate_apply] using conjugate_absRpowDivided p hp u

-- Proof sketch: specialize Proposition 13.50(ii) to the scalar integrand
-- `t ↦ |t|^p / p`, then rewrite the canonical conjugate integrand `gammaZeroConjugate` via the
-- scalar bridge above.
/-- Example 13 51: on a complete sigma-finite measure space, if
`f(X) = ∫ ω, |X ω|^p / p ∂P` on `L²((Ω,\mathcal F,P);\mathbb R)` with `p ∈ ]1,+∞[`, then
`f* (X) = ∫ ω, |X ω|^{p*} / p* ∂P`, where `p* = p.conjExponent = p / (p - 1)`. -/
theorem fenchelConjugate_integralFunctional_absPowerDivided_eq_integralFunctional_conjExponent
    (p : ℝ) (hp : 1 < p) :
    ((integralFunctional P ((fun t : ℝ ↦ |t| ^ p / p).toEReal)).asEReal)∗ =
      (integralFunctional P
        ((fun t : ℝ ↦ |t| ^ p.conjExponent / p.conjExponent).toEReal)).asEReal := by
  simpa [gammaZeroConjugate_absPowerDivided p hp] using
    conjugate_integralFunctional_absPowerDivided_eq_integralFunctional_gammaZeroConjugate p hp

end FenchelMoreau

end

end ERealFunction
