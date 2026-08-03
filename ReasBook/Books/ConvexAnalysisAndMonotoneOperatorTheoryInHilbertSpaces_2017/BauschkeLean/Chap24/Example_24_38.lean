import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap24.Proposition_24_1
import Mathlib.Analysis.InnerProductSpace.NormPow

namespace ERealFunction

noncomputable section

-- Semantic recall: this item reduces the scalar proximal point computation to the Chapter 24
-- gradient characterization together with the nonnegative control equation
-- `ρ + p γ ρ^(p - 1) = |ξ|`.

/-- The scalar power function `η ↦ |η|^p` packaged as an `]-∞,+∞]`-valued function. -/
abbrev absPowerFunction (p : ℝ) : ℝ → Set.Ioi (⊥ : EReal) :=
  (fun η : ℝ ↦ |η| ^ p).toEReal

@[simp] theorem absPowerFunction_apply (p ξ : ℝ) :
    (absPowerFunction p ξ : EReal) = (|ξ| ^ p : ℝ) :=
  rfl

/-- For `p > 1`, the scalar power function `η ↦ |η|^p` belongs to `Γ₀(ℝ)`. -/
theorem absPowerFunction_mem_gammaZero (p : ℝ) (hp : 1 < p) :
    absPowerFunction p ∈ Γ₀(ℝ) := by
  simpa [absPowerFunction] using absPower_mem_gammaZero p hp

/-- The real cube root, written explicitly so the public formulas use the real-line cube root. -/
def realCubeRoot (x : ℝ) : ℝ :=
  Real.sign x * |x| ^ (1 / 3 : ℝ)

/-- Helper for Example 24.38: on nonnegative inputs, `realCubeRoot` is the usual real power
`x ↦ x^(1/3)`. -/
private theorem realCubeRoot_eq_rpow_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    realCubeRoot x = x ^ (1 / 3 : ℝ) := by
  by_cases hx0 : x = 0
  · simp [realCubeRoot, hx0]
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    simp [realCubeRoot, Real.sign_of_pos hx_pos, abs_of_nonneg hx]

/-- Helper for Example 24.38: the explicit real cube root is nonnegative on `ℝ_+`. -/
private theorem realCubeRoot_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ realCubeRoot x := by
  rw [realCubeRoot_eq_rpow_of_nonneg hx]
  positivity

/-- Helper for Example 24.38: cubing the explicit real cube root recovers the original scalar. -/
private theorem realCubeRoot_cube
    (x : ℝ) :
    realCubeRoot x ^ (3 : ℕ) = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [realCubeRoot]
  · have hsign_abs : |Real.sign x| = 1 := by
      rcases lt_or_gt_of_ne hx0 with hx_neg | hx_pos
      · simp [Real.sign_of_neg hx_neg]
      · simp [Real.sign_of_pos hx_pos]
    have hsign_cube : (Real.sign x : ℝ) ^ (3 : ℕ) = Real.sign x := by
      rcases lt_or_gt_of_ne hx0 with hx_neg | hx_pos
      · norm_num [Real.sign_of_neg hx_neg]
      · norm_num [Real.sign_of_pos hx_pos]
    have hpow :
        (|x| ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = |x| := by
      simpa using Real.rpow_inv_natCast_pow (abs_nonneg x) (by norm_num : (3 : ℕ) ≠ 0)
    calc
      realCubeRoot x ^ (3 : ℕ)
          = (Real.sign x * (|x| ^ (1 / 3 : ℝ))) ^ (3 : ℕ) := by
              simp [realCubeRoot]
      _ = (Real.sign x : ℝ) ^ (3 : ℕ) * (|x| ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
            rw [mul_pow]
      _ = Real.sign x * |x| := by rw [hsign_cube, hpow]
      _ = x := by
            rcases lt_or_gt_of_ne hx0 with hx_neg | hx_pos
            · simp [Real.sign_of_neg hx_neg, abs_of_neg hx_neg]
            · simp [Real.sign_of_pos hx_pos, abs_of_pos hx_pos]

/-- The nonnegative scalar equation whose unique solution yields `Prox_{γ φ} ξ` for
`φ(η) = |η|^p`. -/
def isAbsPowerProxRoot (p : ℝ) (γ : PosReal) (ξ ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ ρ + p * (γ : ℝ) * ρ ^ (p - 1) = |ξ|

/-- Helper for Example 24.38: the finite representative of the scaled absolute-power model is the
real seed `y ↦ γ |y|^p`. -/
private theorem scaled_absPower_toReal
    (p : ℝ) (γ : PosReal) :
    (fun y : ℝ ↦ (((γ • absPowerFunction p) y : EReal).toReal)) =
      fun y : ℝ ↦ (γ : ℝ) * |y| ^ p := by
  -- The positively scaled `EReal` model is still finite everywhere, so `toReal` recovers the
  -- underlying real seed pointwise.
  funext y
  rw [posReal_smul_apply, absPowerFunction_apply, ← EReal.coe_mul, EReal.toReal_coe]

/-- Helper for Example 24.38: positive scaling does not change the effective domain of the scalar
absolute-power model. -/
private theorem scaled_absPower_effectiveDomain
    (p : ℝ) (γ : PosReal) :
    effectiveDomain (γ • absPowerFunction p) = Set.univ := by
  -- Rewrite the scaled owner to its everywhere-finite real seed and read off the effective
  -- domain.
  ext y
  simp [effectiveDomain, ← EReal.coe_mul]

/-- Helper for Example 24.38: every real point lies in the interior effective domain of the scaled
absolute-power model. -/
private theorem scaled_absPower_mem_interior_effectiveDomain
    (p : ℝ) (γ : PosReal) (η : ℝ) :
    η ∈ interior (effectiveDomain (γ • absPowerFunction p)) := by
  -- The effective domain is all of `ℝ`, so its interior is also all of `ℝ`.
  simp [scaled_absPower_effectiveDomain]

/-- Helper for Example 24.38: the finite representative of the scaled absolute-power model has the
expected scalar Gâteaux derivative. -/
private theorem scaled_absPower_hasGateauxDerivativeAt
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (η : ℝ) :
    HasGateauxDerivativeAt
      (fun y : ℝ ↦ (((γ • absPowerFunction p) y : EReal).toReal))
      (InnerProductSpace.toDualMap ℝ ℝ (p * (γ : ℝ) * |η| ^ (p - 2) * η))
      η := by
  -- Differentiate the scalar seed `y ↦ γ |y|^p` first.
  have hseed :
      HasDerivAt
        (fun y : ℝ ↦ (γ : ℝ) * |y| ^ p)
        ((p * (γ : ℝ) * |η| ^ (p - 2) * η))
        η := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_abs_rpow η hp).const_mul (γ : ℝ)
  -- Then transfer that scalar derivative to the finite representative of the scaled owner.
  have htarget :
      HasDerivAt
        (fun y : ℝ ↦ (((γ • absPowerFunction p) y : EReal).toReal))
        (p * (γ : ℝ) * |η| ^ (p - 2) * η)
        η := by
    simpa [scaled_absPower_toReal] using hseed
  have hgrad :
      HasGradientAt
        (fun y : ℝ ↦ (((γ • absPowerFunction p) y : EReal).toReal))
        (p * (γ : ℝ) * |η| ^ (p - 2) * η)
        η := by
    exact htarget.hasGradientAt'
  have hGateaux :
      HasGateauxDerivativeAt
        (fun y : ℝ ↦ (((γ • absPowerFunction p) y : EReal).toReal))
        (InnerProductSpace.toDual ℝ ℝ (p * (γ : ℝ) * |η| ^ (p - 2) * η))
        η := by
    exact hgrad.hasFDerivAt.hasGateauxDerivativeAt
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hGateaux

/-- Helper for Example 24.38: the scalar control map `ρ ↦ ρ + p γ ρ^(p-1)` is strictly
increasing on `ℝ_+`. -/
private theorem abs_power_root_map_strictMonoOn
    (p : ℝ) (hp : 1 < p) (γ : PosReal) :
    StrictMonoOn (fun ρ : ℝ ↦ ρ + p * (γ : ℝ) * ρ ^ (p - 1)) (Set.Ici 0) := by
  intro ρ hρ σ hσ hρσ
  -- Both summands are strictly increasing on `ℝ_+`, so their sum is strictly increasing there.
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_sub_pos : 0 < p - 1 := sub_pos.mpr hp
  have hcoeff_pos : 0 < p * (γ : ℝ) := mul_pos hp_pos γ.2
  have hpow :
      ρ ^ (p - 1) < σ ^ (p - 1) :=
    Real.strictMonoOn_rpow_Ici_of_exponent_pos hp_sub_pos hρ hσ hρσ
  have hscaled :
      p * (γ : ℝ) * ρ ^ (p - 1) <
        p * (γ : ℝ) * σ ^ (p - 1) := by
    exact mul_lt_mul_of_pos_left hpow hcoeff_pos
  linarith

/-- Helper for Example 24.38: the modulus of the actual proximal point satisfies the scalar root
equation `(24.72)`. -/
private theorem prox_absPower_abs_is_root
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (ξ : ℝ) :
    isAbsPowerProxRoot p γ ξ
      |Prox[γ, absPowerFunction p, absPowerFunction_mem_gammaZero p hp] ξ| := by
  let q : ℝ := Prox[γ, absPowerFunction p, absPowerFunction_mem_gammaZero p hp] ξ
  have hstationary :
      p * (γ : ℝ) * |q| ^ (p - 2) * q + q = ξ := by
    -- Proposition 24.1 turns the actual proximal point into the scalar first-order condition.
    exact
      (eq_proximityOperator_iff_gateauxGradient_add_eq
        (γ • absPowerFunction p)
        (smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ)
        (scaled_absPower_mem_interior_effectiveDomain p γ q)
        (scaled_absPower_hasGateauxDerivativeAt p hp γ q)).1
        (by
          simp [q, scaledProximityOperator])
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_sub_ne : (p - 2) + 1 ≠ 0 := by
    linarith
  have hpow :
      |q| ^ (p - 1) = |q| ^ (p - 2) * |q| := by
    calc
      |q| ^ (p - 1) = |q| ^ ((p - 2) + 1) := by ring_nf
      _ = |q| ^ (p - 2) * |q| ^ (1 : ℝ) := by
            rw [Real.rpow_add' (abs_nonneg q) hp_sub_ne]
      _ = |q| ^ (p - 2) * |q| := by rw [Real.rpow_one]
  have hcoeff_nonneg : 0 ≤ p * (γ : ℝ) * |q| ^ (p - 2) + 1 := by
    have hterm_nonneg : 0 ≤ p * (γ : ℝ) * |q| ^ (p - 2) := by
      exact
        mul_nonneg
          (show 0 ≤ p * (γ : ℝ) by exact mul_nonneg hp_pos.le γ.2.le)
          (Real.rpow_nonneg (abs_nonneg q) _)
    linarith
  have habs_eq :
      (p * (γ : ℝ) * |q| ^ (p - 2) + 1) * |q| = |ξ| := by
    -- Factor the first-order equation, then take absolute values.
    have hfactor :
        (p * (γ : ℝ) * |q| ^ (p - 2) + 1) * q = ξ := by
      calc
        (p * (γ : ℝ) * |q| ^ (p - 2) + 1) * q
            = p * (γ : ℝ) * |q| ^ (p - 2) * q + q := by ring
        _ = ξ := hstationary
    simpa [abs_mul, abs_of_nonneg hcoeff_nonneg] using congrArg abs hfactor
  refine ⟨abs_nonneg q, ?_⟩
  calc
    |q| + p * (γ : ℝ) * |q| ^ (p - 1)
        = (p * (γ : ℝ) * |q| ^ (p - 2) + 1) * |q| := by
            rw [hpow]
            ring
    _ = |ξ| := habs_eq

/-- First component of Example 24.38: if `p ∈ ]1,+∞[`, `γ ∈ ℝ_{++}`,
`φ(η) = |η|^p`, and `ξ ∈ ℝ`, then
there exists a unique nonnegative real number `ρ` solving
`ρ + p γ ρ^(p - 1) = |ξ|`. -/
theorem example_24_38_1_existsUnique_nonneg_solution
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (ξ : ℝ) :
    ∃! ρ : ℝ, isAbsPowerProxRoot p γ ξ ρ := by
  let ρ0 : ℝ := |Prox[γ, absPowerFunction p, absPowerFunction_mem_gammaZero p hp] ξ|
  have hρ0 : isAbsPowerProxRoot p γ ξ ρ0 := prox_absPower_abs_is_root p hp γ ξ
  refine ⟨ρ0, hρ0, ?_⟩
  intro ρ hρ
  -- Compare two candidate roots through strict monotonicity of the scalar control map.
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hlt' :=
      abs_power_root_map_strictMonoOn p hp γ
        (show ρ ∈ Set.Ici 0 from hρ.1)
        (show ρ0 ∈ Set.Ici 0 from hρ0.1)
        hlt
    simp [hρ.2, hρ0.2] at hlt'
  · have hgt' :=
      abs_power_root_map_strictMonoOn p hp γ
        (show ρ0 ∈ Set.Ici 0 from hρ0.1)
        (show ρ ∈ Set.Ici 0 from hρ.1)
        hgt
    simp [hρ0.2, hρ.2] at hgt'

/-- Helper for Example 24.38: any certified root of `(24.72)` is automatically the unique one. -/
private theorem absPower_root_unique_of_is_root
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (ξ ρ : ℝ)
    (hρ : isAbsPowerProxRoot p γ ξ ρ) :
    ∀ σ : ℝ, isAbsPowerProxRoot p γ ξ σ → σ = ρ := by
  -- Reuse the unique-root statement from part `(1)` instead of reproving monotonicity again.
  intro σ hσ
  rcases example_24_38_1_existsUnique_nonneg_solution p hp γ ξ with ⟨τ, hτ, hτ_unique⟩
  exact (hτ_unique σ hσ).trans (hτ_unique ρ hρ).symm

/-- Second component of Example 24.38: if `ρ` is the unique nonnegative real number solving
`ρ + p γ ρ^(p - 1) = |ξ|`, then `Prox_{γ φ} ξ = sign(ξ) ρ` for `φ(η) = |η|^p`. -/
theorem example_24_38_2_prox_eq_sign_mul_of_unique_nonneg_solution
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (ξ ρ : ℝ)
    (hρ : isAbsPowerProxRoot p γ ξ ρ)
    (hρ_unique : ∀ σ : ℝ, isAbsPowerProxRoot p γ ξ σ → σ = ρ) :
    Prox[γ, absPowerFunction p, absPowerFunction_mem_gammaZero p hp] ξ =
      Real.sign ξ * ρ := by
  let q : ℝ := Real.sign ξ * ρ
  have hq_abs : |q| = ρ := by
    -- The candidate uses the source sign, so its modulus is exactly the nonnegative root.
    by_cases hξ : ξ = 0
    · have hzero_root : isAbsPowerProxRoot p γ ξ 0 := by
        subst hξ
        refine ⟨le_rfl, ?_⟩
        have hp_sub_ne : p - 1 ≠ 0 := by linarith
        simp [hp_sub_ne]
      have hρ_zero : 0 = ρ := hρ_unique 0 hzero_root
      have hρ_eq_zero : ρ = 0 := hρ_zero.symm
      simp [q, hξ, hρ_eq_zero]
    · rcases lt_or_gt_of_ne hξ with hξ_neg | hξ_pos
      · simp [q, Real.sign_of_neg hξ_neg, abs_of_nonneg hρ.1]
      · simp [q, Real.sign_of_pos hξ_pos, abs_of_nonneg hρ.1]
  have hp_sub_ne : (p - 2) + 1 ≠ 0 := by
    linarith
  have habs_pow :
      ρ ^ (p - 1) = ρ ^ (p - 2) * ρ := by
    calc
      ρ ^ (p - 1) = ρ ^ ((p - 2) + 1) := by ring_nf
      _ = ρ ^ (p - 2) * ρ ^ (1 : ℝ) := by
            rw [Real.rpow_add' hρ.1 hp_sub_ne]
      _ = ρ ^ (p - 2) * ρ := by rw [Real.rpow_one]
  have hgrad_eq :
      p * (γ : ℝ) * |q| ^ (p - 2) * q + q = ξ := by
    -- Check the first-order equation branchwise according to the sign of `ξ`.
    by_cases hξ : ξ = 0
    · have hzero_root : isAbsPowerProxRoot p γ ξ 0 := by
        subst hξ
        refine ⟨le_rfl, ?_⟩
        have hp_root_ne : p - 1 ≠ 0 := by linarith
        simp [hp_root_ne]
      have hρ_zero : 0 = ρ := hρ_unique 0 hzero_root
      have hρ_eq_zero : ρ = 0 := hρ_zero.symm
      simp [q, hξ, hρ_eq_zero]
    · rcases lt_or_gt_of_ne hξ with hξ_neg | hξ_pos
      · calc
          p * (γ : ℝ) * |q| ^ (p - 2) * q + q
              = -(p * (γ : ℝ) * ρ ^ (p - 2) * ρ + ρ) := by
                  simp [q, Real.sign_of_neg hξ_neg, abs_of_nonneg hρ.1]
                  ring
          _ = -(ρ + p * (γ : ℝ) * ρ ^ (p - 1)) := by
                rw [habs_pow]
                ring
          _ = -|ξ| := by rw [hρ.2]
          _ = ξ := by rw [abs_of_neg hξ_neg]; ring
      · calc
          p * (γ : ℝ) * |q| ^ (p - 2) * q + q
              = p * (γ : ℝ) * ρ ^ (p - 2) * ρ + ρ := by
                  simp [q, Real.sign_of_pos hξ_pos, abs_of_nonneg hρ.1]
          _ = ρ + p * (γ : ℝ) * ρ ^ (p - 1) := by
                rw [habs_pow]
                ring
          _ = |ξ| := hρ.2
          _ = ξ := by rw [abs_of_pos hξ_pos]
  have hprox :
      q = Prox[γ • absPowerFunction p,
        smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ] ξ := by
    -- Proposition 24.1 closes the proximal identity once the gradient equation is verified.
    exact
      (eq_proximityOperator_iff_gateauxGradient_add_eq
        (γ • absPowerFunction p)
        (smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ)
        (scaled_absPower_mem_interior_effectiveDomain p γ q)
        (scaled_absPower_hasGateauxDerivativeAt p hp γ q)).2
        hgrad_eq
  simpa [q, scaledProximityOperator] using hprox.symm

/-- Helper for Example 24.38: a scalar stationary equation certifies the proximal point directly
through Proposition 24.1. -/
private theorem proxEqOfAbsPowerStationary
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (ξ q : ℝ)
    (hq : q + p * (γ : ℝ) * |q| ^ (p - 2) * q = ξ) :
    Prox[γ, absPowerFunction p, absPowerFunction_mem_gammaZero p hp] ξ = q := by
  have hprox :
      q = Prox[γ • absPowerFunction p,
        smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ] ξ := by
    -- Put the candidate into Proposition 24.1's first-order form and close the proximal identity.
    exact
      (eq_proximityOperator_iff_gateauxGradient_add_eq
        (γ • absPowerFunction p)
        (smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ)
        (scaled_absPower_mem_interior_effectiveDomain p γ q)
        (scaled_absPower_hasGateauxDerivativeAt p hp γ q)).2
        (by simpa [add_comm] using hq)
  simpa [scaledProximityOperator] using hprox.symm

/-- Helper for Example 24.38: the explicit real cube root is odd. -/
private theorem realCubeRoot_neg
    (x : ℝ) :
    realCubeRoot (-x) = -realCubeRoot x := by
  rcases lt_trichotomy x 0 with hx_neg | rfl | hx_pos
  · have hneg_pos : 0 < -x := by linarith
    simp [realCubeRoot, Real.sign_of_pos hneg_pos, Real.sign_of_neg hx_neg, abs_of_neg hx_neg]
  · simp [realCubeRoot]
  · have hneg_neg : -x < 0 := by linarith
    simp [realCubeRoot, Real.sign_of_neg hneg_neg, Real.sign_of_pos hx_pos, abs_of_pos hx_pos]

/-- Helper for Example 24.38: the explicit real cube root respects multiplication on `ℝ_+`. -/
private theorem realCubeRoot_mul_of_nonneg
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    realCubeRoot (x * y) = realCubeRoot x * realCubeRoot y := by
  -- Rewrite every cube root as an `rpow`, then use multiplicativity of `rpow` on `ℝ_+`.
  rw [realCubeRoot_eq_rpow_of_nonneg (mul_nonneg hx hy)]
  rw [realCubeRoot_eq_rpow_of_nonneg hx, realCubeRoot_eq_rpow_of_nonneg hy]
  rw [Real.mul_rpow hx hy]

/-- Helper for Example 24.38: on `ℝ_+`, the explicit real cube root inverts cubing. -/
private theorem realCubeRoot_pow_three_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    realCubeRoot (x ^ (3 : ℕ)) = x := by
  -- Convert the cube root back to an `rpow` and collapse the exponents.
  rw [realCubeRoot_eq_rpow_of_nonneg (pow_nonneg hx _)]
  rw [← Real.rpow_natCast x 3]
  rw [← Real.rpow_mul hx]
  norm_num

/-- Helper for Example 24.38: cubing first and then applying the explicit real cube root returns
the original real scalar. -/
private theorem realCubeRoot_pow_three
    (x : ℝ) :
    realCubeRoot (x ^ (3 : ℕ)) = x := by
  by_cases hx : 0 ≤ x
  · exact realCubeRoot_pow_three_of_nonneg hx
  · have hneg_nonneg : 0 ≤ -x := by linarith
    -- Reduce the negative case to the nonnegative one using oddness of `realCubeRoot`.
    calc
      realCubeRoot (x ^ (3 : ℕ))
          = realCubeRoot (-((-x) ^ (3 : ℕ))) := by
              congr 1
              ring_nf
      _ = -realCubeRoot ((-x) ^ (3 : ℕ)) := by rw [realCubeRoot_neg]
      _ = -(-x) := by rw [realCubeRoot_pow_three_of_nonneg hneg_nonneg]
      _ = x := by ring

/-- Helper for Example 24.38: the nonlinear factor in the `p = 4 / 3` stationary equation is the
explicit real cube root. -/
private theorem absPowerFourThirds_term_eq_realCubeRoot
    (q : ℝ) :
    |q| ^ ((4 / 3 : ℝ) - 2) * q = realCubeRoot q := by
  have hsign_abs : Real.sign q * |q| = q := by
    rcases lt_trichotomy q 0 with hq_neg | rfl | hq_pos
    · simp [Real.sign_of_neg hq_neg, abs_of_neg hq_neg]
    · simp
    · simp [Real.sign_of_pos hq_pos, abs_of_pos hq_pos]
  have hpow : |q| ^ ((4 / 3 : ℝ) - 2) * |q| = |q| ^ (1 / 3 : ℝ) := by
    have hne : ((4 / 3 : ℝ) - 2) + 1 ≠ 0 := by norm_num
    calc
      |q| ^ ((4 / 3 : ℝ) - 2) * |q|
          = |q| ^ ((4 / 3 : ℝ) - 2) * |q| ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = |q| ^ (((4 / 3 : ℝ) - 2) + 1) := by
            rw [← Real.rpow_add' (abs_nonneg q) hne]
      _ = |q| ^ (1 / 3 : ℝ) := by norm_num
  -- Factor out the sign and combine the remaining nonnegative powers of `|q|`.
  calc
    |q| ^ ((4 / 3 : ℝ) - 2) * q
        = |q| ^ ((4 / 3 : ℝ) - 2) * (Real.sign q * |q|) := by
            nth_rewrite 2 [show q = Real.sign q * |q| by simpa using hsign_abs.symm]
            rfl
    _ = Real.sign q * (|q| ^ ((4 / 3 : ℝ) - 2) * |q|) := by ring
    _ = Real.sign q * |q| ^ (1 / 3 : ℝ) := by rw [hpow]
    _ = realCubeRoot q := by simp [realCubeRoot]

/-- Helper for Example 24.38: the quadratic substitution for `p = 3 / 2` yields a certified root
of `(24.72)`. -/
private theorem threeHalvesRootCertificate
    (γ : PosReal) (ξ : ℝ) :
    let u := Real.sqrt (1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)))
    let s := (3 * (γ : ℝ) / 4) * (u - 1)
    let ρ := s ^ (2 : ℕ)
    isAbsPowerProxRoot (3 / 2 : ℝ) γ ξ ρ := by
  dsimp
  let u : ℝ := Real.sqrt (1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)))
  let s : ℝ := (3 * (γ : ℝ) / 4) * (u - 1)
  let ρ : ℝ := s ^ (2 : ℕ)
  have hγ_pos : 0 < (γ : ℝ) := γ.2
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos
  have hu_nonneg : 0 ≤ u := by
    -- The auxiliary square root is nonnegative by definition.
    simp [u]
  have hu_sq : u ^ (2 : ℕ) = 1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by
    have hrad_nonneg : 0 ≤ 1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by
      have : 0 ≤ 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by
        positivity
      linarith
    simpa [u] using Real.sq_sqrt hrad_nonneg
  have hu_ge_one : 1 ≤ u := by
    by_contra hu_lt
    have hu_lt' : u < 1 := lt_of_not_ge hu_lt
    have hterm_nonneg : 0 ≤ 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by
      positivity
    nlinarith [hu_sq, hu_nonneg, hterm_nonneg]
  have hs_nonneg : 0 ≤ s := by
    -- The chosen branch uses the nonnegative square-root solution.
    refine mul_nonneg ?_ (sub_nonneg.mpr hu_ge_one)
    positivity
  have hroot_eq : s ^ (2 : ℕ) + (3 / 2 : ℝ) * (γ : ℝ) * s = |ξ| := by
    -- Expanding the quadratic substitution collapses the equation to the square-root identity.
    calc
      s ^ (2 : ℕ) + (3 / 2 : ℝ) * (γ : ℝ) * s
          = (9 * (γ : ℝ) ^ (2 : ℕ) / 16) * (u ^ (2 : ℕ) - 1) := by
              dsimp [s]
              ring
      _ = |ξ| := by
            rw [hu_sq]
            field_simp [hγ_ne]
            ring
  have hρ_half : ρ ^ ((3 / 2 : ℝ) - 1) = s := by
    -- Since `ρ = s^2` and `s ≥ 0`, the half-power is exactly `s`.
    calc
      ρ ^ ((3 / 2 : ℝ) - 1) = ρ ^ (1 / 2 : ℝ) := by norm_num
      _ = Real.sqrt ρ := by rw [← Real.sqrt_eq_rpow]
      _ = s := by
            rw [show ρ = s ^ (2 : ℕ) by rfl, Real.sqrt_sq_eq_abs, abs_of_nonneg hs_nonneg]
  refine ⟨sq_nonneg s, ?_⟩
  -- Replace the abstract half-power by the concrete substitution variable `s`.
  calc
    ρ + (3 / 2 : ℝ) * (γ : ℝ) * ρ ^ ((3 / 2 : ℝ) - 1)
        = s ^ (2 : ℕ) + (3 / 2 : ℝ) * (γ : ℝ) * s := by
            rw [show ρ = s ^ (2 : ℕ) by rfl, hρ_half]
    _ = |ξ| := hroot_eq

/-- Helper for Example 24.38: the quadratic substitution for `p = 3` yields a certified root of
`(24.72)`. -/
private theorem threeRootCertificate
    (γ : PosReal) (ξ : ℝ) :
    let u := Real.sqrt (1 + 12 * (γ : ℝ) * |ξ|)
    let ρ := (u - 1) / (6 * (γ : ℝ))
    isAbsPowerProxRoot (3 : ℝ) γ ξ ρ := by
  dsimp
  let u : ℝ := Real.sqrt (1 + 12 * (γ : ℝ) * |ξ|)
  let ρ : ℝ := (u - 1) / (6 * (γ : ℝ))
  have hγ_pos : 0 < (γ : ℝ) := γ.2
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos
  have hu_nonneg : 0 ≤ u := by
    -- The auxiliary square root is nonnegative by definition.
    simp [u]
  have hu_sq : u ^ (2 : ℕ) = 1 + 12 * (γ : ℝ) * |ξ| := by
    have hrad_nonneg : 0 ≤ 1 + 12 * (γ : ℝ) * |ξ| := by
      have : 0 ≤ 12 * (γ : ℝ) * |ξ| := by positivity
      linarith
    simpa [u] using Real.sq_sqrt hrad_nonneg
  have hu_ge_one : 1 ≤ u := by
    by_contra hu_lt
    have hu_lt' : u < 1 := lt_of_not_ge hu_lt
    have hterm_nonneg : 0 ≤ 12 * (γ : ℝ) * |ξ| := by positivity
    nlinarith [hu_sq, hu_nonneg, hterm_nonneg]
  refine ⟨div_nonneg (sub_nonneg.mpr hu_ge_one) (by nlinarith [hγ_pos] : 0 ≤ 6 * (γ : ℝ)), ?_⟩
  -- Expanding the quadratic formula for `ρ` reduces the control equation to `u^2`.
  calc
    ρ + (3 : ℝ) * (γ : ℝ) * ρ ^ ((3 : ℝ) - 1)
        = ρ + (3 : ℝ) * (γ : ℝ) * ρ ^ (2 : ℕ) := by norm_num [Real.rpow_natCast]
    _ = (u ^ (2 : ℕ) - 1) / (12 * (γ : ℝ)) := by
          dsimp [ρ]
          field_simp [hγ_ne]
          ring
    _ = |ξ| := by
          rw [hu_sq]
          field_simp [hγ_ne]
          ring

/-- Helper for Example 24.38: the discriminant relation in the `p = 4 / 3` Cardano formula gives
the expected perfect-cube product. -/
private theorem fourThirdsCardanoProductCube
    (γ ξ Δ c : ℝ)
    (hΔ_sq : Δ ^ (2 : ℕ) = ξ ^ (2 : ℕ) + 256 * γ ^ (3 : ℕ) / 729)
    (hc_cube : c ^ (3 : ℕ) = 2) :
    (Δ + ξ) * (Δ - ξ) = (4 * γ * c ^ (2 : ℕ) / 9) ^ (3 : ℕ) := by
  have hc_six : c ^ (6 : ℕ) = 4 := by
    calc
      c ^ (6 : ℕ) = (c ^ (3 : ℕ)) ^ (2 : ℕ) := by
        rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul]
      _ = (2 : ℝ) ^ (2 : ℕ) := by rw [hc_cube]
      _ = 4 := by norm_num
  calc
    (Δ + ξ) * (Δ - ξ) = Δ ^ (2 : ℕ) - ξ ^ (2 : ℕ) := by ring
    _ = 256 * γ ^ (3 : ℕ) / 729 := by rw [hΔ_sq]; ring
    _ = 64 * γ ^ (3 : ℕ) * c ^ (6 : ℕ) / 729 := by rw [hc_six]; ring
    _ = (4 * γ * c ^ (2 : ℕ) / 9) ^ (3 : ℕ) := by ring

/-- Helper for Example 24.38: the Cardano parameter for `p = 4 / 3` satisfies the reduced cubic
equation. -/
private theorem fourThirdsCardanoParameterCubic
    (γ ξ Δ u v c t : ℝ)
    (hu_cube : u ^ (3 : ℕ) = Δ + ξ)
    (hv_cube : v ^ (3 : ℕ) = Δ - ξ)
    (hc_cube : c ^ (3 : ℕ) = 2)
    (huv : u * v = 4 * γ * c ^ (2 : ℕ) / 9)
    (ht_mul : c * t = u - v) :
    t ^ (3 : ℕ) = ξ - (4 / 3 : ℝ) * γ * t := by
  have htwice : 2 * t ^ (3 : ℕ) = 2 * ξ - (8 / 3 : ℝ) * γ * t := by
    calc
      2 * t ^ (3 : ℕ) = c ^ (3 : ℕ) * t ^ (3 : ℕ) := by rw [hc_cube]
      _ = (c * t) ^ (3 : ℕ) := by rw [mul_pow]
      _ = (u - v) ^ (3 : ℕ) := by rw [ht_mul]
      _ = u ^ (3 : ℕ) - v ^ (3 : ℕ) - 3 * u * v * (u - v) := by ring
      _ = (Δ + ξ) - (Δ - ξ) - 3 * u * v * (u - v) := by rw [hu_cube, hv_cube]
      _ = 2 * ξ - 3 * u * v * (u - v) := by ring
      _ = 2 * ξ - 3 * (u * v) * (u - v) := by ring
      _ = 2 * ξ - 3 * (4 * γ * c ^ (2 : ℕ) / 9) * (c * t) := by rw [huv, ht_mul]
      _ = 2 * ξ - (4 / 3 : ℝ) * γ * c ^ (3 : ℕ) * t := by ring
      _ = 2 * ξ - (8 / 3 : ℝ) * γ * t := by rw [hc_cube]; ring
  linarith [htwice]

/-- Helper for Example 24.38: the `p = 4` Cardano radicands differ by the linear term
`ξ / (4γ)`. -/
private theorem fourCardanoRadicandDiff
    (γ ξ Δ : ℝ)
    (hγ_ne : γ ≠ 0) :
    (Δ + ξ) / (8 * γ) - (Δ - ξ) / (8 * γ) = ξ / (4 * γ) := by
  field_simp [hγ_ne]
  ring

/-- Helper for Example 24.38: the `p = 4` Cardano radicands multiply to the perfect cube
`(1 / (12γ))^3`. -/
private theorem fourCardanoRadicandProduct
    (γ ξ Δ : ℝ)
    (hγ_ne : γ ≠ 0)
    (hΔ_sq : Δ ^ (2 : ℕ) = ξ ^ (2 : ℕ) + 1 / (27 * γ)) :
    ((Δ + ξ) / (8 * γ)) * ((Δ - ξ) / (8 * γ)) = (1 / (12 * γ)) ^ (3 : ℕ) := by
  calc
    ((Δ + ξ) / (8 * γ)) * ((Δ - ξ) / (8 * γ))
        = (Δ ^ (2 : ℕ) - ξ ^ (2 : ℕ)) / (64 * γ ^ (2 : ℕ)) := by
            field_simp [hγ_ne]
            ring
    _ = (1 / (27 * γ)) / (64 * γ ^ (2 : ℕ)) := by
          rw [hΔ_sq]
          ring
    _ = (1 / (12 * γ)) ^ (3 : ℕ) := by
          field_simp [hγ_ne]
          ring

/-- Helper for Example 24.38: the `p = 4` Cardano variable `q = u - v` satisfies the cubic
identity obtained from `u^3 - v^3` and `uv = 1 / (12γ)`. -/
private theorem fourCardanoQCube
    (γ ξ a b u v q : ℝ)
    (hγ_ne : γ ≠ 0)
    (hq : q = u - v)
    (hu_cube : u ^ (3 : ℕ) = a)
    (hv_cube : v ^ (3 : ℕ) = b)
    (huv : u * v = 1 / (12 * γ))
    (hab_diff : a - b = ξ / (4 * γ)) :
    q ^ (3 : ℕ) = ξ / (4 * γ) - q / (4 * γ) := by
  calc
    q ^ (3 : ℕ) = (u - v) ^ (3 : ℕ) := by rw [hq]
    _ = u ^ (3 : ℕ) - v ^ (3 : ℕ) - 3 * u * v * (u - v) := by ring
    _ = a - b - 3 * u * v * q := by rw [hu_cube, hv_cube, hq]
    _ = ξ / (4 * γ) - 3 * u * v * q := by rw [hab_diff]
    _ = ξ / (4 * γ) - q / (4 * γ) := by
          rw [show 3 * u * v * q = (3 * (u * v)) * q by ring]
          rw [huv]
          field_simp [hγ_ne]
          ring

/-- Helper for Example 24.38: the Cardano expression for `p = 4 / 3` satisfies the scalar
stationary equation. -/
private theorem fourThirdsCardanoStationary
    (γ : PosReal) (ξ : ℝ) :
    let Δ := Real.sqrt (ξ ^ (2 : ℕ) + 256 * (γ : ℝ) ^ (3 : ℕ) / 729)
    let q :=
      ξ +
        (4 * (γ : ℝ)) / (3 * realCubeRoot 2) *
          (realCubeRoot (Δ - ξ) - realCubeRoot (Δ + ξ))
    q + (4 / 3 : ℝ) * (γ : ℝ) * |q| ^ ((4 / 3 : ℝ) - 2) * q = ξ := by
  dsimp
  let Δ : ℝ := Real.sqrt (ξ ^ (2 : ℕ) + 256 * (γ : ℝ) ^ (3 : ℕ) / 729)
  let u : ℝ := realCubeRoot (Δ + ξ)
  let v : ℝ := realCubeRoot (Δ - ξ)
  let c : ℝ := realCubeRoot 2
  let t : ℝ := (u - v) / c
  let q : ℝ := ξ + (4 * (γ : ℝ)) / (3 * c) * (v - u)
  have hγ_pos : 0 < (γ : ℝ) := γ.2
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos
  have hΔ_nonneg : 0 ≤ Δ := by
    -- The discriminant square root is nonnegative by definition.
    simp [Δ]
  have hΔ_sq : Δ ^ (2 : ℕ) = ξ ^ (2 : ℕ) + 256 * (γ : ℝ) ^ (3 : ℕ) / 729 := by
    have hrad_nonneg : 0 ≤ ξ ^ (2 : ℕ) + 256 * (γ : ℝ) ^ (3 : ℕ) / 729 := by
      have : 0 ≤ 256 * (γ : ℝ) ^ (3 : ℕ) / 729 := by positivity
      nlinarith
    simpa [Δ] using Real.sq_sqrt hrad_nonneg
  have hΔ_ge_abs : |ξ| ≤ Δ := by
    have hsq : ξ ^ (2 : ℕ) ≤ Δ ^ (2 : ℕ) := by
      have hextra_nonneg : 0 ≤ 256 * (γ : ℝ) ^ (3 : ℕ) / 729 := by positivity
      nlinarith [hΔ_sq, hextra_nonneg]
    have habs_sq : |ξ| ^ (2 : ℕ) ≤ Δ ^ (2 : ℕ) := by
      simpa [pow_two] using hsq
    nlinarith [habs_sq, abs_nonneg ξ, hΔ_nonneg]
  have hu_arg_nonneg : 0 ≤ Δ + ξ := by
    linarith [neg_le_abs ξ, hΔ_ge_abs]
  have hv_arg_nonneg : 0 ≤ Δ - ξ := by
    linarith [le_abs_self ξ, hΔ_ge_abs]
  have hu_cube : u ^ (3 : ℕ) = Δ + ξ := by
    simpa [u] using realCubeRoot_cube (Δ + ξ)
  have hv_cube : v ^ (3 : ℕ) = Δ - ξ := by
    simpa [v] using realCubeRoot_cube (Δ - ξ)
  have hc_cube : c ^ (3 : ℕ) = 2 := by
    simpa [c] using realCubeRoot_cube (2 : ℝ)
  have hc_ne : c ≠ 0 := by
    intro hc0
    rw [hc0] at hc_cube
    norm_num at hc_cube
  let d : ℝ := 4 * (γ : ℝ) * c ^ (2 : ℕ) / 9
  have hd_nonneg : 0 ≤ d := by
    -- The Cardano product branch is nonnegative.
    dsimp [d]
    positivity
  have huv : u * v = d := by
    have hprod : (Δ + ξ) * (Δ - ξ) = d ^ (3 : ℕ) := by
      simpa [d] using
        fourThirdsCardanoProductCube (γ := (γ : ℝ)) (ξ := ξ) (Δ := Δ) (c := c) hΔ_sq hc_cube
    -- The product of the Cardano cube roots is the cube root of the product.
    calc
      u * v = realCubeRoot ((Δ + ξ) * (Δ - ξ)) := by
                dsimp [u, v]
                rw [realCubeRoot_mul_of_nonneg hu_arg_nonneg hv_arg_nonneg]
      _ = realCubeRoot (d ^ (3 : ℕ)) := by rw [hprod]
      _ = d := by simpa [d] using realCubeRoot_pow_three_of_nonneg hd_nonneg
  have ht_mul : c * t = u - v := by
    -- Clear the denominator in the Cardano parameter.
    dsimp [t]
    field_simp [hc_ne]
  have ht_cube_eq : t ^ (3 : ℕ) = ξ - (4 / 3 : ℝ) * (γ : ℝ) * t := by
    exact
      fourThirdsCardanoParameterCubic
        (γ := (γ : ℝ)) (ξ := ξ) (Δ := Δ) (u := u) (v := v) (c := c) (t := t)
        hu_cube hv_cube hc_cube (by simpa [d] using huv) ht_mul
  have hq_eq : q = t ^ (3 : ℕ) := by
    -- Rewrite the printed formula in terms of the Cardano parameter `t`.
    calc
      q = ξ - (4 / 3 : ℝ) * (γ : ℝ) * t := by
            dsimp [q, t]
            field_simp [hc_ne]
            ring
      _ = t ^ (3 : ℕ) := by
            linarith [ht_cube_eq]
  -- Transport the nonlinear term to `∛q`; the stationary equation is then
  -- exactly `t^3 + 4γt/3 = ξ`.
  calc
    q + (4 / 3 : ℝ) * (γ : ℝ) * |q| ^ ((4 / 3 : ℝ) - 2) * q
        = t ^ (3 : ℕ) + (4 / 3 : ℝ) * (γ : ℝ) * t := by
            rw [hq_eq]
            have htransport :
                |t ^ (3 : ℕ)| ^ ((4 / 3 : ℝ) - 2) * t ^ (3 : ℕ) = t := by
              rw [absPowerFourThirds_term_eq_realCubeRoot, realCubeRoot_pow_three]
            have htransport' :
                (4 / 3 : ℝ) * (γ : ℝ) *
                    (|t ^ (3 : ℕ)| ^ ((4 / 3 : ℝ) - 2) * t ^ (3 : ℕ)) =
                  (4 / 3 : ℝ) * (γ : ℝ) * t := by
              rw [htransport]
            simpa [mul_assoc] using congrArg (fun z : ℝ ↦ t ^ (3 : ℕ) + z) htransport'
    _ = ξ := by linarith [ht_cube_eq]

/-- Helper for Example 24.38: the Cardano expression for `p = 4` satisfies the cubic stationary
equation. -/
private theorem fourCardanoStationary
    (γ : PosReal) (ξ : ℝ) :
    let Δ := Real.sqrt (ξ ^ (2 : ℕ) + 1 / (27 * (γ : ℝ)))
    let q :=
      realCubeRoot ((Δ + ξ) / (8 * (γ : ℝ))) -
        realCubeRoot ((Δ - ξ) / (8 * (γ : ℝ)))
    q + 4 * (γ : ℝ) * q ^ (3 : ℕ) = ξ := by
  dsimp
  let Δ : ℝ := Real.sqrt (ξ ^ (2 : ℕ) + 1 / (27 * (γ : ℝ)))
  let a : ℝ := (Δ + ξ) / (8 * (γ : ℝ))
  let b : ℝ := (Δ - ξ) / (8 * (γ : ℝ))
  let u : ℝ := realCubeRoot a
  let v : ℝ := realCubeRoot b
  let q : ℝ := u - v
  have hγ_pos : 0 < (γ : ℝ) := γ.2
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos
  have hΔ_nonneg : 0 ≤ Δ := by
    -- The discriminant square root is nonnegative by definition.
    simp [Δ]
  have hΔ_sq : Δ ^ (2 : ℕ) = ξ ^ (2 : ℕ) + 1 / (27 * (γ : ℝ)) := by
    have hrad_nonneg : 0 ≤ ξ ^ (2 : ℕ) + 1 / (27 * (γ : ℝ)) := by
      have : 0 ≤ 1 / (27 * (γ : ℝ)) := by positivity
      nlinarith
    simpa [Δ] using Real.sq_sqrt hrad_nonneg
  have hΔ_ge_abs : |ξ| ≤ Δ := by
    have hsq : ξ ^ (2 : ℕ) ≤ Δ ^ (2 : ℕ) := by
      have hextra_nonneg : 0 ≤ 1 / (27 * (γ : ℝ)) := by positivity
      nlinarith [hΔ_sq, hextra_nonneg]
    have habs_sq : |ξ| ^ (2 : ℕ) ≤ Δ ^ (2 : ℕ) := by
      simpa [pow_two] using hsq
    nlinarith [habs_sq, abs_nonneg ξ, hΔ_nonneg]
  have ha_num_nonneg : 0 ≤ Δ + ξ := by
    linarith [neg_le_abs ξ, hΔ_ge_abs]
  have hb_num_nonneg : 0 ≤ Δ - ξ := by
    linarith [le_abs_self ξ, hΔ_ge_abs]
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hu_cube : u ^ (3 : ℕ) = a := by
    simpa [u] using realCubeRoot_cube a
  have hv_cube : v ^ (3 : ℕ) = b := by
    simpa [v] using realCubeRoot_cube b
  have huv : u * v = 1 / (12 * (γ : ℝ)) := by
    have hab : a * b = (1 / (12 * (γ : ℝ))) ^ (3 : ℕ) := by
      -- The product of the two Cardano radicands is the perfect cube dictated by the discriminant.
      simpa [a, b] using
        fourCardanoRadicandProduct (γ := (γ : ℝ)) (ξ := ξ) (Δ := Δ) hγ_ne hΔ_sq
    calc
      u * v = realCubeRoot (a * b) := by
                dsimp [u, v]
                rw [realCubeRoot_mul_of_nonneg ha_nonneg hb_nonneg]
      _ = realCubeRoot ((1 / (12 * (γ : ℝ))) ^ (3 : ℕ)) := by rw [hab]
      _ = 1 / (12 * (γ : ℝ)) := by
            apply realCubeRoot_pow_three_of_nonneg
            positivity
  have hq_cube : q ^ (3 : ℕ) = ξ / (4 * (γ : ℝ)) - q / (4 * (γ : ℝ)) := by
    have hab_diff : a - b = ξ / (4 * (γ : ℝ)) := by
      simpa [a, b] using fourCardanoRadicandDiff (γ := (γ : ℝ)) (ξ := ξ) (Δ := Δ) hγ_ne
    -- Expanding `(u - v)^3` and substituting the product formula collapses the cubic.
    exact
      fourCardanoQCube
        (γ := (γ : ℝ)) (ξ := ξ) (a := a) (b := b) (u := u) (v := v) (q := q)
        hγ_ne rfl hu_cube hv_cube huv hab_diff
  -- Multiply the cubic identity by `4γ` and solve for `ξ`.
  calc
    q + 4 * (γ : ℝ) * q ^ (3 : ℕ)
        = q + 4 * (γ : ℝ) * (ξ / (4 * (γ : ℝ)) - q / (4 * (γ : ℝ))) := by rw [hq_cube]
    _ = ξ := by
          field_simp [hγ_ne]
          ring

/-- Example 24.38 (3): for `p = 4 / 3`, the proximity operator of `γ (η ↦ |η|^(4 / 3))` is the
closed-form expression obtained from the cubic equation `(24.72)`. -/
theorem example_24_38_3_prox_absPower_four_thirds_eq
    (γ : PosReal) (ξ : ℝ) :
    let φ := absPowerFunction (4 / 3 : ℝ)
    let hφ : φ ∈ Γ₀(ℝ) := absPowerFunction_mem_gammaZero (4 / 3 : ℝ) (by norm_num)
    let ρ := Real.sqrt (ξ ^ (2 : ℕ) + 256 * (γ : ℝ) ^ (3 : ℕ) / 729)
    Prox[γ, φ, hφ] ξ =
      ξ +
        (4 * (γ : ℝ)) / (3 * realCubeRoot 2) *
          (realCubeRoot (ρ - ξ) - realCubeRoot (ρ + ξ)) := by
  dsimp
  let ρ : ℝ := Real.sqrt (ξ ^ (2 : ℕ) + 256 * (γ : ℝ) ^ (3 : ℕ) / 729)
  let q : ℝ :=
    ξ +
      (4 * (γ : ℝ)) / (3 * realCubeRoot 2) *
        (realCubeRoot (ρ - ξ) - realCubeRoot (ρ + ξ))
  have hstationary :
      q + (4 / 3 : ℝ) * (γ : ℝ) * |q| ^ ((4 / 3 : ℝ) - 2) * q = ξ := by
    -- The stable endpoint for the Cardano branch is the signed stationary equation.
    simpa [ρ, q] using fourThirdsCardanoStationary γ ξ
  simpa [q, ρ] using
    proxEqOfAbsPowerStationary (4 / 3 : ℝ) (by norm_num) γ ξ q hstationary

/-- Special case (4) of Example 24.38: for `p = 3 / 2`, the proximity operator of
`γ (η ↦ |η|^(3 / 2))` is the
explicit formula displayed after `(24.72)`. -/
theorem example_24_38_4_prox_absPower_three_halves_eq
    (γ : PosReal) (ξ : ℝ) :
    let φ := absPowerFunction (3 / 2 : ℝ)
    let hφ : φ ∈ Γ₀(ℝ) := absPowerFunction_mem_gammaZero (3 / 2 : ℝ) (by norm_num)
    Prox[γ, φ, hφ] ξ =
      ξ +
        (9 * (γ : ℝ) ^ (2 : ℕ)) / 8 *
          Real.sign ξ *
            (1 - Real.sqrt (1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)))) := by
  dsimp
  let u : ℝ := Real.sqrt (1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)))
  let s : ℝ := (3 * (γ : ℝ) / 4) * (u - 1)
  let ρ : ℝ := s ^ (2 : ℕ)
  have hρ : isAbsPowerProxRoot (3 / 2 : ℝ) γ ξ ρ := by
    -- The quadratic substitution gives the unique nonnegative root from part `(1)`.
    simpa [u, s, ρ] using threeHalvesRootCertificate γ ξ
  have hu_nonneg : 0 ≤ u := by
    simp [u]
  have hu_sq : u ^ (2 : ℕ) = 1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by
    have hrad_nonneg : 0 ≤ 1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by
      have : 0 ≤ 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by positivity
      linarith
    simpa [u] using Real.sq_sqrt hrad_nonneg
  have hu_ge_one : 1 ≤ u := by
    by_contra hu_lt
    have hu_lt' : u < 1 := lt_of_not_ge hu_lt
    have hterm_nonneg : 0 ≤ 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)) := by positivity
    nlinarith [hu_sq, hu_nonneg, hterm_nonneg]
  have hs_nonneg : 0 ≤ s := by
    -- We keep the nonnegative square-root branch to match `(24.72)`.
    refine mul_nonneg ?_ (sub_nonneg.mpr hu_ge_one)
    nlinarith [γ.2]
  have hρ_half : ρ ^ ((3 / 2 : ℝ) - 1) = s := by
    -- The half-power of `ρ = s^2` is the auxiliary square-root variable `s`.
    calc
      ρ ^ ((3 / 2 : ℝ) - 1) = ρ ^ (1 / 2 : ℝ) := by norm_num
      _ = Real.sqrt ρ := by rw [← Real.sqrt_eq_rpow]
      _ = s := by
            rw [show ρ = s ^ (2 : ℕ) by rfl, Real.sqrt_sq_eq_abs, abs_of_nonneg hs_nonneg]
  have hρ_eq : ρ + (3 / 2 : ℝ) * (γ : ℝ) * s = |ξ| := by
    simpa [hρ_half] using hρ.2
  have hprox :=
    example_24_38_2_prox_eq_sign_mul_of_unique_nonneg_solution
      (3 / 2 : ℝ) (by norm_num) γ ξ ρ hρ
      (absPower_root_unique_of_is_root (3 / 2 : ℝ) (by norm_num) γ ξ ρ hρ)
  have hsign : Real.sign ξ * |ξ| = ξ := by
    rcases lt_trichotomy ξ 0 with hξ_neg | rfl | hξ_pos
    · simp [Real.sign_of_neg hξ_neg, abs_of_neg hξ_neg]
    · simp
    · simp [Real.sign_of_pos hξ_pos, abs_of_pos hξ_pos]
  have hs_term :
      (3 / 2 : ℝ) * (γ : ℝ) * s =
        (9 * (γ : ℝ) ^ (2 : ℕ)) / 8 * (u - 1) := by
    -- This is the linear correction term coming from the quadratic substitution.
    dsimp [s]
    ring
  calc
    Prox[γ, absPowerFunction (3 / 2 : ℝ),
        absPowerFunction_mem_gammaZero (3 / 2 : ℝ) (by norm_num)] ξ
        = Real.sign ξ * ρ := hprox
    _ = ξ +
        (9 * (γ : ℝ) ^ (2 : ℕ)) / 8 *
          Real.sign ξ * (1 - u) := by
            calc
              Real.sign ξ * ρ = Real.sign ξ * (|ξ| - (3 / 2 : ℝ) * (γ : ℝ) * s) := by
                                  congr 1
                                  linarith [hρ_eq]
              _ = ξ + (9 * (γ : ℝ) ^ (2 : ℕ)) / 8 * Real.sign ξ * (1 - u) := by
                    rw [sub_eq_add_neg, mul_add, hsign, hs_term]
                    ring
    _ = ξ +
        (9 * (γ : ℝ) ^ (2 : ℕ)) / 8 *
          Real.sign ξ *
            (1 - Real.sqrt (1 + 16 * |ξ| / (9 * (γ : ℝ) ^ (2 : ℕ)))) := by
              simp [u]

/-- Special case (5) of Example 24.38: for `p = 2`, the proximity operator of
`γ (η ↦ |η|^2)` is the linear
rescaling `ξ ↦ ξ / (1 + 2γ)`. -/
theorem example_24_38_5_prox_absPower_two_eq
    (γ : PosReal) (ξ : ℝ) :
    let φ := absPowerFunction (2 : ℝ)
    let hφ : φ ∈ Γ₀(ℝ) := absPowerFunction_mem_gammaZero (2 : ℝ) (by norm_num)
    Prox[γ, φ, hφ] ξ =
      ξ / (1 + 2 * (γ : ℝ)) := by
  dsimp
  let ρ : ℝ := |ξ| / (1 + 2 * (γ : ℝ))
  have hden_pos : 0 < 1 + 2 * (γ : ℝ) := by
    nlinarith [γ.2]
  have hρ : isAbsPowerProxRoot (2 : ℝ) γ ξ ρ := by
    refine ⟨div_nonneg (abs_nonneg ξ) hden_pos.le, ?_⟩
    have hden_ne : 1 + 2 * (γ : ℝ) ≠ 0 := ne_of_gt hden_pos
    have hlin : ρ * (1 + 2 * (γ : ℝ)) = |ξ| := by
      calc
        ρ * (1 + 2 * (γ : ℝ))
            = (|ξ| / (1 + 2 * (γ : ℝ))) * (1 + 2 * (γ : ℝ)) := by rfl
        _ = |ξ| := by field_simp [hden_ne]
    calc
      ρ + (2 : ℝ) * (γ : ℝ) * ρ ^ ((2 : ℝ) - 1)
          = ρ + (2 : ℝ) * (γ : ℝ) * ρ := by
              rw [show (2 : ℝ) - 1 = (1 : ℝ) by norm_num, Real.rpow_one]
      _ = ρ * (1 + 2 * (γ : ℝ)) := by ring
      _ = |ξ| := hlin
  have hprox :=
    example_24_38_2_prox_eq_sign_mul_of_unique_nonneg_solution
      (2 : ℝ) (by norm_num) γ ξ ρ hρ
      (absPower_root_unique_of_is_root (2 : ℝ) (by norm_num) γ ξ ρ hρ)
  -- Rewrite the signed nonnegative root back to the displayed linear rescaling.
  calc
    Prox[γ, absPowerFunction (2 : ℝ), absPowerFunction_mem_gammaZero (2 : ℝ) (by norm_num)] ξ
        = Real.sign ξ * ρ := hprox
    _ = ξ / (1 + 2 * (γ : ℝ)) := by
      calc
        Real.sign ξ * ρ = Real.sign ξ * (|ξ| / (1 + 2 * (γ : ℝ))) := by rfl
        _ = (Real.sign ξ * |ξ|) / (1 + 2 * (γ : ℝ)) := by
                  rw [div_eq_mul_inv]
                  ring
        _ = ξ * (1 + 2 * (γ : ℝ))⁻¹ := by
              rw [div_eq_mul_inv]
              have hsign : Real.sign ξ * |ξ| = ξ := by
                rcases lt_trichotomy ξ 0 with hξ_neg | rfl | hξ_pos
                · simp [Real.sign_of_neg hξ_neg, abs_of_neg hξ_neg]
                · simp
                · simp [Real.sign_of_pos hξ_pos, abs_of_pos hξ_pos]
              rw [hsign]
        _ = ξ / (1 + 2 * (γ : ℝ)) := by rw [div_eq_mul_inv]

/-- Special case (6) of Example 24.38: for `p = 3`, the proximity operator of `γ (η ↦ |η|^3)` is the
square-root formula displayed in clause `(iv)`. -/
theorem example_24_38_6_prox_absPower_three_eq
    (γ : PosReal) (ξ : ℝ) :
    let φ := absPowerFunction (3 : ℝ)
    let hφ : φ ∈ Γ₀(ℝ) := absPowerFunction_mem_gammaZero (3 : ℝ) (by norm_num)
    Prox[γ, φ, hφ] ξ =
      Real.sign ξ * (Real.sqrt (1 + 12 * (γ : ℝ) * |ξ|) - 1) / (6 * (γ : ℝ)) := by
  dsimp
  let u : ℝ := Real.sqrt (1 + 12 * (γ : ℝ) * |ξ|)
  let ρ : ℝ := (u - 1) / (6 * (γ : ℝ))
  have hρ : isAbsPowerProxRoot (3 : ℝ) γ ξ ρ := by
    -- The quadratic formula gives the unique nonnegative root from part `(1)`.
    simpa [u, ρ] using threeRootCertificate γ ξ
  have hprox :=
    example_24_38_2_prox_eq_sign_mul_of_unique_nonneg_solution
      (3 : ℝ) (by norm_num) γ ξ ρ hρ
      (absPower_root_unique_of_is_root (3 : ℝ) (by norm_num) γ ξ ρ hρ)
  calc
    Prox[γ, absPowerFunction (3 : ℝ),
        absPowerFunction_mem_gammaZero (3 : ℝ) (by norm_num)] ξ
        = Real.sign ξ * ρ := hprox
    _ = Real.sign ξ * (u - 1) / (6 * (γ : ℝ)) := by
          dsimp [ρ]
          ring
    _ = Real.sign ξ * (Real.sqrt (1 + 12 * (γ : ℝ) * |ξ|) - 1) / (6 * (γ : ℝ)) := by
          simp [u]

/-- Special case (7) of Example 24.38: for `p = 4`, the proximity operator of
`γ (η ↦ |η|^4)` is the Cardano
formula obtained by solving `(24.72)` in `ℝ_+`. -/
theorem example_24_38_7_prox_absPower_four_eq
    (γ : PosReal) (ξ : ℝ) :
    let φ := absPowerFunction (4 : ℝ)
    let hφ : φ ∈ Γ₀(ℝ) := absPowerFunction_mem_gammaZero (4 : ℝ) (by norm_num)
    let ρ := Real.sqrt (ξ ^ (2 : ℕ) + 1 / (27 * (γ : ℝ)))
    Prox[γ, φ, hφ] ξ =
      realCubeRoot ((ρ + ξ) / (8 * (γ : ℝ))) -
        realCubeRoot ((ρ - ξ) / (8 * (γ : ℝ))) := by
  dsimp
  let ρ : ℝ := Real.sqrt (ξ ^ (2 : ℕ) + 1 / (27 * (γ : ℝ)))
  let q : ℝ :=
    realCubeRoot ((ρ + ξ) / (8 * (γ : ℝ))) -
      realCubeRoot ((ρ - ξ) / (8 * (γ : ℝ)))
  have hq_cube : q + 4 * (γ : ℝ) * q ^ (3 : ℕ) = ξ := by
    -- The Cardano expression solves the cubic stationary equation directly.
    simpa [ρ, q] using fourCardanoStationary γ ξ
  have hstationaryNat : q + 4 * (γ : ℝ) * |q| ^ (2 : ℕ) * q = ξ := by
    -- For `p = 4`, the nonlinear factor is just `q^3`.
    have hsq_abs : |q| ^ (2 : ℕ) = q ^ (2 : ℕ) := sq_abs q
    calc
      q + 4 * (γ : ℝ) * |q| ^ (2 : ℕ) * q
          = q + 4 * (γ : ℝ) * q ^ (3 : ℕ) := by
              rw [hsq_abs]
              ring
      _ = ξ := hq_cube
  have hstationary : q + (4 : ℝ) * (γ : ℝ) * |q| ^ ((4 : ℝ) - 2) * q = ξ := by
    simpa [show ((4 : ℝ) - 2) = (2 : ℝ) by norm_num, Real.rpow_natCast] using hstationaryNat
  simpa [ρ, q] using
    proxEqOfAbsPowerStationary (4 : ℝ) (by norm_num) γ ξ q hstationary

end

end ERealFunction
