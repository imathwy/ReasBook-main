import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap11.Proposition_11_7
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Example_13_8
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap17.Proposition_17_6

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped ERealFunction Gradient InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section StrongerDifferentiabilityBounds

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The scalar modulus `ψ` attached to a one-dimensional control function `φ`. -/
noncomputable def ψ (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun s ↦ if s = 0 then 0 else φ s / |s|

/-- The auxiliary modulus `ψ` vanishes at the origin by definition. -/
@[simp] theorem psi_zero (φ : ℝ → ℝ) :
    ψ φ 0 = 0 := by
  simp [ψ]

/-- Away from the origin, `ψ φ` is the quotient `φ(s) / |s|`. -/
theorem psi_eq_div_abs_of_ne (φ : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) :
    ψ φ s = φ s / |s| := by
  simp [ψ, hs]

/-- The scalar integral modulus `θ` attached to `φ`.

Lean's interval integral is total, so the source-facing owner is defined directly from `φ`; the
theorem-level convexity hypotheses are what make this the intended integral in the textbook
situation. -/
noncomputable def θ (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun s ↦ ∫ t in (0 : ℝ)..1, φ (s * t) / t

/-- Evaluating `θ φ` at `s` gives the interval integral from its definition. -/
@[simp] theorem theta_apply (φ : ℝ → ℝ) (s : ℝ) :
    θ φ s = ∫ t in (0 : ℝ)..1, φ (s * t) / t :=
  rfl

variable (φ : ℝ → ℝ)

/-- The Fenchel conjugate of the finite-valued remainder function `θ φ`, viewed on the canonical
`EReal` owner surface. -/
noncomputable def thetaConj : ℝ → EReal :=
  (θ φ).toEReal.asEReal∗

/-- The source-facing conjugate remainder `θ*` attached to `θ φ`.

In Theorem 18.13, `θ*` controls the admissible-set condition defining `ϱ`, so this owner must
retain the extended-real finiteness information of the Fenchel conjugate rather than collapsing it
through `toReal`. -/
noncomputable def thetaStar : ℝ → EReal :=
  thetaConj φ

/-- Helper for Theorem 18 13: coercing a convex real-valued scalar function through `toEReal`
preserves convexity on its effective domain. -/
lemma convexOn_toEReal_from_univ
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ) :
    ConvexOn φ.toEReal (effectiveDomain φ.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Function.effectiveDomain_toEReal]
  · simp [Function.effectiveDomain_toEReal]
  · intro s hs t ht a ha0 ha1
    -- Rewrite the Jensen inequality back to the original real-valued control function.
    have hreal :
        φ (a • s + (1 - a) • t) ≤ a * φ s + (1 - a) * φ t := by
      simpa [smul_eq_mul] using
        hφ_conv.2 (by simp : s ∈ Set.univ) (by simp : t ∈ Set.univ) ha0.le
          (sub_nonneg.mpr ha1.le) (by linarith)
    change ((φ (a • s + (1 - a) • t) : ℝ) : EReal) ≤
      ((a * φ s + (1 - a) * φ t : ℝ) : EReal)
    exact_mod_cast hreal

/-- Helper for Theorem 18 13: an even convex scalar control function that vanishes only at `0` is
nonnegative everywhere. -/
lemma phi_nonneg_of_even_convex_zero
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (s : ℝ) :
    0 ≤ φ s := by
  have hconv_toEReal :
      ConvexOn φ.toEReal (effectiveDomain φ.toEReal) :=
    convexOn_toEReal_from_univ φ hφ_conv
  have heven_toEReal : Function.Even φ.toEReal.asEReal := by
    intro t
    simp [hφ_even t]
  -- Proposition 11.7 identifies `0` as the global minimizer of the even convex owner.
  have hzero_min : IsMinOn φ.toEReal.asEReal Set.univ 0 :=
    isMinOn_zero_of_even_convexOn φ.toEReal hconv_toEReal heven_toEReal
  have hφ0 : φ 0 = 0 := (hφ_zero 0).2 rfl
  have hφ0_eq : ((φ 0 : ℝ) : EReal) = 0 := by
    exact_mod_cast hφ0
  have hφ0_le : ((φ 0 : ℝ) : EReal) ≤ ((φ s : ℝ) : EReal) :=
    (isMinOn_univ_iff.mp hzero_min) s
  have hs_nonneg : (0 : EReal) ≤ ((φ s : ℝ) : EReal) := by
    simpa [hφ0_eq] using hφ0_le
  exact_mod_cast hs_nonneg

/-- Helper for Theorem 18 13: nonnegativity of `φ` propagates to nonnegativity of the integral
remainder owner `θ φ`. -/
lemma theta_nonneg_of_phi_nonneg
    (hφ_nonneg : ∀ s : ℝ, 0 ≤ φ s)
    (s : ℝ) :
    0 ≤ θ φ s := by
  rw [theta_apply]
  -- The interval integrand is pointwise nonnegative on `[0,1]`.
  exact intervalIntegral.integral_nonneg zero_le_one fun t ht ↦ by
    have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa using ht
    exact div_nonneg (hφ_nonneg (s * t)) ht_mem.1

/-- Helper for Theorem 18 13: under the source hypotheses, the scalar conjugate owner satisfies
`θ*(0) = 0`. -/
lemma thetaConj_zero_eq_zero
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) :
    thetaConj φ 0 = 0 := by
  have hφ_nonneg : ∀ s : ℝ, 0 ≤ φ s :=
    phi_nonneg_of_even_convex_zero φ hφ_even hφ_conv hφ_zero
  have hθ_nonneg : ∀ s : ℝ, 0 ≤ θ φ s :=
    theta_nonneg_of_phi_nonneg φ hφ_nonneg
  have hθ_zero : θ φ 0 = 0 := by
    rw [theta_apply]
    have hφ0 : φ 0 = 0 := (hφ_zero 0).2 rfl
    simp [hφ0]
  rw [thetaConj, conjugate_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro s
    -- At `u = 0`, every affine defect collapses to `-θ(s)`.
    simpa using hθ_nonneg s
  · -- The defect at `x = 0` is exactly `0`, so the supremum is at least `0`.
    have hzero_term :
        (0 : EReal) ≤
          (((⟪(0 : ℝ), (0 : ℝ)⟫_ℝ : ℝ) : EReal) - (((θ φ 0 : ℝ) : EReal))) := by
      rw [hθ_zero]
      simp
    exact hzero_term.trans <|
      le_iSup
        (fun s : ℝ ↦ (((⟪s, (0 : ℝ)⟫_ℝ : ℝ) : EReal) - (((θ φ s : ℝ) : EReal))))
        0

/-- Helper for Theorem 18 13: the source-facing owner `θ*` is definitionally the canonical
`EReal` conjugate owner. -/
theorem thetaStar_asEReal_of_nonneg
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    thetaStar φ s = thetaConj φ s := by
  let _ := hφ_even
  let _ := hφ_conv
  let _ := hφ_zero
  let _ := hs
  rfl

/- Keep the hypotheses in `thetaStar_asEReal_of_nonneg` so existing clause-specialization code can
still invoke the same theorem name while the corrected owner remains definitionally transparent. -/

/-- Helper for Theorem 18 13: under the source hypotheses, the source-facing conjugate
vanishes at `0`. -/
@[simp] theorem thetaStar_zero_eq_zero
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) :
    thetaStar φ 0 = 0 := by
  simpa [thetaStar] using thetaConj_zero_eq_zero φ hφ_even hφ_conv hφ_zero

/-- Helper for Theorem 18 13: evaluating the scalar conjugate at a test point gives a lower bound
for `θ*(ν)`. -/
lemma thetaStar_ge_testPointAffineDefect
    (r ν : ℝ) :
    (((ν * r : ℝ) : EReal) - ((θ φ r : ℝ) : EReal)) ≤ thetaStar φ ν := by
  rw [thetaStar, thetaConj, conjugate_apply]
  have hinner : ⟪r, ν⟫_ℝ = r * ν := by
    simpa using (RCLike.inner_apply' r ν)
  have htest :
      (((⟪r, ν⟫_ℝ : ℝ) : EReal) - ((θ φ r : ℝ) : EReal)) ≤
        ⨆ s : ℝ, (((⟪s, ν⟫_ℝ : ℝ) : EReal) - ((θ φ s : ℝ) : EReal)) := by
    exact le_iSup (fun s : ℝ ↦ (((⟪s, ν⟫_ℝ : ℝ) : EReal) - ((θ φ s : ℝ) : EReal))) r
  simpa [Function.asEReal_apply, hinner, mul_comm] using htest

/-- Helper for Theorem 18 13: the scalar conjugate `θ*` is nonnegative because the affine defect
vanishes at the test point `0`. -/
lemma thetaStar_nonneg
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (ν : ℝ) :
    0 ≤ thetaStar φ ν := by
  have hθ0 : θ φ 0 = 0 := by
    rw [theta_apply]
    have hφ0 : φ 0 = 0 := (hφ_zero 0).2 rfl
    simp [hφ0]
  have hzero :
      (((ν * 0 : ℝ) : EReal) - ((θ φ 0 : ℝ) : EReal)) = 0 := by
    rw [hθ0]
    simp
  have htest := thetaStar_ge_testPointAffineDefect (φ := φ) 0 ν
  rw [hzero] at htest
  simpa using htest

/-- Helper for Theorem 18 13: the integral remainder `θ φ` inherits evenness from `φ`. -/
lemma theta_even
    (hφ_even : Function.Even φ) :
    Function.Even (θ φ) := by
  intro s
  rw [theta_apply, theta_apply]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with t ht
  have harg : (-s) * t = -(s * t) := by
    ring
  simpa [harg] using congrArg (fun u : ℝ ↦ u / t) (hφ_even (s * t))

section Varrho

/-- The admissible nonnegative parameters in the defining inequality for the scalar control
function `ϱ`. -/
def varrhoSet (s : ℝ) : Set ℝ :=
  {ν : ℝ | 0 ≤ ν ∧ (2 : EReal) * thetaStar φ ν ≤ ((ν * s : ℝ) : EReal)}

/- Theorem 18.13 is source-facing. The scalar owners are the direct textbook functions `ψ`, `θ`,
and `ϱ`; `varrhoSet` is only their derived support API. -/

/-- Membership in the admissible set for `ϱ` is exactly the defining pair of conditions
`ν ≥ 0` and `2 θ*(ν) ≤ ν s`. -/
@[simp] theorem mem_varrhoSet
    (s ν : ℝ) :
    ν ∈ varrhoSet φ s ↔
      0 ≤ ν ∧ (2 : EReal) * thetaStar φ ν ≤ ((ν * s : ℝ) : EReal) :=
  Iff.rfl

variable (hφ_even : Function.Even φ)
  (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
  (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)

/-- Under the source hypotheses of Theorem 18.13, the admissible set defining `ϱ(s)` is
nonempty. -/
theorem varrhoSet_nonempty
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (s : ℝ) :
    (varrhoSet φ s).Nonempty := by
  refine ⟨0, ?_⟩
  constructor
  · norm_num
  · -- The zero parameter is admissible because the scalar conjugate vanishes at the origin.
    simp [thetaStar_zero_eq_zero φ hφ_even hφ_conv hφ_zero]

/-- Under the source hypotheses of Theorem 18.13, the admissible set defining `ϱ(s)` is bounded
above in `ℝ`. -/
theorem varrhoSet_bddAbove
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (s : ℝ) :
    BddAbove (varrhoSet φ s) := by
  by_cases hs : s < 0
  · refine ⟨0, ?_⟩
    intro ν hν
    have htwo_nonneg : (0 : EReal) ≤ (2 : EReal) * thetaStar φ ν := by
      exact mul_nonneg (by norm_num) (thetaStar_nonneg (φ := φ) hφ_zero ν)
    have hνs_nonneg : (0 : EReal) ≤ ((ν * s : ℝ) : EReal) := le_trans htwo_nonneg hν.2
    have hνs_nonpos : ((ν * s : ℝ) : EReal) ≤ 0 := by
      have hreal : ν * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hν.1 hs.le
      exact_mod_cast hreal
    have hνs_eq : ((ν * s : ℝ) : EReal) = 0 := le_antisymm hνs_nonpos hνs_nonneg
    have hνs_real : ν * s = 0 := by
      exact_mod_cast hνs_eq
    have hν_zero : ν = 0 := by
      refine (mul_eq_zero.mp hνs_real).resolve_right ?_
      exact ne_of_lt hs
    simp [hν_zero]
  · have hs_nonneg : 0 ≤ s := le_of_not_gt hs
    let r : ℝ := s + 1
    have hφ_nonneg : ∀ t : ℝ, 0 ≤ φ t :=
      phi_nonneg_of_even_convex_zero φ hφ_even hφ_conv hφ_zero
    have hθr_nonneg : 0 ≤ θ φ r :=
      theta_nonneg_of_phi_nonneg φ hφ_nonneg r
    refine ⟨2 * θ φ r, ?_⟩
    intro ν hν
    have htest := thetaStar_ge_testPointAffineDefect (φ := φ) r ν
    have hscaled :
        (2 : EReal) * ((((ν * r : ℝ) : EReal) - ((θ φ r : ℝ) : EReal))) ≤
          (2 : EReal) * thetaStar φ ν := by
      exact mul_le_mul_of_nonneg_left htest (by norm_num)
    have hbound :
        (2 : EReal) * ((((ν * r : ℝ) : EReal) - ((θ φ r : ℝ) : EReal))) ≤
          ((ν * s : ℝ) : EReal) := by
      exact le_trans hscaled hν.2
    have hbound' : (2 : EReal) * (((ν * r - θ φ r : ℝ) : EReal)) ≤ ((ν * s : ℝ) : EReal) := by
      simpa [EReal.coe_sub] using hbound
    have hbound'' : (((2 * (ν * r - θ φ r) : ℝ)) : EReal) ≤ ((ν * s : ℝ) : EReal) := by
      simpa [EReal.coe_mul] using hbound'
    have hbound_real : 2 * (ν * r - θ φ r) ≤ ν * s := by
      exact_mod_cast hbound''
    have hcoeff_ge_one : 1 ≤ 2 * r - s := by
      dsimp [r]
      linarith
    have hν_le_scaled : ν ≤ ν * (2 * r - s) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_right hcoeff_ge_one hν.1)
    have hscaled_bound : ν * (2 * r - s) ≤ 2 * θ φ r := by
      nlinarith [hbound_real]
    exact le_trans hν_le_scaled hscaled_bound

/-- The canonical `EReal` supremum underlying the scalar control function `ϱ`. -/
noncomputable def varrhoSup : ℝ → EReal :=
  fun s ↦ sSup (Real.toEReal '' varrhoSet φ s)

/-- Evaluating the canonical `EReal` supremum owner for `ϱ` rewrites it as the corresponding image
supremum. -/
@[simp] theorem varrhoSup_apply (s : ℝ) :
    varrhoSup φ s = sSup (Real.toEReal '' varrhoSet φ s) :=
  rfl

/-- Under the source hypotheses of Theorem 18.13, the canonical `EReal` supremum defining `ϱ(s)`
is not `-∞`. -/
theorem varrhoSup_ne_bot
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (s : ℝ) :
    varrhoSup φ s ≠ ⊥ := by
  rcases varrhoSet_nonempty φ hφ_even hφ_conv hφ_zero s with ⟨ν, hν⟩
  -- A real witness in the defining image set forces the supremum away from `⊥`.
  have hle : ((ν : ℝ) : EReal) ≤ varrhoSup φ s := by
    rw [varrhoSup_apply]
    exact le_sSup ⟨ν, hν, rfl⟩
  intro hbot
  rw [hbot] at hle
  simp at hle

/-- Under the source hypotheses of Theorem 18.13, the canonical `EReal` supremum defining `ϱ(s)`
is finite. -/
theorem varrhoSup_lt_top
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (s : ℝ) :
    varrhoSup φ s < ⊤ := by
  rcases varrhoSet_bddAbove φ hφ_even hφ_conv hφ_zero s with ⟨M, hM⟩
  have hsSup_le : varrhoSup φ s ≤ (M : EReal) := by
    rw [varrhoSup_apply]
    refine sSup_le ?_
    intro a ha
    rcases ha with ⟨ν, hν, rfl⟩
    exact_mod_cast hM hν
  exact lt_of_le_of_lt hsSup_le (EReal.coe_lt_top M)

/-- Under the source hypotheses of Theorem 18.13, the scalar control function `ϱ` attached to `φ`
is the real number represented by the finite `EReal` supremum `varrhoSup φ s`. -/
noncomputable def ϱ
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) :
    ℝ → ℝ :=
  fun s ↦
    let _ := hφ_even
    let _ := hφ_conv
    let _ := hφ_zero
    (varrhoSup φ s).toReal

/-- Evaluating `ϱ φ` at `s` gives the real representative of the finite `EReal` supremum
`varrhoSup φ s`. -/
@[simp] theorem varrho_apply
    (s : ℝ) :
    ϱ φ hφ_even hφ_conv hφ_zero s = (varrhoSup φ s).toReal :=
  rfl

/-- Coercing the real-valued source-facing owner `ϱ` to `EReal` recovers the canonical supremum
owner `varrhoSup`. -/
@[simp] theorem varrho_asEReal
    (s : ℝ) :
    ((ϱ φ hφ_even hφ_conv hφ_zero s : ℝ) : EReal) = varrhoSup φ s := by
  have hs_bot : varrhoSup φ s ≠ ⊥ :=
    varrhoSup_ne_bot φ hφ_even hφ_conv hφ_zero s
  have hs_top : varrhoSup φ s ≠ ⊤ :=
    ne_of_lt (varrhoSup_lt_top φ hφ_even hφ_conv hφ_zero s)
  -- The source-facing owner `ϱ` is defined by `toReal`, so coercing back recovers the supremum.
  simpa [ϱ] using (EReal.coe_toReal hs_top hs_bot)

end Varrho

variable [CompleteSpace H]

/- Route correction: the conjugate transport step should first be reduced to Proposition 17.35 on
the canonical `toEReal` owner, instead of trying to cancel finite `EReal` terms ad hoc later. -/
/-- Helper for Theorem 18 13: Proposition 17.35 specializes the conjugate of a differentiable
real-valued convex function at its gradient to the usual Fenchel--Young contact value. -/
lemma conjugate_gradient_eq_inner_sub_local
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (x : H) :
    f.toEReal.asEReal∗ (∇ f x) = (((⟪x, ∇ f x⟫_ℝ - f x : ℝ)) : EReal) := by
  have hx : x ∈ effectiveDomain f.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simp [Function.effectiveDomain_toEReal]
    · intro y hy z hz a ha0 ha1
      have hreal :
          f (a • y + (1 - a) • z) ≤ a * f y + (1 - a) * f z := by
        simpa [smul_eq_mul] using
          hconv.2 (by simp : y ∈ Set.univ) (by simp : z ∈ Set.univ) ha0.le
            (sub_nonneg.mpr ha1.le) (by linarith)
      change ((f (a • y + (1 - a) • z) : ℝ) : EReal) ≤
        ((a * f y + (1 - a) * f z : ℝ) : EReal)
      exact_mod_cast hreal
  have hgateaux :
      HasGateauxDerivativeAt
        (fun z ↦ (f.toEReal z : EReal).toReal)
        (toDualMap ℝ H (∇ f x)) x := by
    -- The Fréchet gradient gives the required Gâteaux derivative on the canonical owner.
    simpa using (((hdiff x).hasGradientAt).hasFDerivAt.hasGateauxDerivativeAt)
  have hsub : ∇ f x ∈ (∂ f.toEReal) x :=
    gateauxGradient_mem_subdifferential f.toEReal hconv_toEReal hx (∇ f x) hgateaux
  have hfy :
      (f.toEReal x : EReal) + f.toEReal.asEReal∗ (∇ f x) =
        ((⟪x, ∇ f x⟫_ℝ : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f.toEReal)
      (by simp [Function.effectiveDomain_toEReal]) x (∇ f x)).1 hsub
  have hx_top : (f.toEReal x : EReal) ≠ ⊤ := by
    simp [Function.toEReal_apply]
  have hx_bot : (f.toEReal x : EReal) ≠ ⊥ := by
    simp [Function.toEReal_apply]
  have hfy_left :
      f.toEReal.asEReal∗ (∇ f x) + (f.toEReal x : EReal) ≤
        ((⟪x, ∇ f x⟫_ℝ : ℝ) : EReal) := by
    simpa [Function.toEReal_apply, add_comm] using hfy.le
  have hfy_right :
      ((⟪x, ∇ f x⟫_ℝ : ℝ) : EReal) ≤
        f.toEReal.asEReal∗ (∇ f x) + (f.toEReal x : EReal) := by
    simpa [Function.toEReal_apply, add_comm] using hfy.symm.le
  -- Rearrange the finite Fenchel--Young equality to isolate the conjugate term.
  apply le_antisymm
  · exact
      (EReal.le_sub_iff_add_le (Or.inl hx_bot) (Or.inl hx_top)).2
        hfy_left
  · exact
      (EReal.sub_le_iff_le_add (Or.inl hx_bot) (Or.inl hx_top)).2
        hfy_right

/-- Helper for Theorem 18 13: composing `f` with the affine segment from `x` to `y` differentiates
to the gradient paired with the segment direction `y - x`. -/
private lemma hasDerivAt_comp_lineMap
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f) (x y : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s))
      ⟪y - x, ∇ f (AffineMap.lineMap x y t)⟫_ℝ t := by
  have hf :
      HasFDerivAt f (InnerProductSpace.toDual ℝ H (∇ f (AffineMap.lineMap x y t)))
        (AffineMap.lineMap x y t) :=
    (hdiff (AffineMap.lineMap x y t)).hasGradientAt.hasFDerivAt
  have hline : HasDerivAt (AffineMap.lineMap x y) (y - x) t :=
    AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)
  have hlineF :
      HasFDerivAt (AffineMap.lineMap x y)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (y - x)) t :=
    hline.hasFDerivAt
  -- Compose the derivative of `f` with the derivative of the affine segment.
  simpa [Function.comp, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    (hf.comp t hlineF).hasDerivAt

/-- Helper for Theorem 18 13: the segment defect
`t ↦ f(lineMap x y t) - t * ⟪y - x, ∇f x⟫` differentiates to the translated gradient pairing. -/
lemma segmentLinearization_hasDerivAt
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f) (x y : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s) - s * ⟪y - x, ∇ f x⟫_ℝ)
      (⟪y - x, ∇ f (AffineMap.lineMap x y t) - ∇ f x⟫_ℝ) t := by
  have hcomp :
      HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s))
        ⟪y - x, ∇ f (AffineMap.lineMap x y t)⟫_ℝ t :=
    hasDerivAt_comp_lineMap (f := f) hdiff x y t
  have hlin :
      HasDerivAt (fun s : ℝ ↦ s * ⟪y - x, ∇ f x⟫_ℝ)
        ⟪y - x, ∇ f x⟫_ℝ t := by
    simpa using (hasDerivAt_id t).mul_const ⟪y - x, ∇ f x⟫_ℝ
  have htmp := hcomp.sub hlin
  -- Rewrite the derivative of the defect in the normalized source form.
  convert htmp using 1
  rw [inner_sub_right]

omit [CompleteSpace H] in
/-- Helper for Theorem 18 13: the radial scalar owner `θ φ` conjugates to `θ* φ` on every real
Hilbert space. -/
lemma thetaRadialConjugate_eq_thetaStar_norm
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (w : H) :
    ((((θ φ).toEReal ∘ (norm : H → ℝ)).asEReal∗) w) = thetaStar φ ‖w‖ := by
  have hφ_nonneg : ∀ s : ℝ, 0 ≤ φ s :=
    phi_nonneg_of_even_convex_zero φ hφ_even hφ_conv hφ_zero
  have hθ_nonneg : ∀ s : ℝ, 0 ≤ θ φ s :=
    theta_nonneg_of_phi_nonneg φ hφ_nonneg
  have hθ_even_toEReal : Function.Even ((θ φ).toEReal) := by
    intro s
    apply Subtype.ext
    exact congrArg (fun t : ℝ ↦ (t : EReal)) (theta_even (φ := φ) hφ_even s)
  have hθ0 : θ φ 0 = 0 := by
    rw [theta_apply]
    have hφ0 : φ 0 = 0 := (hφ_zero 0).2 rfl
    simp [hφ0]
  have hsubsingleton_min :
      Subsingleton H → ∀ t : ℝ, (((θ φ).toEReal 0 : Set.Ioi (⊥ : EReal)) : EReal) ≤
        (((θ φ).toEReal t : Set.Ioi (⊥ : EReal)) : EReal) := by
    intro _ t
    have hzero : (((θ φ).toEReal 0 : Set.Ioi (⊥ : EReal)) : EReal) = 0 := by
      change ((θ φ 0 : ℝ) : EReal) = 0
      exact_mod_cast hθ0
    have ht_nonneg : 0 ≤ θ φ t := hθ_nonneg t
    have hcoe : (0 : EReal) ≤ (((θ φ).toEReal t : Set.Ioi (⊥ : EReal)) : EReal) := by
      change (0 : EReal) ≤ ((θ φ t : ℝ) : EReal)
      exact_mod_cast ht_nonneg
    rw [hzero]
    exact hcoe
  have hconj :=
    congrFun
      (conjugate_comp_norm_eq_comp_norm_conjugate_of_even_all_spaces
        (H := H) ((θ φ).toEReal) hθ_even_toEReal hsubsingleton_min)
      w
  simpa [thetaStar, thetaConj, Function.comp] using hconj

omit [CompleteSpace H] in
/-- Helper for Theorem 18 13: translating the radial affine defect by `x` does not change its
supremum, so the shifted supremum still equals `θ*(‖w‖)`. -/
lemma shiftedThetaAffineDefect_eq_thetaStar_norm
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (x w : H) :
    (⨆ z : H, (((⟪z - x, w⟫_ℝ : ℝ) : EReal) - ((θ φ ‖z - x‖ : ℝ) : EReal))) =
      thetaStar φ ‖w‖ := by
  calc
    (⨆ z : H, (((⟪z - x, w⟫_ℝ : ℝ) : EReal) - ((θ φ ‖z - x‖ : ℝ) : EReal))) =
        ⨆ u : H, (((⟪u, w⟫_ℝ : ℝ) : EReal) - ((θ φ ‖u‖ : ℝ) : EReal)) := by
          exact ((Equiv.addRight x).surjective.iSup_congr (Equiv.addRight x) fun u => by
            simp [sub_eq_add_neg]).symm
    _ = ((((θ φ).toEReal ∘ (norm : H → ℝ)).asEReal∗) w) := by
          rw [conjugate_apply]
          simp [Function.comp_apply, Function.asEReal_apply, Function.toEReal_apply]
    _ = thetaStar φ ‖w‖ :=
          thetaRadialConjugate_eq_thetaStar_norm (φ := φ) hφ_even hφ_conv hφ_zero w

-- Semantic recall: `lean_leansearch` confirmed mathlib's canonical gradient owner `gradient f x`
-- and the bridge from `Differentiable ℝ f` to `HasGradientAt f (∇ f x) x`. The labeled
-- implications below therefore stay source-facing on `f`, `∇ f`, and `φ`; any stronger
-- `(gradf, hgrad)` generalization belongs only to downstream helper API.
-- Proof sketch: apply Cauchy--Schwarz to bound the inner product by
-- `‖x - y‖ * ‖∇ f x - ∇ f y‖`, then invoke the assumed `ψ`-control and the identity
-- `ψ(r) * r = φ(r)` for `r = ‖x - y‖`.
/-- Clause (i) ⇒ (ii) in Theorem 18.13: the pointwise gradient norm bound by `ψ`
implies the scalar inner-product
bound by `φ`. -/
theorem gradient_inner_le_phi_of_gradient_norm_bound_by_psi
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (hi : ∀ x y : H, ‖∇ f x - ∇ f y‖ ≤ ψ φ ‖x - y‖) (x y : H) :
    ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ φ ‖x - y‖ := by
  let _ := f
  let _ := hdiff
  let _ := hconv
  let _ := hφ_even
  let _ := hφ_conv
  let r : ℝ := ‖x - y‖
  have hinner :
      ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ r * ‖∇ f x - ∇ f y‖ := by
    -- First control the inner product by Cauchy--Schwarz.
    simpa [r, mul_comm] using real_inner_le_norm (x - y) (∇ f x - ∇ f y)
  have hpsi :
      r * ‖∇ f x - ∇ f y‖ ≤ r * ψ φ r := by
    -- Then insert the assumed `ψ`-bound on the gradient increment.
    exact mul_le_mul_of_nonneg_left (hi x y) (by simp [r])
  have hmul : r * ψ φ r = φ r := by
    by_cases hr : r = 0
    · have hφ0 : φ 0 = 0 := (hφ_zero 0).2 rfl
      simp [r, hr, psi_zero, hφ0]
    · rw [psi_eq_div_abs_of_ne φ hr]
      rw [abs_of_nonneg (by simp [r])]
      field_simp [hr]
  -- The defining identity `r * ψ(r) = φ(r)` closes the estimate.
  calc
    ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ r * ‖∇ f x - ∇ f y‖ := hinner
    _ ≤ r * ψ φ r := hpsi
    _ = φ r := hmul
    _ = φ ‖x - y‖ := by rfl

-- Proof sketch: integrate along the segment `x + t • (y - x)`. The Fréchet derivative identifies
-- the derivative of `t ↦ f (x + t • (y - x))` with the inner product against `∇ f`, and the
-- hypothesis from clause (ii) bounds the integrand by `φ (t * ‖x - y‖) / t`, whose integral is
-- `θ φ ‖x - y‖`.
/-- Clause (ii) ⇒ (iii) in Theorem 18.13: the scalar inner-product bound by `φ`
implies the usual descent estimate
with remainder `θ`. -/
theorem descent_le_linearization_add_theta_of_gradient_inner_le_phi
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (hii : ∀ x y : H, ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ φ ‖x - y‖) (x y : H) :
    f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + θ φ ‖x - y‖ := by
  let r : ℝ := ‖x - y‖
  let defect : ℝ → ℝ := fun t ↦ ⟪y - x, ∇ f (AffineMap.lineMap x y t) - ∇ f x⟫_ℝ
  let scalarBound : ℝ → ℝ := fun t ↦ φ (t * r) / t
  have hconv_toEReal : ConvexOn f.toEReal (effectiveDomain f.toEReal) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simp [Function.effectiveDomain_toEReal]
    · intro a ha b hb α hα0 hα1
      have hreal :
          f (α • a + (1 - α) • b) ≤ α * f a + (1 - α) * f b := by
        simpa using
          hconv.2 (by simp : a ∈ Set.univ) (by simp : b ∈ Set.univ) hα0.le
            (sub_nonneg.mpr hα1.le) (by linarith)
      change ((f (α • a + (1 - α) • b) : ℝ) : EReal) ≤
        ((α * f a + (1 - α) * f b : ℝ) : EReal)
      exact_mod_cast hreal
  have hgrad_support :
      ∀ a b : H, ⟪b - a, ∇ f a⟫_ℝ + f a ≤ f b := by
    intro a b
    have ha : a ∈ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hgateaux :
        HasGateauxDerivativeAt
          (fun z ↦ (f.toEReal z : EReal).toReal)
          (toDualMap ℝ H (∇ f a)) a := by
      simpa using (((hdiff a).hasGradientAt).hasFDerivAt.hasGateauxDerivativeAt)
    have hsupp :
        (⟪b - a, ∇ f a⟫_ℝ : EReal) + (f.toEReal a : EReal) ≤ (f.toEReal b : EReal) :=
      gateauxGradient_add_value_le (f := f.toEReal) (hconv := hconv_toEReal)
        (x := a) (hx := ha) (gradf := ∇ f a) (hgrad := hgateaux) b
    have hsupp' :
        (((⟪b - a, ∇ f a⟫_ℝ + f a : ℝ)) : EReal) ≤ ((f b : ℝ) : EReal) := by
      simpa [Function.toEReal_apply, EReal.coe_add] using hsupp
    exact_mod_cast hsupp'
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt
          (fun s : ℝ ↦ f (AffineMap.lineMap x y s) - s * ⟪y - x, ∇ f x⟫_ℝ)
          (defect t) t := by
    intro t ht
    simpa [defect] using segmentLinearization_hasDerivAt (f := f) hdiff x y t
  have hdefect_mono : MonotoneOn defect (Set.uIcc (0 : ℝ) 1) := by
    intro s hs t ht hst
    by_cases hst_eq : s = t
    · simp [hst_eq]
    · let xs : H := AffineMap.lineMap x y s
      let xt : H := AffineMap.lineMap x y t
      have hsupport₁ : ⟪xt - xs, ∇ f xs⟫_ℝ + f xs ≤ f xt := hgrad_support xs xt
      have hsupport₂ : f xt ≤ ⟪xt - xs, ∇ f xt⟫_ℝ + f xs := by
        have hbase : ⟪xs - xt, ∇ f xt⟫_ℝ + f xt ≤ f xs := hgrad_support xt xs
        have hbase' : -⟪xt - xs, ∇ f xt⟫_ℝ + f xt ≤ f xs := by
          have hsub : xs - xt = -(xt - xs) := by
            abel
          rw [hsub, inner_neg_left] at hbase
          exact hbase
        linarith
      have hmono_real : 0 ≤ ⟪xt - xs, ∇ f xt - ∇ f xs⟫_ℝ := by
        have hxs_le_hxt : ⟪xt - xs, ∇ f xs⟫_ℝ ≤ ⟪xt - xs, ∇ f xt⟫_ℝ := by
          linarith
        rw [inner_sub_right]
        linarith
      have hline_sub : xt - xs = (t - s) • (y - x) := by
        calc
          xt - xs = (xt - x) - (xs - x) := by
            dsimp [xs, xt]
            abel
          _ = t • (y - x) - s • (y - x) := by
            rw [show xt - x = t • (y - x) by
                simpa [xt, vsub_eq_sub] using AffineMap.lineMap_vsub_left x y t]
            rw [show xs - x = s • (y - x) by
                simpa [xs, vsub_eq_sub] using AffineMap.lineMap_vsub_left x y s]
          _ = (t - s) • (y - x) := by
            rw [sub_smul]
      have hinner_eq :
          ⟪xt - xs, ∇ f xt - ∇ f xs⟫_ℝ = (t - s) * (defect t - defect s) := by
        dsimp [defect, xs, xt]
        rw [hline_sub, real_inner_smul_left, inner_sub_right, inner_sub_right, inner_sub_right]
        ring
      have hscaled :
          0 ≤ (t - s) * (defect t - defect s) := by
        simpa [hinner_eq] using hmono_real
      have hts : s < t := lt_of_le_of_ne hst hst_eq
      have hts_pos : 0 < t - s := sub_pos.mpr hts
      have hdefect_diff_nonneg : 0 ≤ defect t - defect s :=
        nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hscaled) hts_pos
      linarith
  have hdefect_int : IntervalIntegrable defect MeasureTheory.volume 0 1 :=
    hdefect_mono.intervalIntegrable
  have hφ_nonneg : ∀ s : ℝ, 0 ≤ φ s :=
    phi_nonneg_of_even_convex_zero φ hφ_even hφ_conv hφ_zero
  have hscalarBound_mono : MonotoneOn scalarBound (Set.uIcc (0 : ℝ) 1) := by
    intro s hs t ht hst
    by_cases hst_eq : s = t
    · simp [hst_eq]
    · by_cases hs0 : s = 0
      · subst hs0
        by_cases ht0 : t = 0
        · simp [scalarBound, ht0]
        · have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
            simpa using ht
          have ht_nonneg : 0 ≤ t := ht_mem.1
          have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht0)
          have hnonneg : 0 ≤ scalarBound t := by
            simpa [scalarBound, mul_comm] using div_nonneg (hφ_nonneg (t * r)) ht_nonneg
          simpa [scalarBound] using hnonneg
      · let g : ℝ → ℝ := fun u ↦ φ (u * r)
        have hg_conv : _root_.ConvexOn ℝ Set.univ g := by
          have hg_comp :
              _root_.ConvexOn ℝ Set.univ (φ ∘ ⇑(AffineMap.lineMap (0 : ℝ) r)) :=
            hφ_conv.comp_affineMap (AffineMap.lineMap (0 : ℝ) r)
          convert hg_comp using 1 with u
          funext u
          rw [Function.comp_apply, AffineMap.lineMap_apply_ring]
          simp [g]
        have hφ0 : φ 0 = 0 := (hφ_zero 0).2 rfl
        have hsec :
            (g s - g 0) / (s - 0) ≤ (g t - g 0) / (t - 0) :=
          hg_conv.secant_mono (a := 0) (x := s) (y := t) (by simp) (by simp) (by simp) hs0
            (by
              have hts : s < t := lt_of_le_of_ne hst hst_eq
              have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
                simpa using hs
              exact ne_of_gt (lt_trans (lt_of_le_of_ne hs_mem.1 (Ne.symm hs0)) hts))
            hst
        simpa [g, scalarBound, hφ0] using hsec
  have hscalarBound_int : IntervalIntegrable scalarBound MeasureTheory.volume 0 1 :=
    hscalarBound_mono.intervalIntegrable
  have hdefect_le :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, defect t ≤ scalarBound t := by
    intro t ht
    by_cases ht0 : t = 0
    · simp [defect, scalarBound, ht0]
    · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hline : AffineMap.lineMap x y t - x = t • (y - x) := by
        simpa [vsub_eq_sub] using AffineMap.lineMap_vsub_left x y t
      have hnorm :
          ‖AffineMap.lineMap x y t - x‖ = t * r := by
        calc
          ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by rw [hline]
          _ = |t| * ‖y - x‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ = t * r := by simp [r, norm_sub_rev, abs_of_nonneg ht.1]
      have hscaled :
          t * defect t ≤ φ (t * r) := by
        have hraw :
            ⟪AffineMap.lineMap x y t - x, ∇ f (AffineMap.lineMap x y t) - ∇ f x⟫_ℝ ≤
              φ ‖AffineMap.lineMap x y t - x‖ := by
          simpa using hii (AffineMap.lineMap x y t) x
        have hnorm' : ‖t • (y - x)‖ = t * r := by
          simpa [hline] using hnorm
        rw [hline, real_inner_smul_left, hnorm'] at hraw
        simpa [defect] using hraw
      exact (le_div_iff₀ ht_pos).2 (by simpa [scalarBound, mul_comm] using hscaled)
  have hint_le :
      ∫ t in (0 : ℝ)..1, defect t ≤ ∫ t in (0 : ℝ)..1, scalarBound t := by
    exact intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (a := 0) (b := 1)
      (f := defect) (g := scalarBound) zero_le_one hdefect_int hscalarBound_int hdefect_le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hdefect_int
  have hdefect_eq :
      ∫ t in (0 : ℝ)..1, defect t = f y - ⟪y - x, ∇ f x⟫_ℝ - f x := by
    simpa [defect, AffineMap.lineMap_apply_module, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hFTC
  have hmodel : f y - ⟪y - x, ∇ f x⟫_ℝ - f x ≤ θ φ r := by
    rw [← hdefect_eq, theta_apply]
    simpa [scalarBound, r, mul_comm] using hint_le
  linarith

-- Semantic recall/local precedent: the Chapter 18 gradient-conjugate surface uses
-- `_root_.ConvexOn ℝ Set.univ f`, `Differentiable ℝ f`, the canonical gradient `∇ f`, and the
-- full source-side hypotheses on `φ`.
/-- Theorem 18.13. Clause (iii) ⇒ (iv): the descent estimate with remainder `θ`
implies the Fenchel-conjugate
lower bound involving `θ*` along the gradient image. -/
theorem conjugate_gradient_ge_affine_add_thetaConjugate_of_descent_le_linearization_add_theta
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (hiii : ∀ x y : H, f y ≤ f x + ⟪y - x, ∇ f x⟫_ℝ + θ φ ‖x - y‖)
    (x y : H) :
    f.toEReal.asEReal∗ (∇ f y) ≥
      f.toEReal.asEReal∗ (∇ f x) +
        (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
          thetaStar φ ‖∇ f x - ∇ f y‖ := by
  let w : H := ∇ f y - ∇ f x
  let c : ℝ := ⟪x, ∇ f y⟫_ℝ - f x
  have hsup :
      ((c : ℝ) : EReal) +
          (⨆ z : H, (((⟪z - x, w⟫_ℝ : ℝ) : EReal) - ((θ φ ‖z - x‖ : ℝ) : EReal))) ≤
        f.toEReal.asEReal∗ (∇ f y) := by
    rw [add_comm, ← ereal_iSup_add_of_real_shift c
      (fun z : H ↦ (((⟪z - x, w⟫_ℝ : ℝ) : EReal) - ((θ φ ‖z - x‖ : ℝ) : EReal))),
      conjugate_apply]
    refine iSup_le ?_
    intro z
    have hz : f z ≤ f x + ⟪z - x, ∇ f x⟫_ℝ + θ φ ‖x - z‖ := hiii x z
    have hmain :
        ((c : ℝ) : EReal) +
            ((((⟪z - x, w⟫_ℝ : ℝ) : EReal) - ((θ φ ‖z - x‖ : ℝ) : EReal))) ≤
          (((⟪z, ∇ f y⟫_ℝ : ℝ) : EReal) - ((f z : ℝ) : EReal)) := by
      refine (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 ?_
      have hz' : f z ≤ f x + ⟪z - x, ∇ f x⟫_ℝ + θ φ ‖z - x‖ := by
        simpa [norm_sub_rev] using hz
      have hsum_real :
          c + (⟪z - x, w⟫_ℝ - θ φ ‖z - x‖) + f z ≤ ⟪z, ∇ f y⟫_ℝ := by
        have hupper :
            c + (⟪z - x, w⟫_ℝ - θ φ ‖z - x‖) + f z ≤
              c + (⟪z - x, w⟫_ℝ - θ φ ‖z - x‖) +
                (f x + ⟪z - x, ∇ f x⟫_ℝ + θ φ ‖z - x‖) := by
          gcongr
        have hidentity :
            c + (⟪z - x, w⟫_ℝ - θ φ ‖z - x‖) +
                (f x + ⟪z - x, ∇ f x⟫_ℝ + θ φ ‖z - x‖) =
              ⟪z, ∇ f y⟫_ℝ := by
          have hinner_sum :
              ⟪x + (z - x), ∇ f y⟫_ℝ = ⟪z, ∇ f y⟫_ℝ := by
            have hxz : x + (z - x) = z := by
              abel
            exact congrArg (fun u : H ↦ ⟪u, ∇ f y⟫_ℝ) hxz
          calc
            c + (⟪z - x, w⟫_ℝ - θ φ ‖z - x‖) +
                (f x + ⟪z - x, ∇ f x⟫_ℝ + θ φ ‖z - x‖) =
                ⟪x, ∇ f y⟫_ℝ + ⟪z - x, ∇ f y⟫_ℝ := by
                  dsimp [c, w]
                  rw [inner_sub_right]
                  ring
            _ = ⟪x + (z - x), ∇ f y⟫_ℝ := by
                  rw [← inner_add_left]
            _ = ⟪z, ∇ f y⟫_ℝ := hinner_sum
        exact hidentity ▸ hupper
      exact_mod_cast hsum_real
    exact le_trans (by simpa [add_comm] using hmain) <|
      le_iSup
        (fun u : H ↦ (((⟪u, ∇ f y⟫_ℝ : ℝ) : EReal) - (Function.asEReal (Function.toEReal f) u)))
        z
  have hxconj := conjugate_gradient_eq_inner_sub_local (f := f) hdiff hconv x
  have hc :
      ((c : ℝ) : EReal) =
        f.toEReal.asEReal∗ (∇ f x) + (⟪x, w⟫_ℝ : EReal) := by
    have hreal : c = (⟪x, ∇ f x⟫_ℝ - f x) + ⟪x, w⟫_ℝ := by
      dsimp [c, w]
      rw [inner_sub_right]
      ring
    calc
      ((c : ℝ) : EReal) = ((((⟪x, ∇ f x⟫_ℝ - f x) + ⟪x, w⟫_ℝ : ℝ)) : EReal) := by
        exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
      _ = (((⟪x, ∇ f x⟫_ℝ - f x : ℝ)) : EReal) + (⟪x, w⟫_ℝ : EReal) := by
        rw [EReal.coe_add]
      _ = f.toEReal.asEReal∗ (∇ f x) + (⟪x, w⟫_ℝ : EReal) := by
        rw [hxconj]
  calc
    f.toEReal.asEReal∗ (∇ f y) ≥
        ((c : ℝ) : EReal) +
          (⨆ z : H, (((⟪z - x, w⟫_ℝ : ℝ) : EReal) - ((θ φ ‖z - x‖ : ℝ) : EReal))) :=
      hsup
    _ = f.toEReal.asEReal∗ (∇ f x) + (⟪x, w⟫_ℝ : EReal) + thetaStar φ ‖w‖ := by
      rw [hc, shiftedThetaAffineDefect_eq_thetaStar_norm (φ := φ) hφ_even hφ_conv hφ_zero]
    _ = f.toEReal.asEReal∗ (∇ f x) + (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
          thetaStar φ ‖∇ f x - ∇ f y‖ := by
      simp [w, norm_sub_rev, add_assoc]

/-- Clause (iv) ⇒ (v) in Theorem 18.13: the Fenchel-conjugate lower bound implies the lower bound
`⟪x - y, ∇f(x) - ∇f(y)⟫ ≥ 2 θ*(‖∇f(x) - ∇f(y)‖)`. -/
theorem gradient_inner_ge_two_thetaConjugate_of_conjugate_gradient_ge_affine_add_thetaConjugate
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (hiv :
      ∀ x y : H,
        f.toEReal.asEReal∗ (∇ f y) ≥
          f.toEReal.asEReal∗ (∇ f x) +
            (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) +
              thetaStar φ ‖∇ f x - ∇ f y‖)
    (x y : H) :
    ((⟪x - y, ∇ f x - ∇ f y⟫_ℝ : ℝ) : EReal) ≥
      (2 : EReal) * thetaStar φ ‖∇ f x - ∇ f y‖ := by
  let _ := hφ_even
  let _ := hφ_conv
  let _ := hφ_zero
  let T : EReal := thetaStar φ ‖∇ f x - ∇ f y‖
  have hxconj := conjugate_gradient_eq_inner_sub_local (f := f) hdiff hconv x
  have hyconj := conjugate_gradient_eq_inner_sub_local (f := f) hdiff hconv y
  have hxy' :
      f.toEReal.asEReal∗ (∇ f x) + (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) + T ≤
        f.toEReal.asEReal∗ (∇ f y) := by
    exact hiv x y
  have hyx' :
      f.toEReal.asEReal∗ (∇ f y) + (⟪y, ∇ f x - ∇ f y⟫_ℝ : EReal) + T ≤
        f.toEReal.asEReal∗ (∇ f x) := by
    simpa [T, norm_sub_rev] using hiv y x
  rw [hxconj, hyconj] at hxy' hyx'
  have hxy_left :
      (((⟪x, ∇ f x⟫_ℝ - f x : ℝ)) : EReal) + (⟪x, ∇ f y - ∇ f x⟫_ℝ : EReal) =
        ((⟪x, ∇ f y⟫_ℝ - f x : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    rw [inner_sub_right]
    ring
  have hyx_left :
      (((⟪y, ∇ f y⟫_ℝ - f y : ℝ)) : EReal) + (⟪y, ∇ f x - ∇ f y⟫_ℝ : EReal) =
        ((⟪y, ∇ f x⟫_ℝ - f y : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    rw [inner_sub_right]
    ring
  rw [hxy_left] at hxy'
  rw [hyx_left] at hyx'
  have hxy_aux :
      T ≤ (((f x - f y + ⟪y - x, ∇ f y⟫_ℝ : ℝ)) : EReal) := by
    have hsub :
        T ≤
          (((⟪y, ∇ f y⟫_ℝ - f y : ℝ) : EReal) -
            ((⟪x, ∇ f y⟫_ℝ - f x : ℝ) : EReal)) := by
      exact
        (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2
          (by simpa [add_comm] using hxy')
    have hreal :
        (⟪y, ∇ f y⟫_ℝ - f y) - (⟪x, ∇ f y⟫_ℝ - f x) =
          f x - f y + ⟪y - x, ∇ f y⟫_ℝ := by
      rw [inner_sub_left]
      ring
    change T ≤ ((((⟪y, ∇ f y⟫_ℝ - f y) - (⟪x, ∇ f y⟫_ℝ - f x) : ℝ)) : EReal) at hsub
    simpa [hreal] using hsub
  have hyx_aux :
      T ≤ (((f y - f x + ⟪x - y, ∇ f x⟫_ℝ : ℝ)) : EReal) := by
    have hsub :
        T ≤
          (((⟪x, ∇ f x⟫_ℝ - f x : ℝ) : EReal) -
            ((⟪y, ∇ f x⟫_ℝ - f y : ℝ) : EReal)) := by
      exact
        (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2
          (by simpa [add_comm] using hyx')
    have hreal :
        (⟪x, ∇ f x⟫_ℝ - f x) - (⟪y, ∇ f x⟫_ℝ - f y) =
          f y - f x + ⟪x - y, ∇ f x⟫_ℝ := by
      rw [inner_sub_left]
      ring
    change T ≤ ((((⟪x, ∇ f x⟫_ℝ - f x) - (⟪y, ∇ f x⟫_ℝ - f y) : ℝ)) : EReal) at hsub
    simpa [hreal] using hsub
  have hsum :
      T + T ≤
        (((f x - f y + ⟪y - x, ∇ f y⟫_ℝ : ℝ)) : EReal) +
          (((f y - f x + ⟪x - y, ∇ f x⟫_ℝ : ℝ)) : EReal) := by
    exact add_le_add hxy_aux hyx_aux
  have hreal :
      (f x - f y + ⟪y - x, ∇ f y⟫_ℝ) + (f y - f x + ⟪x - y, ∇ f x⟫_ℝ) =
        ⟪x - y, ∇ f x - ∇ f y⟫_ℝ := by
    have hswap : ⟪y - x, ∇ f y⟫_ℝ = -⟪x - y, ∇ f y⟫_ℝ := by
      have hxy : y - x = -(x - y) := by
        abel
      rw [hxy, inner_neg_left]
    rw [hswap, inner_sub_right]
    ring
  have hsum' :
      T + T ≤
        (((f x - f y + ⟪y - x, ∇ f y⟫_ℝ) +
          (f y - f x + ⟪x - y, ∇ f x⟫_ℝ) : ℝ) : EReal) := by
    simpa [EReal.coe_add] using hsum
  have hsum'' :
      T + T ≤ (((⟪x - y, ∇ f x - ∇ f y⟫_ℝ : ℝ)) : EReal) := by
    convert hsum' using 1
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal.symm
  have htwo : (2 : EReal) * T = T + T := by
    cases T using WithBot.recBotCoe with
    | bot =>
        change (((2 : ℝ) : EReal) * (⊥ : EReal) = ⊥)
        have h2pos : (0 : ℝ) < 2 := by
          norm_num
        rw [EReal.coe_mul_bot_of_pos h2pos]
    | coe a =>
        cases a using WithTop.recTopCoe with
        | top =>
            change (((2 : ℝ) : EReal) * (⊤ : EReal) = ⊤ + ⊤)
            have h2pos : (0 : ℝ) < 2 := by
              norm_num
            rw [EReal.coe_mul_top_of_pos h2pos]
            simp
        | coe r =>
            change (((2 : ℝ) : EReal) * ((r : ℝ) : EReal) = ((r : ℝ) : EReal) + ((r : ℝ) : EReal))
            simp [← EReal.coe_mul, two_mul]
  rw [htwo]
  exact hsum''

/-- Clause (v) ⇒ (vi) in Theorem 18.13: the lower bound by `2 θ*` implies the
gradient norm estimate controlled by
`ϱ`. -/
theorem gradient_norm_le_varrho_of_gradient_inner_ge_two_thetaConjugate
    (f : H → ℝ)
    (hdiff : Differentiable ℝ f)
    (hconv : _root_.ConvexOn ℝ Set.univ f)
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (hv :
      ∀ x y : H,
        ((⟪x - y, ∇ f x - ∇ f y⟫_ℝ : ℝ) : EReal) ≥
          (2 : EReal) * thetaStar φ ‖∇ f x - ∇ f y‖)
    (x y : H) :
    ‖∇ f x - ∇ f y‖ ≤ ϱ φ hφ_even hφ_conv hφ_zero ‖x - y‖ := by
  let _ := f
  let _ := hdiff
  let _ := hconv
  let ν : ℝ := ‖∇ f x - ∇ f y‖
  let s : ℝ := ‖x - y‖
  have hinner_real :
      ⟪x - y, ∇ f x - ∇ f y⟫_ℝ ≤ ν * s := by
    -- Cauchy--Schwarz turns the hypothesis into the defining `ϱ`-set inequality.
    simpa [ν, s, mul_comm] using real_inner_le_norm (x - y) (∇ f x - ∇ f y)
  have hinner :
      (((⟪x - y, ∇ f x - ∇ f y⟫_ℝ : ℝ) : EReal)) ≤ ((ν * s : ℝ) : EReal) := by
    exact_mod_cast hinner_real
  have hmem : ν ∈ varrhoSet φ s := by
    constructor
    · exact norm_nonneg _
    · -- The chosen `ν` satisfies the admissibility inequality by hypothesis and Cauchy--Schwarz.
      exact le_trans (by simpa [ν] using hv x y) hinner
  have hν_le_sup : ((ν : ℝ) : EReal) ≤ varrhoSup φ s := by
    rw [varrhoSup_apply]
    exact le_sSup ⟨ν, hmem, rfl⟩
  rw [← varrho_asEReal (φ := φ) (hφ_even := hφ_even) (hφ_conv := hφ_conv)
    (hφ_zero := hφ_zero) (s := s)] at hν_le_sup
  exact_mod_cast hν_le_sup

end StrongerDifferentiabilityBounds

end

end ERealFunction
