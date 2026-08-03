import Mathlib
import BauschkeLean.Chap01.Theorem_1_46
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Example_16_32
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Theorem_16_29
import BauschkeLean.Chap16.Theorem_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: translating the base point of a convex function does not change the
subgradient vector; it only shifts the evaluation point. -/
lemma mem_subdifferential_translate_iff
    {f : H → Set.Ioi (⊥ : EReal)} {x0 z u : H} :
    u ∈ (∂ fun w : H ↦ f (x0 + w)) z ↔ u ∈ (∂ f) (x0 + z) := by
  rw [mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · intro hu y
    have hshift : y - x0 - z = y - (x0 + z) := by
      abel
    simpa [hshift] using hu (y - x0)
  · intro hu y
    have hshift : x0 + y - (x0 + z) = y - z := by
      abel
    simpa [hshift] using hu (x0 + y)

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: translating a `Γ₀(H)` function by a base point preserves
membership in `Γ₀(H)`. -/
lemma translate_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (x0 : H) :
    (fun z : H ↦ f (x0 + z)) ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · simpa using hf.1.comp (continuous_const.add continuous_id)
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases hf.2.nonempty with ⟨x, hx⟩
      refine ⟨x - x0, ?_⟩
      change (f (x0 + (x - x0)) : EReal) < ⊤
      simpa using hx
    · intro x hx y hy a ha0 ha1
      have hexpand :
          a • x0 + a • x + ((1 - a) • x0 + (1 - a) • y) =
            x0 + (a • x + (1 - a) • y) := by
        calc
          a • x0 + a • x + ((1 - a) • x0 + (1 - a) • y)
              = (a • x0 + (1 - a) • x0) + (a • x + (1 - a) • y) := by
                abel
          _ = ((a + (1 - a)) • x0) + (a • x + (1 - a) • y) := by
                rw [← add_smul]
          _ = x0 + (a • x + (1 - a) • y) := by
                simp
      simpa [smul_add, hexpand] using
        hf.2.ineq (x := x0 + x) hx (y := x0 + y) hy ha0 ha1

/-- Helper for Theorem 16 58: affine tilting adds the linear perturbation `x ↦ -⟪x, u⟫` to an
`EReal`-valued function. -/
noncomputable def affineTiltEReal (φ : H → EReal) (u : H) : H → EReal :=
  fun x ↦ φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal))

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: evaluating the affine tilt exposes the added linear term. -/
@[simp] theorem affineTiltEReal_apply
    (φ : H → EReal) (u x : H) :
    affineTiltEReal φ u x = φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal)) :=
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: affine tilting a `Γ₀(H)` function preserves properness. -/
theorem affine_tilt_isProper
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    IsProper (affineTiltEReal f.asEReal u) := by
  have htilt_eq_coe :
      ∀ ⦃x : H⦄, x ∈ effectiveDomain f →
        affineTiltEReal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
    intro x hx
    have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  constructor
  · intro x
    by_cases hx : x ∈ effectiveDomain f
    · rw [htilt_eq_coe hx]
      exact EReal.coe_ne_bot _
    · have hx_top : f.asEReal x = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
      rw [affineTiltEReal, hx_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
      simp
  · rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_dom_iff, htilt_eq_coe hx]
    simpa using (EReal.coe_lt_top (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ)))

/-- Helper for Theorem 16 58: package the affine tilt back into the `]-∞,+∞]` codomain expected
by the convex-analysis API. -/
noncomputable abbrev affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (affineTiltEReal f.asEReal u) (affine_tilt_isProper f hf u)

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: coercing the packaged affine tilt back to `EReal` recovers the raw
tilted function. -/
@[simp] theorem affineTiltIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u x : H) :
    (affineTiltIoi f hf u x : EReal) = affineTiltEReal f.asEReal u x := by
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: the affine tilt of a `Γ₀(H)` function again belongs to `Γ₀(H)`. -/
theorem affine_tilt_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    affineTiltIoi f hf u ∈ Γ₀(H) := by
  have hlinear_gamma :
      (fun x : H ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) ∈ Γ(H) := by
    rw [mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      change (((-(⟪a • x + (1 - a) • y, u⟫_ℝ) : ℝ) : EReal)) ≤
        (a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
          (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))
      have hreal :
          -(⟪a • x + (1 - a) • y, u⟫_ℝ) =
            a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      have hsub : (1 - (a : EReal)) = (((1 - a : ℝ)) : EReal) := by
        norm_num
      rw [hreal, hsub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    · simpa using
        (continuous_coe_real_ereal.comp
          ((continuous_id.inner continuous_const).neg)).lowerSemicontinuous
  have htilt_gamma : affineTiltEReal f.asEReal u ∈ Γ(H) := by
    have hf_gamma : f.asEReal ∈ Γ(H) := asEReal_mem_gamma_of_mem_gammaZero hf
    rw [mem_gamma_iff] at hf_gamma hlinear_gamma ⊢
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      have haE_nonneg : (0 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha0
      have hbE_nonneg : (0 : EReal) ≤ (1 - a : EReal) := by
        exact_mod_cast sub_nonneg.mpr ha1
      have haE_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
      have hbE_ne_top : (1 - a : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - a)
      calc
        affineTiltEReal f.asEReal u (a • x + (1 - a) • y)
            ≤ ((a : EReal) * f.asEReal x + (1 - a : EReal) * f.asEReal y) +
                ((a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
                  (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))) := by
              simpa [affineTiltEReal] using
                add_le_add (hf_gamma.1 ha0 ha1) (hlinear_gamma.1 ha0 ha1)
        _ = (a : EReal) * affineTiltEReal f.asEReal u x +
              (1 - a : EReal) * affineTiltEReal f.asEReal u y := by
              simp [affineTiltEReal,
                EReal.left_distrib_of_nonneg_of_ne_top haE_nonneg haE_ne_top,
                EReal.left_distrib_of_nonneg_of_ne_top hbE_nonneg hbE_ne_top,
                add_assoc, add_left_comm]
    · rw [lowerSemicontinuous_iff_le_liminf]
      intro x
      calc
        affineTiltEReal f.asEReal u x
            ≤ Filter.liminf f.asEReal (nhds x) +
                Filter.liminf (fun y : H ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal))) (nhds x) := by
              simpa [affineTiltEReal] using
                add_le_add (hf_gamma.2.le_liminf x) (hlinear_gamma.2.le_liminf x)
        _ ≤ Filter.liminf (affineTiltEReal f.asEReal u) (nhds x) := by
              simpa [affineTiltEReal] using
                (EReal.le_liminf_add :
                  Filter.liminf f.asEReal (nhds x) +
                      Filter.liminf
                        (fun y : H ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                        (nhds x) ≤
                    Filter.liminf
                      (fun y : H ↦
                        f.asEReal y + (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                      (nhds x))
  exact properIoi_mem_gammaZero_of_mem_gamma (affine_tilt_isProper f hf u) htilt_gamma

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: affine tilting does not change the effective domain. -/
theorem effectiveDomain_affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    effectiveDomain (affineTiltIoi f hf u) = effectiveDomain f := by
  ext x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hvalue :
        affineTiltEReal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
      rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
      simp [sub_eq_add_neg]
    rw [affineTiltIoi_apply, hvalue]
    constructor
    · intro _
      exact mem_effectiveDomain_iff.mp hx
    · intro _
      exact EReal.coe_lt_top _
  · rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hx_top : f.asEReal x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    rw [affineTiltIoi_apply, affineTiltEReal, hx_top,
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
    simp [hx_top]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: the `]-∞,+∞]`-valued norm function belongs to `Γ₀(H)`. -/
lemma norm_toEReal_mem_gammaZero :
    ((norm : H → ℝ).toEReal) ∈ Γ₀(H) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha hb
    have hnorm :
        ‖a • x + (1 - a) • y‖ ≤ a * ‖x‖ + (1 - a) * ‖y‖ := by
      simpa [smul_eq_mul] using
        (convexOn_univ_norm.2 (by simp) (by simp) ha (sub_nonneg.mpr hb) (by ring) :
          ‖a • x + (1 - a) • y‖ ≤ a • ‖x‖ + (1 - a) • ‖y‖)
    change ((‖a • x + (1 - a) • y‖ : ℝ) : EReal) ≤
      (((a * ‖x‖ + (1 - a) * ‖y‖ : ℝ)) : EReal)
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    exact_mod_cast hnorm
  · simpa using (continuous_coe_real_ereal.comp continuous_norm).lowerSemicontinuous

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: evaluating a conjugate at the origin rewrites it as the negative
infimum of the range. -/
lemma conjugate_zero_eq_neg_sInf_range_local (φ : H → EReal) :
    φ∗ 0 = -sInf (Set.range φ) := by
  calc
    φ∗ 0 = ⨆ x : H, -φ x := by
      simp [conjugate_apply]
    _ = -(⨅ x : H, φ x) := by
      exact (OrderIso.map_iInf EReal.negOrderIso (fun x : H ↦ φ x)).symm
    _ = -sInf (Set.range φ) := by
      rw [sInf_range]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: subgradients of the affine tilt are shifted by the tilting vector. -/
lemma mem_subdifferential_affineTiltIoi_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (v z u : H) :
    u ∈ (∂ affineTiltIoi f hf v) z ↔ u + v ∈ (∂ f) z := by
  rw [mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · intro hu y
    have huy := hu y
    have hadded := add_le_add_right huy (((⟪y, v⟫_ℝ : ℝ) : EReal))
    have hleft :
        (((⟪y, v⟫_ℝ : ℝ) : EReal) +
            ((⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z)) =
          (⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal) := by
      have hreal : ⟪y, v⟫_ℝ + -⟪z, v⟫_ℝ = ⟪y - z, v⟫_ℝ := by
        simpa [sub_eq_add_neg] using (inner_sub_left y z v).symm
      calc
        (((⟪y, v⟫_ℝ : ℝ) : EReal) +
            ((⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z))
            = (f z : EReal) +
                (((⟪y, v⟫_ℝ + (-⟪z, v⟫_ℝ) + ⟪y - z, u⟫_ℝ : ℝ) : EReal)) := by
                  rw [affineTiltEReal, EReal.coe_add, EReal.coe_add]
                  simp [add_assoc, add_left_comm, add_comm]
        _ = (f z : EReal) + (((⟪y - z, v⟫_ℝ + ⟪y - z, u⟫_ℝ : ℝ) : EReal)) := by
              rw [hreal]
        _ = (⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal) := by
              rw [inner_add_right, EReal.coe_add]
              simp [add_comm]
    have hright :
        (((⟪y, v⟫_ℝ : ℝ) : EReal) + affineTiltEReal f.asEReal v y) = (f y : EReal) := by
      calc
        (((⟪y, v⟫_ℝ : ℝ) : EReal) + affineTiltEReal f.asEReal v y)
            = (f y : EReal) +
                (((⟪y, v⟫_ℝ + -⟪y, v⟫_ℝ : ℝ) : EReal)) := by
                  rw [affineTiltEReal, EReal.coe_add]
                  simp [add_left_comm]
        _ = (f y : EReal) := by
              simp
    have hplain : (⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal) ≤ (f y : EReal) := by
      rw [← hleft, ← hright]
      simpa [affineTiltIoi_apply] using hadded
    exact hplain
  · intro hu y
    have huy := hu y
    have hadded := add_le_add_right huy (((-⟪y, v⟫_ℝ : ℝ) : EReal))
    have hleft :
        (((-⟪y, v⟫_ℝ : ℝ) : EReal) + ((⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal))) =
          (⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z := by
      have hreal : -⟪y, v⟫_ℝ + ⟪y - z, v⟫_ℝ = -⟪z, v⟫_ℝ := by
        rw [inner_sub_left]
        ring
      have hreal' :
          -⟪y, v⟫_ℝ + (⟪y - z, v⟫_ℝ + ⟪y - z, u⟫_ℝ) =
            -⟪z, v⟫_ℝ + ⟪y - z, u⟫_ℝ := by
        rw [← add_assoc, hreal]
      calc
        (((-⟪y, v⟫_ℝ : ℝ) : EReal) + ((⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal)))
            = (f z : EReal) +
                (((-⟪y, v⟫_ℝ + (⟪y - z, v⟫_ℝ + ⟪y - z, u⟫_ℝ) : ℝ) : EReal)) := by
                  rw [inner_add_right, EReal.coe_add, EReal.coe_add]
                  simp [add_left_comm, add_comm]
        _ = (f z : EReal) + (((-⟪z, v⟫_ℝ + ⟪y - z, u⟫_ℝ : ℝ) : EReal)) := by
              rw [hreal']
        _ = (⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z := by
              rw [affineTiltEReal, EReal.coe_add]
              simp [sub_eq_add_neg, add_assoc, add_comm]
    have hright :
        (((-⟪y, v⟫_ℝ : ℝ) : EReal) + (f y : EReal)) = affineTiltEReal f.asEReal v y := by
      simp [affineTiltEReal, add_comm]
    have htilted :
        (⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z ≤ affineTiltEReal f.asEReal v y := by
      rw [← hleft, ← hright]
      exact hadded
    simpa [affineTiltIoi_apply] using htilted

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: the penalty subgradient at the base point of a translated norm has
norm bounded by the scaling factor. -/
lemma norm_le_of_mem_subdifferential_posReal_smul_norm_translate
    (γ : PosReal) (z q : H)
    (hq : q ∈ (∂ fun x : H ↦ (γ • ((norm : H → ℝ).toEReal)) (-z + x)) z) :
    ‖q‖ ≤ (γ : ℝ) := by
  have hq0 :
      q ∈ (∂ ((γ • ((norm : H → ℝ).toEReal) : H → Set.Ioi (⊥ : EReal)))) (0 : H) := by
    simpa using
      (mem_subdifferential_translate_iff
        (f := (γ • ((norm : H → ℝ).toEReal) : H → Set.Ioi (⊥ : EReal)))
        (x0 := -z) (z := z) (u := q)).1 hq
  rw [subdifferential_posReal_smul_eq_smul ((norm : H → ℝ).toEReal) γ] at hq0
  change q ∈ (γ : ℝ) • ((∂ ((norm : H → ℝ).toEReal)) (0 : H)) at hq0
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hq0
  have hnorm_subdifferential :
      (∂ ((norm : H → ℝ).toEReal)) (0 : H) = Metric.closedBall (0 : H) 1 := by
    simpa using subdifferential_norm_eq_singleton_or_closedBall (H := H) (0 : H)
  have hunit :
      (γ : ℝ)⁻¹ • q ∈ Metric.closedBall (0 : H) 1 := by
    simpa [hnorm_subdifferential] using hq0
  have hunit_norm : ‖(γ : ℝ)⁻¹ • q‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hunit
  have hq_scaled :
      ‖(γ : ℝ)⁻¹ • q‖ = (γ : ℝ)⁻¹ * ‖q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr γ.2.le)]
  have hscaled_le : (γ : ℝ)⁻¹ * ‖q‖ ≤ 1 := by
    simpa [hq_scaled] using hunit_norm
  have hmul_le := mul_le_mul_of_nonneg_left hscaled_le γ.2.le
  simpa [γ.2.ne', hq_scaled, mul_assoc, mul_left_comm, mul_comm] using hmul_le

/- Source/core/bridge triage:
- `source-facing`: Theorem 16.58 is the Brøndsted--Rockafellar approximation statement.
- `core/canonical`: the owner abstractions are the subdifferential `∂ f` and the packaged
  `Γ₀(H)` Fenchel conjugate `f∗[hf]`.
- `bridge/view`: graph language for `∂ f` is derived from the primitive data `z`, `w`, and
  `w ∈ (∂ f) z`, so the public surface keeps the latter and avoids pair-projection bookkeeping.
-/

-- Proof sketch: apply Ekeland's variational principle to the shifted function
-- `x ↦ (f x : EReal) - ⟪x, v⟫`. The gap hypothesis makes `y` an approximate minimizer with error
-- `λ * μ`. Ekeland yields `z` with `‖z - y‖ ≤ λ` such that `z` minimizes the perturbation by
-- `μ ‖· - z‖`. Fermat's rule puts `0` in the subdifferential of that perturbation at `z`, the
-- sum rule splits the subdifferential, and the norm subdifferential formula produces
-- `w ∈ (∂ f) z` with `‖w - v‖ ≤ μ`.
/-- Theorem 16 58: the Brondsted--Rockafellar approximation theorem. For `f ∈ Γ₀(H)`, if the
Fenchel--Young gap at `(y, v)` is at most `λμ`, then there exist `z` and `w ∈ (∂ f) z` with
`z` within distance `λ` of `y` and `w` within distance `μ` of `v`. -/
theorem exists_subgradient_point_close_of_fenchelYoung_gap_le
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (y v : H) (lam μ : NNReal)
    (hgap :
      (f y : EReal) + (f∗[hf] v : EReal) ≤
        ((⟪y, v⟫_ℝ + ((lam * μ : NNReal) : ℝ) : ℝ) : EReal)) :
    ∃ z w, w ∈ (∂ f) z ∧ ‖z - y‖ ≤ (lam : ℝ) ∧ ‖w - v‖ ≤ (μ : ℝ) := by
  have hexact_case :
      lam = 0 ∨ μ = 0 →
        ∃ z w, w ∈ (∂ f) z ∧ ‖z - y‖ ≤ (lam : ℝ) ∧ ‖w - v‖ ≤ (μ : ℝ) := by
    intro hzero
    have hgap_exact :
        (f y : EReal) + (f∗[hf] v : EReal) ≤ ((⟪y, v⟫_ℝ : ℝ) : EReal) := by
      rcases hzero with hlam | hμ
      · simpa [hlam] using hgap
      · simpa [hμ] using hgap
    have hfy :
        ((⟪y, v⟫_ℝ : ℝ) : EReal) ≤ (f y : EReal) + (f∗[hf] v : EReal) := by
      simpa [gammaZeroConjugate_apply] using
        fenchel_young_inequality (f := f.asEReal) (isProper_of_mem_gammaZero hf) y v
    have hfy_eq :
        (f y : EReal) + (f∗[hf] v : EReal) = ((⟪y, v⟫_ℝ : ℝ) : EReal) :=
      le_antisymm hgap_exact hfy
    have hv : v ∈ (∂ f) y := by
      exact (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty y v).2 hfy_eq
    rcases hzero with hlam | hμ
    · refine ⟨y, v, hv, ?_, ?_⟩
      · simp [hlam]
      · simp
    · refine ⟨y, v, hv, ?_, ?_⟩
      · simp
      · simp [hμ]
  by_cases hlam : lam = 0
  · exact hexact_case (Or.inl hlam)
  by_cases hμ : μ = 0
  · exact hexact_case (Or.inr hμ)
  let ψ : H → Set.Ioi (⊥ : EReal) := affineTiltIoi f hf v
  have hψ : ψ ∈ Γ₀(H) := by
    simpa [ψ] using affine_tilt_mem_gammaZero (f := f) (hf := hf) v
  have hy_dom_f : y ∈ effectiveDomain f := by
    by_contra hy_dom_f
    have hy_top : (f y : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy_dom_f))
    have hlhs_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hy_top, EReal.top_add_of_ne_bot (ne_of_gt (f∗[hf] v).2)]
    have hrhs_ne_top :
        (((⟪y, v⟫_ℝ + ((lam * μ : NNReal) : ℝ) : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
    exact hrhs_ne_top (le_antisymm le_top (hlhs_top ▸ hgap))
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom_f)
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hvconj_top : (f∗[hf] v : EReal) ≠ ⊤ := by
    intro hvconj_top
    have hlhs_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hvconj_top, EReal.add_top_of_ne_bot hy_bot]
    have hrhs_ne_top :
        (((⟪y, v⟫_ℝ + ((lam * μ : NNReal) : ℝ) : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
    exact hrhs_ne_top (le_antisymm le_top (hlhs_top ▸ hgap))
  have hvconj_bot : (f∗[hf] v : EReal) ≠ ⊥ := ne_of_gt (f∗[hf] v).2
  have hconj_val :
      (f∗[hf] v : EReal) = ((((f∗[hf] v : EReal).toReal : ℝ) : EReal)) :=
    (EReal.coe_toReal hvconj_top hvconj_bot).symm
  have hψy_eq :
      (ψ y : EReal) = (((f y : EReal).toReal - ⟪y, v⟫_ℝ : ℝ) : EReal) := by
    change (f y : EReal) + (((-⟪y, v⟫_ℝ : ℝ) : EReal)) =
      (((f y : EReal).toReal - ⟪y, v⟫_ℝ : ℝ) : EReal)
    rw [← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  have hψy_top : (ψ y : EReal) ≠ ⊤ := by
    rw [hψy_eq]
    exact EReal.coe_ne_top _
  have hψy_bot : (ψ y : EReal) ≠ ⊥ := by
    rw [hψy_eq]
    exact EReal.coe_ne_bot _
  have hgap_real :
      (f y : EReal).toReal + (f∗[hf] v : EReal).toReal ≤
        ⟪y, v⟫_ℝ + (lam : ℝ) * (μ : ℝ) := by
    have hcast :
        ((((f y : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal)) ≤
          (((⟪y, v⟫_ℝ + (lam : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
      calc
        ((((f y : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal))
            = ((((f y : EReal).toReal : ℝ) : EReal)) +
                ((((f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
                  rw [EReal.coe_add]
        _ = (f y : EReal) + (f∗[hf] v : EReal) := by
              rw [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hvconj_top hvconj_bot]
        _ ≤ (((⟪y, v⟫_ℝ + (lam : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
              simpa [NNReal.coe_mul] using hgap
    exact EReal.coe_le_coe_iff.mp hcast
  have hψy_toReal :
      (ψ y : EReal).toReal = (f y : EReal).toReal - ⟪y, v⟫_ℝ := by
    rw [hψy_eq]
    exact EReal.toReal_coe _
  have hψgap_real :
      (ψ y : EReal).toReal + (f∗[hf] v : EReal).toReal ≤ (lam : ℝ) * (μ : ℝ) := by
    rw [hψy_toReal]
    nlinarith
  have hlam_pos : 0 < (lam : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hlam)
  have hμ_pos : 0 < (μ : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hμ)
  let γ : PosReal := ⟨(lam : ℝ) / (μ : ℝ), by positivity⟩
  let z : H := Prox[γ, ψ, hψ] y
  have hprox : IsProxPoint (γ • ψ) y z := by
    simpa [z, scaledProximityOperator] using
      proximityOperator_isProxPoint
        (γ • ψ)
        (hasUniqueProxPoint_of_mem_gammaZero (γ • ψ) (smul_mem_gammaZero ψ hψ γ))
        y
  have hprox_var :
      ∀ x, (⟪x - z, y - z⟫_ℝ : EReal) + (((γ • ψ) z : Set.Ioi (⊥ : EReal)) : EReal) ≤
        (((γ • ψ) x : Set.Ioi (⊥ : EReal)) : EReal) :=
    (isProxPoint_iff_forall_inner_add_le (γ • ψ) (smul_mem_gammaZero ψ hψ γ).2 y z).1 hprox
  have hz_dom_psi : z ∈ effectiveDomain ψ := by
    rcases hψ.2.nonempty with ⟨q, hq⟩
    by_contra hz_dom_psi
    have hz_top' : (ψ z : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hz_dom_psi))
    have hscaled_top : ((γ • ψ) z : EReal) = ⊤ := by
      rw [posReal_smul_apply, hz_top']
      simpa using (EReal.coe_mul_top_of_pos γ.2 : ((γ : ℝ) : EReal) * ⊤ = ⊤)
    have hq_scaled_ne_top : ((γ • ψ) q : EReal) ≠ ⊤ := by
      rw [posReal_smul_apply, EReal.mul_ne_top]
      exact
        ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
          Or.inl (EReal.coe_ne_top (γ : ℝ)),
          Or.inr (ne_of_lt (mem_effectiveDomain_iff.mp hq))⟩
    have hsum_top : (⟪q - z, y - z⟫_ℝ : EReal) + ((γ • ψ) z : EReal) = ⊤ := by
      rw [hscaled_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    have hvar_q := hprox_var q
    rw [hsum_top] at hvar_q
    exact hq_scaled_ne_top (top_le_iff.mp hvar_q)
  have hz_top : (ψ z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom_psi)
  have hz_bot : (ψ z : EReal) ≠ ⊥ := ne_of_gt (ψ z).2
  have hz_dom_f : z ∈ effectiveDomain f := by
    rw [← effectiveDomain_affineTiltIoi (f := f) (hf := hf) v]
    exact hz_dom_psi
  have hzf_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom_f)
  have hzf_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
  have hψz_eq :
      (ψ z : EReal) = (((f z : EReal).toReal - ⟪z, v⟫_ℝ : ℝ) : EReal) := by
    change (f z : EReal) + (((-⟪z, v⟫_ℝ : ℝ) : EReal)) =
      (((f z : EReal).toReal - ⟪z, v⟫_ℝ : ℝ) : EReal)
    rw [← EReal.coe_toReal hzf_top hzf_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  have hψz_toReal :
      (ψ z : EReal).toReal = (f z : EReal).toReal - ⟪z, v⟫_ℝ := by
    rw [hψz_eq]
    exact EReal.toReal_coe _
  -- The proximal-point variational inequality is exactly subgradient membership for `γ • ψ`.
  have hscaled_subgrad : y - z ∈ (∂ (γ • ψ)) z := by
    rw [mem_subdifferential_iff]
    exact hprox_var
  rw [subdifferential_posReal_smul_eq_smul ψ γ] at hscaled_subgrad
  change y - z ∈ (γ : ℝ) • ((∂ ψ) z) at hscaled_subgrad
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hscaled_subgrad
  let u : H := (γ : ℝ)⁻¹ • (y - z)
  have hu : u ∈ (∂ ψ) z := by
    simpa [u] using hscaled_subgrad
  have hfy_z_real :
      ⟪z, v⟫_ℝ ≤ (f z : EReal).toReal + (f∗[hf] v : EReal).toReal := by
    have hcast :
        (((⟪z, v⟫_ℝ : ℝ) : EReal)) ≤
          ((((f z : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
      calc
        (((⟪z, v⟫_ℝ : ℝ) : EReal)) ≤ (f z : EReal) + (f∗[hf] v : EReal) := by
          simpa [gammaZeroConjugate_apply] using
            (fenchel_young_inequality (f := f.asEReal) (isProper_of_mem_gammaZero hf) z v)
        _ = ((((f z : EReal).toReal : ℝ) : EReal)) +
              ((((f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
                rw [EReal.coe_toReal hzf_top hzf_bot, EReal.coe_toReal hvconj_top hvconj_bot]
        _ = ((((f z : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
              rw [EReal.coe_add]
    exact EReal.coe_le_coe_iff.mp hcast
  have htilt_gap_real :
      (ψ y : EReal).toReal - (ψ z : EReal).toReal ≤ (lam : ℝ) * (μ : ℝ) := by
    rw [hψz_toReal]
    nlinarith
  have hdist_cast :
      (((‖y - z‖ ^ 2 + (γ : ℝ) * (ψ z : EReal).toReal : ℝ) : EReal)) ≤
        ((((γ : ℝ) * (ψ y : EReal).toReal : ℝ) : EReal)) := by
    simpa [posReal_smul_apply, EReal.coe_add, EReal.coe_mul, EReal.coe_toReal hz_top hz_bot,
      EReal.coe_toReal hψy_top hψy_bot, real_inner_self_eq_norm_sq] using hprox_var y
  have hdist_real :
      ‖y - z‖ ^ 2 + (γ : ℝ) * (ψ z : EReal).toReal ≤ (γ : ℝ) * (ψ y : EReal).toReal := by
    exact EReal.coe_le_coe_iff.mp hdist_cast
  have hz_close_sq : ‖y - z‖ ^ 2 ≤ (lam : ℝ) ^ 2 := by
    have hdist_bound :
        ‖y - z‖ ^ 2 ≤ (γ : ℝ) * ((ψ y : EReal).toReal - (ψ z : EReal).toReal) := by
      nlinarith [hdist_real]
    have hγ_val : (γ : ℝ) = (lam : ℝ) / (μ : ℝ) := rfl
    rw [hγ_val] at hdist_bound
    have hscaled :
        ‖y - z‖ ^ 2 ≤ ((lam : ℝ) / (μ : ℝ)) * ((lam : ℝ) * (μ : ℝ)) := by
      exact le_trans hdist_bound (mul_le_mul_of_nonneg_left htilt_gap_real (by positivity))
    have hcancel :
        ((lam : ℝ) / (μ : ℝ)) * ((lam : ℝ) * (μ : ℝ)) = (lam : ℝ) ^ 2 := by
      field_simp [hμ_pos.ne']
    rw [hcancel] at hscaled
    exact hscaled
  have hz_close : ‖z - y‖ ≤ (lam : ℝ) := by
    have hyz_sq : ‖z - y‖ ^ 2 ≤ (lam : ℝ) ^ 2 := by
      simpa [norm_sub_rev] using hz_close_sq
    nlinarith [hyz_sq]
  have hu_norm : ‖u‖ ≤ (μ : ℝ) := by
    have hu_norm_eq : ‖u‖ = (γ : ℝ)⁻¹ * ‖y - z‖ := by
      calc
        ‖u‖ = ‖(γ : ℝ)⁻¹ • (y - z)‖ := by rfl
        _ = (γ : ℝ)⁻¹ * ‖y - z‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr γ.2.le)]
    have hγinv : (γ : ℝ)⁻¹ = (μ : ℝ) / (lam : ℝ) := by
      dsimp [γ]
      field_simp [hlam_pos.ne', hμ_pos.ne']
    rw [hu_norm_eq, hγinv]
    have hyz_le : ‖y - z‖ ≤ (lam : ℝ) := by
      simpa [norm_sub_rev] using hz_close
    have hscaled :
        ((μ : ℝ) / (lam : ℝ)) * ‖y - z‖ ≤ ((μ : ℝ) / (lam : ℝ)) * (lam : ℝ) :=
      mul_le_mul_of_nonneg_left hyz_le (by positivity)
    have hcancel : ((μ : ℝ) / (lam : ℝ)) * (lam : ℝ) = (μ : ℝ) := by
      field_simp [hlam_pos.ne']
    simpa [hcancel] using hscaled
  have hw : u + v ∈ (∂ f) z := by
    exact (mem_subdifferential_affineTiltIoi_iff (f := f) (hf := hf) v z u).1 hu
  refine ⟨z, u + v, hw, hz_close, ?_⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu_norm

end SubdifferentialCalculus

end ERealFunction
