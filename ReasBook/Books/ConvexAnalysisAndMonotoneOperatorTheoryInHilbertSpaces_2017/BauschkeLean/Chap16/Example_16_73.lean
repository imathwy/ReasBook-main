import Mathlib
import BauschkeLean.Chap08.Corollary_8_40
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap13.Example_13_8
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap16.Example_16_32
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

/-- Helper for Example 16 73: on `ℝ`, the inner product is ordinary multiplication. -/
private lemma real_inner_eq_mul_scalar (s t : ℝ) :
    inner ℝ s t = s * t := by
  calc
    inner ℝ s t = (starRingEnd ℝ) s * t := RCLike.inner_apply' s t
    _ = s * t := by simp

section ScalarAndRadialSubdifferential

variable (φ : ℝ → ℝ)

/-- Helper for Example 16 73: a continuous convex real-valued function on `ℝ` packages as a
member of `Γ₀(ℝ)` after applying `toEReal`. -/
private lemma real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(ℝ) := by
  -- Package the real-valued formula through the Chapter 9 `Γ(ℝ)` owner first.
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · -- The real Jensen inequality transfers directly through the `EReal` coercion.
    intro x y a ha0 ha1
    have hreal :
        φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0 (sub_nonneg.mpr ha1) (by ring)
    change ((φ (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * φ x + (1 - a) * φ y : ℝ) : EReal)
    exact_mod_cast hreal
  · -- Continuity of the real formula gives lower semicontinuity of its `EReal` coercion.
    simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/- Source/core/bridge triage:
- `source-facing`: Example 16.73 records the scalar subdifferential formula for `φ` at `0` and
  the radial subdifferential formulas for `y ↦ φ ‖y‖`.
- `core/canonical`: clause `(1)` is governed by the scalar owner `∂` on `ℝ`, together with the
  one-dimensional monotonicity API of Proposition 17.16 and the continuity/subdifferential owner
  of Proposition 16.17. Clauses `(2)` and `(3)` are governed by the radial membership criterion of
  Example 16.31 and the norm subdifferential formula of Example 16.32.
- `bridge/view`: clause `(2)` packages the owner membership description as a pointwise scalar
  action on the normalized ray, while clause `(3)` specializes the zero branch to the closed ball
  determined by clause `(1)`.
-/

/-- Helper for Example 16 73: evenness makes the scalar subdifferential at `0` symmetric under
negation. -/
private lemma subdifferential_zero_neg_mem_of_even
    (heven : Function.Even φ) {a : ℝ} (ha : a ∈ (∂ φ.toEReal) 0) :
    -a ∈ (∂ φ.toEReal) 0 := by
  rw [mem_subdifferential_iff] at ha ⊢
  intro y
  -- Evaluate the original subgradient inequality at `-y` and rewrite it back to the slope `-a`.
  have hy : (((inner ℝ (-y - 0) a) + φ 0 : ℝ) : EReal) ≤ ((φ (-y) : ℝ) : EReal) := by
    simpa [Function.toEReal_apply, EReal.coe_add] using ha (-y)
  have hy' : (((inner ℝ (y - 0) (-a)) + φ 0 : ℝ) : EReal) ≤ ((φ y : ℝ) : EReal) := by
    calc
      (((inner ℝ (y - 0) (-a)) + φ 0 : ℝ) : EReal) =
          (((inner ℝ (-y - 0) a) + φ 0 : ℝ) : EReal) := by
            simp [real_inner_eq_mul_scalar]
      _ ≤ ((φ (-y) : ℝ) : EReal) := hy
      _ = ((φ y : ℝ) : EReal) := by rw [heven y]
  simpa [Function.toEReal_apply, EReal.coe_add] using hy'

/-- Helper for Example 16 73: every scalar subgradient at `0` lies between the two affine tests at
`1` and `-1`. -/
private lemma subdifferential_zero_subset_interval_of_even
    (heven : Function.Even φ) :
    (∂ φ.toEReal) 0 ⊆ Set.Icc (φ 0 - φ 1) (φ 1 - φ 0) := by
  intro a ha
  constructor
  · -- Testing at `-1` controls the lower endpoint.
    have htest := (mem_subdifferential_iff (f := φ.toEReal) 0 a).1 ha (-1)
    have hreal : -a + φ 0 ≤ φ 1 :=
      EReal.coe_le_coe_iff.mp <|
        by
          have htestE : (((-a) + φ 0 : ℝ) : EReal) ≤ ((φ 1 : ℝ) : EReal) := by
            calc
              (((-a) + φ 0 : ℝ) : EReal) =
                  (((inner ℝ (-1 - 0) a) + φ 0 : ℝ) : EReal) := by
                    simp [real_inner_eq_mul_scalar]
              _ ≤ ((φ (-1) : ℝ) : EReal) := by
                    simpa [Function.toEReal_apply, EReal.coe_add] using htest
              _ = ((φ 1 : ℝ) : EReal) := by rw [heven 1]
          exact htestE
    linarith
  · -- Testing at `1` controls the upper endpoint.
    have htest := (mem_subdifferential_iff (f := φ.toEReal) 0 a).1 ha 1
    have hreal : a + φ 0 ≤ φ 1 :=
      EReal.coe_le_coe_iff.mp <|
        by simpa [Function.toEReal_apply, EReal.coe_add, real_inner_eq_mul_scalar] using htest
    linarith

/-- Helper for Example 16 73: a nonempty closed convex symmetric bounded subset of `ℝ` is a
centered closed interval. -/
private lemma subdifferential_zero_eq_interval_of_closed_convex_symmetric_bounded
    {S : Set ℝ} (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    (hS_bddBelow : BddBelow S) (hS_bddAbove : BddAbove S)
    (hS_symm : ∀ {a : ℝ}, a ∈ S → -a ∈ S) :
    ∃ ρ : NNReal, S = Set.Icc (-(ρ : ℝ)) (ρ : ℝ) := by
  have hS_connected : IsConnected S := hS_convex.isConnected hS_nonempty
  have hS_eq_interval : S = Set.Icc (sInf S) (sSup S) :=
    eq_Icc_csInf_csSup_of_connected_bdd_closed hS_connected hS_bddBelow hS_bddAbove hS_closed
  have hsInf_mem : sInf S ∈ S := hS_closed.csInf_mem hS_nonempty hS_bddBelow
  have hsSup_mem : sSup S ∈ S := hS_closed.csSup_mem hS_nonempty hS_bddAbove
  have hInf_le_negSup : sInf S ≤ -sSup S :=
    (isGLB_csInf hS_nonempty hS_bddBelow).1 (hS_symm hsSup_mem)
  have hNegInf_le_sup : -(sInf S) ≤ sSup S :=
    (isLUB_csSup hS_nonempty hS_bddAbove).1 (hS_symm hsInf_mem)
  have hNegSup_le_inf : -sSup S ≤ sInf S := by
    linarith
  have hInf_eq_negSup : sInf S = -sSup S := le_antisymm hInf_le_negSup hNegSup_le_inf
  have hInf_le_sup : sInf S ≤ sSup S :=
    (isLUB_csSup hS_nonempty hS_bddAbove).1 hsInf_mem
  have hSup_nonneg : 0 ≤ sSup S := by
    linarith [hInf_le_sup, hInf_eq_negSup]
  refine ⟨⟨sSup S, hSup_nonneg⟩, ?_⟩
  -- Replace the generic endpoints by the symmetric pair `[-ρ, ρ]`.
  simpa [hInf_eq_negSup] using hS_eq_interval

-- Proof sketch: view the real-valued scalar function `φ` through `φ.toEReal`. Corollary
-- 8.40 makes `φ` continuous, so `φ.toEReal ∈ Γ₀(ℝ)`. Proposition 16.17(ii) identifies
-- `(∂ φ.toEReal) 0` as a nonempty weakly compact interval, evenness makes it symmetric,
-- and Proposition 11.7(ii) gives monotonicity on `ℝ₊`, yielding the radius `ρ`.
/-- Example 16 73 (1): if `φ : ℝ → ℝ` is convex and even, then the scalar subdifferential at `0`
is a symmetric interval `[-ρ, ρ]` for some `ρ ∈ ℝ₊`. -/
theorem exists_symmetric_subdifferential_zero_eq_interval
    (hconv : _root_.ConvexOn ℝ Set.univ φ) (heven : Function.Even φ) :
    ∃ ρ : NNReal, (∂ φ.toEReal) 0 = Set.Icc (-(ρ : ℝ)) (ρ : ℝ) := by
  have hcont : Continuous φ := continuous_of_convexOn_univ φ hconv
  have hconv_toEReal : ConvexOn φ.toEReal (effectiveDomain φ.toEReal) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy a ha0 ha1
      have hreal :
          φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
        simpa [smul_eq_mul] using
          hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by ring)
      change ((φ (a • x + (1 - a) • y) : ℝ) : EReal) ≤
        ((a * φ x + (1 - a) * φ y : ℝ) : EReal)
      exact_mod_cast hreal
  have hzero_cont : ContinuousAtOnEffectiveDomain φ.toEReal 0 := by
    constructor
    · simp [Function.effectiveDomain_toEReal]
    · simpa
        [Function.effectiveDomain_toEReal, Function.toEReal_apply, continuousWithinAt_univ] using
          hcont.continuousAt
  have hsub_nonempty :
      ((∂ φ.toEReal) 0).Nonempty :=
    (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
      φ.toEReal hconv_toEReal hzero_cont).1
  have hsub_closed : IsClosed ((∂ φ.toEReal) 0) := isClosed_subdifferential φ.toEReal 0
  have hsub_convex : Convex ℝ ((∂ φ.toEReal) 0) := convex_subdifferential φ.toEReal 0
  have hsub_bounds :
      (∂ φ.toEReal) 0 ⊆ Set.Icc (φ 0 - φ 1) (φ 1 - φ 0) :=
    subdifferential_zero_subset_interval_of_even (φ := φ) heven
  have hsub_bddBelow : BddBelow ((∂ φ.toEReal) 0) := by
    refine ⟨φ 0 - φ 1, ?_⟩
    intro a ha
    exact (hsub_bounds ha).1
  have hsub_bddAbove : BddAbove ((∂ φ.toEReal) 0) := by
    refine ⟨φ 1 - φ 0, ?_⟩
    intro a ha
    exact (hsub_bounds ha).2
  -- The scalar fiber is a nonempty closed convex symmetric bounded subset of `ℝ`, hence a
  -- centered interval.
  exact
    subdifferential_zero_eq_interval_of_closed_convex_symmetric_bounded
      hsub_nonempty hsub_closed hsub_convex hsub_bddBelow hsub_bddAbove
      (fun ha ↦ subdifferential_zero_neg_mem_of_even (φ := φ) heven ha)

end ScalarAndRadialSubdifferential

section RadialSubdifferential

open scoped Pointwise

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (φ : ℝ → ℝ)

/-- Helper for Example 16 73: for a nonzero base point, lying on the same ray is equivalent to
being a nonnegative multiple of the normalized direction. -/
private lemma sameRay_iff_eq_nonneg_smul_inv_norm_of_ne {x u : H} (hx : x ≠ 0) :
    SameRay ℝ x u ↔ ∃ a : ℝ, 0 ≤ a ∧ u = a • (‖x‖⁻¹ • x) := by
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm_dir : SameRay ℝ x (‖x‖⁻¹ • x) :=
    SameRay.sameRay_pos_smul_right x (inv_pos.mpr hx_pos)
  have hdir_ne : ‖x‖⁻¹ • x ≠ 0 := by
    intro hzero
    have hnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
      simpa using norm_smul_inv_norm hx
    have : ‖‖x‖⁻¹ • x‖ = 0 := by
      simp [hzero]
    linarith
  constructor
  · intro hxu
    -- Move the same-ray relation onto the normalized direction and read off the scalar factor.
    have hu_dir : SameRay ℝ u (‖x‖⁻¹ • x) :=
      SameRay.trans hxu.symm hnorm_dir (fun hx0 ↦ False.elim (hx hx0))
    rcases hu_dir.exists_nonneg_right hdir_ne with ⟨a, ha, hau⟩
    exact ⟨a, ha, hau⟩
  · rintro ⟨a, ha, rfl⟩
    -- Recompose the normalized direction with the nonnegative scalar.
    have hdir_u : SameRay ℝ (‖x‖⁻¹ • x) (a • (‖x‖⁻¹ • x)) :=
      SameRay.sameRay_nonneg_smul_right _ ha
    exact SameRay.trans hnorm_dir hdir_u (fun hzero ↦ False.elim (hdir_ne hzero))

/-- Helper for Example 16 73: a scalar subgradient of an even function at a positive point is
nonnegative. -/
private lemma subgradient_nonneg_of_even_at_pos
    (heven : Function.Even φ) {r a : ℝ} (hr : 0 < r)
    (ha : a ∈ (∂ φ.toEReal) r) :
    0 ≤ a := by
  have htest := (mem_subdifferential_iff (f := φ.toEReal) r a).1 ha (-r)
  have htestE :
      (((inner ℝ (-r - r) a) + φ r : ℝ) : EReal) ≤ ((φ (-r) : ℝ) : EReal) := by
    -- First compress the `EReal` sum back to a single real-valued inequality.
    simpa [Function.toEReal_apply, EReal.coe_add] using htest
  have htest_real' : inner ℝ (-r - r) a + φ r ≤ φ (-r) :=
    EReal.coe_le_coe_iff.mp htestE
  have htest_real : ((-2 * r) * a + φ r : ℝ) ≤ φ (-r) := by
    -- Then rewrite the real inner product on `ℝ` as ordinary multiplication.
    calc
      (-2 * r) * a + φ r = (-r - r) * a + φ r := by
        ring
      _ = inner ℝ (-r - r) a + φ r := by
        simp [real_inner_eq_mul_scalar]
      _ ≤ φ (-r) := htest_real'
  have hmul_nonpos : (-2 * r) * a ≤ 0 := by
    simpa [heven r] using sub_nonpos.mpr htest_real
  nlinarith

/-- Helper for Example 16 73: a nonnegative slope that minorizes `φ` on `ℝ≥0` belongs to the
scalar subdifferential at `0`, hence is bounded above by the interval radius from clause `(1)`. -/
private lemma nonneg_affine_minorant_slope_le_interval_radius
    {ρ : NNReal} (hρ : (∂ φ.toEReal) 0 = Set.Icc (-(ρ : ℝ)) (ρ : ℝ))
    {a : ℝ} (ha_nonneg : 0 ≤ a)
    (hminor : ∀ t : ℝ, 0 ≤ t → t * a + φ 0 ≤ φ t) :
    a ≤ (ρ : ℝ) := by
  have hzero_mem : (0 : ℝ) ∈ (∂ φ.toEReal) 0 := by
    -- The interval description from clause `(1)` contains the origin.
    rw [hρ]
    simp
  have hzero_subgrad := (mem_subdifferential_iff (f := φ.toEReal) 0 0).1 hzero_mem
  have hphi_zero_le : ∀ t : ℝ, φ 0 ≤ φ t := by
    intro t
    -- The zero subgradient provides the global lower bound `φ 0 ≤ φ t`.
    have hzero0 :
        (inner ℝ (t - 0) (0 : ℝ) : EReal) + (φ.toEReal 0 : EReal) ≤ (φ.toEReal t : EReal) :=
      hzero_subgrad t
    have hzeroE :
        (φ.toEReal 0 : EReal) ≤ (φ.toEReal t : EReal) := by
      simpa [EReal.coe_add, sub_zero, real_inner_eq_mul_scalar] using hzero0
    have hzeroE' : ((φ 0 : ℝ) : EReal) ≤ ((φ t : ℝ) : EReal) := by
      simpa [Function.toEReal_apply] using hzeroE
    exact EReal.coe_le_coe_iff.mp hzeroE'
  have ha_mem : a ∈ (∂ φ.toEReal) 0 := by
    -- Extend the assumed half-line minorant to all real `t`.
    rw [mem_subdifferential_iff]
    intro t
    have hreal : t * a + φ 0 ≤ φ t := by
      by_cases ht : 0 ≤ t
      · exact hminor t ht
      · have hta_nonpos : t * a ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) ha_nonneg
        have hta_le : t * a + φ 0 ≤ φ 0 := by
          linarith
        exact le_trans hta_le (hphi_zero_le t)
    -- Repackage the real inequality into the `EReal` subgradient owner.
    exact EReal.coe_le_coe_iff.mpr <|
      by
        simpa [Function.toEReal_apply, EReal.coe_add, sub_zero, real_inner_eq_mul_scalar] using
          hreal
  have ha_interval : a ∈ Set.Icc (-(ρ : ℝ)) (ρ : ℝ) := by
    -- Once `a` is a scalar subgradient at `0`, the interval description bounds it by `ρ`.
    simpa [hρ] using ha_mem
  exact ha_interval.2

/-- Helper for Example 16 73: origin radial subgradient membership is the corresponding real-valued
affine minorant inequality. -/
private lemma mem_subdifferential_comp_norm_zero_iff_real (u : H) :
    u ∈ (∂ (fun y : H ↦ φ ‖y‖).toEReal) 0 ↔
      ∀ y : H, inner ℝ y u + φ 0 ≤ φ ‖y‖ := by
  rw [ERealFunction.mem_subdifferential_iff]
  constructor
  · intro hu y
    -- At the origin every term is real-valued, so the owner inequality descends to `ℝ`.
    have hE :
        (⟪y - 0, u⟫_ℝ : EReal) + ((fun z : H ↦ φ ‖z‖).toEReal 0 : EReal) ≤
          ((fun z : H ↦ φ ‖z‖).toEReal y : EReal) :=
      hu y
    have hE' : (((inner ℝ y u + φ 0 : ℝ) : EReal)) ≤ ((φ ‖y‖ : ℝ) : EReal) := by
      simpa [Function.toEReal_apply, EReal.coe_add, sub_zero, norm_zero] using hE
    exact EReal.coe_le_coe_iff.mp hE'
  · intro hu y
    -- Conversely, lift the real affine minorant inequality back to the `EReal` owner.
    have hE' : (((inner ℝ y u + φ 0 : ℝ) : EReal)) ≤ ((φ ‖y‖ : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (hu y)
    have hE :
        (⟪y - 0, u⟫_ℝ : EReal) + ((fun z : H ↦ φ ‖z‖).toEReal 0 : EReal) ≤
          ((fun z : H ↦ φ ‖z‖).toEReal y : EReal) := by
      simpa [Function.toEReal_apply, EReal.coe_add, sub_zero, norm_zero] using hE'
    exact hE

/-- Helper for Example 16 73: at the origin, radial subgradient membership is exactly the norm
bound dictated by the scalar interval description from clause `(1)`. -/
private lemma mem_subdifferential_comp_norm_zero_iff_norm_le_radius
    {ρ : NNReal} (hρ : (∂ φ.toEReal) 0 = Set.Icc (-(ρ : ℝ)) (ρ : ℝ)) (u : H) :
    u ∈ (∂ (fun y : H ↦ φ ‖y‖).toEReal) 0 ↔ ‖u‖ ≤ (ρ : ℝ) := by
  rw [mem_subdifferential_comp_norm_zero_iff_real (φ := φ) u]
  constructor
  · intro hu
    by_cases hu0 : u = 0
    · -- The zero vector lies in every closed ball of nonnegative radius.
      simp [hu0]
    · let v : H := ‖u‖⁻¹ • u
      have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
      have hv_norm : ‖v‖ = 1 := by
        -- Normalize `u` to a unit direction for the ray test.
        dsimp [v]
        simpa using norm_smul_inv_norm hu0
      have huv : inner ℝ v u = ‖u‖ := by
        -- The normalized direction extracts the slope `‖u‖`.
        dsimp [v]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp [hu_norm_ne]
      have hminor : ∀ t : ℝ, 0 ≤ t → t * ‖u‖ + φ 0 ≤ φ t := by
        intro t ht
        have htest := hu (t • v)
        have hnorm : ‖t • v‖ = t := by
          rw [norm_smul, Real.norm_of_nonneg ht, hv_norm, mul_one]
        -- Testing on the ray `t • v` turns the vector inequality into the scalar half-line
        -- minorant with slope `‖u‖`.
        simpa [real_inner_smul_left, huv, hnorm] using htest
      exact
        nonneg_affine_minorant_slope_le_interval_radius
          (φ := φ) hρ (norm_nonneg u) hminor
  · intro hu_norm
    have hu_scalar_mem : ‖u‖ ∈ (∂ φ.toEReal) 0 := by
      -- The interval description places the nonnegative scalar `‖u‖` in the scalar
      -- subdifferential at `0`.
      rw [hρ]
      refine ⟨?_, hu_norm⟩
      have hρ_nonneg : 0 ≤ (ρ : ℝ) := ρ.2
      exact by linarith [norm_nonneg u, hρ_nonneg]
    have hu_scalar := (mem_subdifferential_iff (f := φ.toEReal) 0 ‖u‖).1 hu_scalar_mem
    intro y
    have hscalar : ‖y‖ * ‖u‖ + φ 0 ≤ φ ‖y‖ := by
      -- Apply the scalar subgradient inequality at `t = ‖y‖`.
      exact EReal.coe_le_coe_iff.mp <|
        by
          simpa [EReal.coe_add, sub_zero, real_inner_eq_mul_scalar] using hu_scalar ‖y‖
    -- Cauchy--Schwarz upgrades the scalar inequality to the vector inequality at the origin.
    linarith [real_inner_le_norm y u, hscalar]

/-- Helper for Example 16 73: on `ℝ`, equality in Cauchy--Schwarz is exactly the same-ray
condition. -/
private lemma real_inner_eq_norm_mul_iff_same_ray (x u : H) :
    inner ℝ x u = ‖x‖ * ‖u‖ ↔ SameRay ℝ x u := by
  simpa [sameRay_iff_norm_smul_eq, eq_comm] using
    (inner_eq_norm_mul_iff_real (x := x) (y := u))

/-- Helper for Example 16 73: for a nonempty effective domain, subgradient membership is
equivalent to Fenchel--Young equality. -/
private lemma mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) (x u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u = ((inner ℝ x u : ℝ) : EReal) := by
  have hproper : IsProper f.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (f y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  constructor
  · intro hu
    have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    have hx : x ∈ effectiveDomain f :=
      subdifferential_domain_subset_effectiveDomain f hdom hx_dom
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hu_halfspace :
        ∀ y ∈ effectiveDomain f,
          ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hu
      exact hu
    have hdefect_le :
        ∀ y : H, ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x := by
      intro y
      by_cases hy : y ∈ effectiveDomain f
      · have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
        have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
        have hinner_sub :
            ⟪y - x, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ := by
          simp [sub_eq_add_neg, inner_add_left]
        have hdefect_real :
            ⟪y, u⟫_ℝ - (f y : EReal).toReal ≤ ⟪x, u⟫_ℝ - (f x : EReal).toReal := by
          linarith [hu_halfspace y hy, hinner_sub]
        have hy_toReal :
            ((((f y : EReal).toReal : ℝ) : EReal)) = (f y : EReal) :=
          EReal.coe_toReal hy_top hy_bot
        have hx_toReal :
            ((((f x : EReal).toReal : ℝ) : EReal)) = (f x : EReal) :=
          EReal.coe_toReal hfx_top hfx_bot
        calc
          ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y =
              (((⟪y, u⟫_ℝ - (f y : EReal).toReal : ℝ) : EReal)) := by
                rw [← hy_toReal, ← EReal.coe_sub]
                simp
          _ ≤ (((⟪x, u⟫_ℝ - (f x : EReal).toReal : ℝ) : EReal)) :=
            EReal.coe_le_coe_iff.mpr hdefect_real
          _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x := by
                rw [← hx_toReal, ← EReal.coe_sub]
                simp
      · have hy_top : (f y : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
        rw [hy_top, EReal.sub_top]
        exact bot_le
    have hconj_le : f.asEReal∗ u ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x := by
      rw [conjugate_apply]
      exact iSup_le hdefect_le
    have hsum_le : (f x : EReal) + f.asEReal∗ u ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      simpa [add_comm] using
        (EReal.le_sub_iff_add_le (Or.inl hfx_bot) (Or.inl hfx_top)).1 hconj_le
    have hfy_le :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + f.asEReal∗ u := by
      simpa using fenchel_young_inequality hproper x u
    exact le_antisymm hsum_le hfy_le
  · intro hEq
    have hconj_bot : f.asEReal∗ u ≠ ⊥ := conjugate_ne_bot_of_isProper hproper u
    have hfx_top : (f x : EReal) ≠ ⊤ := by
      intro hfx_top
      have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
        rw [hfx_top]
        exact EReal.top_add_of_ne_bot hconj_bot
      exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)
    have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hconj_top : f.asEReal∗ u ≠ ⊤ := by
      intro hconj_top
      have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
        rw [hconj_top]
        exact EReal.add_top_of_ne_bot hfx_bot
      exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)
    have hx : x ∈ effectiveDomain f := by
      rw [mem_effectiveDomain_iff]
      exact lt_of_le_of_ne le_top hfx_top
    have hEq_real : (f x : EReal).toReal + (f.asEReal∗ u).toReal = ⟪x, u⟫_ℝ := by
      have hx_toReal :
          ((((f x : EReal).toReal : ℝ) : EReal)) = (f x : EReal) :=
        EReal.coe_toReal hfx_top hfx_bot
      have hconj_toReal :
          ((((f.asEReal∗ u).toReal : ℝ) : EReal)) = f.asEReal∗ u :=
        EReal.coe_toReal hconj_top hconj_bot
      apply EReal.coe_eq_coe_iff.mp
      calc
        (((f x : EReal).toReal + (f.asEReal∗ u).toReal : ℝ) : EReal) =
            ((((f x : EReal).toReal : ℝ) : EReal)) +
              ((((f.asEReal∗ u).toReal : ℝ) : EReal)) := by
                rw [EReal.coe_add]
        _ = (f x : EReal) + f.asEReal∗ u := by
              rw [hx_toReal, hconj_toReal]
        _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hEq
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂]
    intro y hy
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
    have hfy :
        ((⟪y, u⟫_ℝ : ℝ) : EReal) ≤ (f y : EReal) + f.asEReal∗ u := by
      simpa using fenchel_young_inequality hproper y u
    have hfy_real : ⟪y, u⟫_ℝ ≤ (f y : EReal).toReal + (f.asEReal∗ u).toReal := by
      have hy_toReal :
          ((((f y : EReal).toReal : ℝ) : EReal)) = (f y : EReal) :=
        EReal.coe_toReal hy_top hy_bot
      have hconj_toReal :
          ((((f.asEReal∗ u).toReal : ℝ) : EReal)) = f.asEReal∗ u :=
        EReal.coe_toReal hconj_top hconj_bot
      apply EReal.coe_le_coe_iff.mp
      calc
        ((⟪y, u⟫_ℝ : ℝ) : EReal) ≤ (f y : EReal) + f.asEReal∗ u := hfy
        _ = ((((f y : EReal).toReal : ℝ) : EReal)) +
              ((((f.asEReal∗ u).toReal : ℝ) : EReal)) := by
                rw [← hy_toReal, ← hconj_toReal]
                simp
        _ = (((f y : EReal).toReal + (f.asEReal∗ u).toReal : ℝ) : EReal) := by
              rw [EReal.coe_add]
    have hinner_sub :
        ⟪y - x, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ := by
      simp [sub_eq_add_neg, inner_add_left]
    have hhalfspace :
        ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      linarith [hfy_real, hEq_real]
    simpa [hinner_sub] using hhalfspace

/-- Helper for Example 16 73: scalar Fenchel--Young equality for `φ.toEReal` is exactly scalar
subdifferential membership. -/
private lemma scalar_fenchel_young_eq_iff_mem_subdifferential (a b : ℝ) :
    (φ.toEReal a : EReal) + φ.toEReal.asEReal∗ b = (((a * b : ℝ) : EReal)) ↔
      b ∈ (∂ φ.toEReal) a := by
  have hdom : (effectiveDomain φ.toEReal).Nonempty := by
    refine ⟨0, ?_⟩
    simp [Function.effectiveDomain_toEReal]
  constructor
  · intro hEq
    have hEq_inner :
        (φ.toEReal a : EReal) + φ.toEReal.asEReal∗ b = ((inner ℝ a b : ℝ) : EReal) := by
      simpa [real_inner_eq_mul_scalar] using hEq
    exact
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        (f := φ.toEReal) hdom a b).2 hEq_inner
  · intro hb
    have hEq_inner :=
      (mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
        (f := φ.toEReal) hdom a b).1 hb
    simpa [real_inner_eq_mul_scalar] using hEq_inner

/-- Helper for Example 16 73: for radial `toEReal` data, subgradient membership is equivalent to
scalar subgradient membership at the norm together with a same-ray condition. -/
private lemma mem_subdifferential_comp_norm_toEReal_iff_norm_mem_subdifferential_and_same_ray
    (hφ_gamma : φ.toEReal ∈ Γ₀(ℝ)) (htoEven : Function.Even φ.toEReal) (x u : H) :
    u ∈ (∂ (fun y : H ↦ φ ‖y‖).toEReal) x ↔
      ‖u‖ ∈ (∂ φ.toEReal) ‖x‖ ∧ SameRay ℝ x u := by
  have hdom_radial : (effectiveDomain (fun y : H ↦ φ ‖y‖).toEReal).Nonempty := by
    refine ⟨0, ?_⟩
    simp [Function.effectiveDomain_toEReal]
  have hconj_eval :
      (fun y : H ↦ φ ‖y‖).toEReal.asEReal∗ u = φ.toEReal.asEReal∗ ‖u‖ := by
    have hconj_fun :
        (fun y : H ↦ φ ‖y‖).toEReal.asEReal∗ = φ.toEReal.asEReal∗ ∘ (norm : H → ℝ) :=
      conjugate_comp_norm_eq_comp_norm_conjugate_of_even (H := H) φ.toEReal htoEven
    have hconj_point := congrArg (fun g : H → EReal ↦ g u) hconj_fun
    simpa [Function.comp] using hconj_point
  have hradial_fy :
      u ∈ (∂ (fun y : H ↦ φ ‖y‖).toEReal) x ↔
        (φ ‖x‖ : EReal) + φ.toEReal.asEReal∗ ‖u‖ = ((inner ℝ x u : ℝ) : EReal) := by
    rw [mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
      (f := (fun y : H ↦ φ ‖y‖).toEReal) hdom_radial x u]
    rw [hconj_eval]
    simp [Function.toEReal_apply]
  refine hradial_fy.trans ?_
  constructor
  · intro hEq
    have hscalar_le :
        (((‖x‖ * ‖u‖ : ℝ) : EReal)) ≤ (φ ‖x‖ : EReal) + φ.toEReal.asEReal∗ ‖u‖ := by
      calc
        (((‖x‖ * ‖u‖ : ℝ) : EReal)) = ((⟪‖x‖, ‖u‖⟫_ℝ : ℝ) : EReal) := by
          simp [real_inner_eq_mul_scalar]
        _ ≤ (φ ‖x‖ : EReal) + φ.toEReal.asEReal∗ ‖u‖ := by
          simpa using
            (fenchel_young_inequality
              (f := φ.toEReal.asEReal) (isProper_of_mem_gammaZero hφ_gamma) ‖x‖ ‖u‖)
    have hinner_le :
        (((⟪x, u⟫_ℝ : ℝ) : EReal)) ≤ (((‖x‖ * ‖u‖ : ℝ) : EReal)) :=
      EReal.coe_le_coe_iff.mpr (real_inner_le_norm x u)
    have hscalar_eq :
        (φ ‖x‖ : EReal) + φ.toEReal.asEReal∗ ‖u‖ = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
      have hcontact_le :
          (φ ‖x‖ : EReal) + φ.toEReal.asEReal∗ ‖u‖ ≤ (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
        rw [hEq]
        exact hinner_le
      exact le_antisymm hcontact_le hscalar_le
    have hscalar_subgradient : ‖u‖ ∈ (∂ φ.toEReal) ‖x‖ := by
      exact
        (scalar_fenchel_young_eq_iff_mem_subdifferential
          (φ := φ) ‖x‖ ‖u‖).1 hscalar_eq
    have hinner_eq :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) = (((‖x‖ * ‖u‖ : ℝ) : EReal)) :=
      hEq.symm.trans hscalar_eq
    have hray : SameRay ℝ x u := by
      exact
        (real_inner_eq_norm_mul_iff_same_ray (x := x) (u := u)).1
          (EReal.coe_eq_coe_iff.mp hinner_eq)
    exact ⟨hscalar_subgradient, hray⟩
  · rintro ⟨hu, hray⟩
    have hscalar_eq :
        (φ ‖x‖ : EReal) + φ.toEReal.asEReal∗ ‖u‖ = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
      exact
        (scalar_fenchel_young_eq_iff_mem_subdifferential
          (φ := φ) ‖x‖ ‖u‖).2 hu
    have hinner_eq :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := by
      exact EReal.coe_eq_coe_iff.mpr <|
        (real_inner_eq_norm_mul_iff_same_ray (x := x) (u := u)).2 hray
    calc
      (φ ‖x‖ : EReal) + φ.toEReal.asEReal∗ ‖u‖ = (((‖x‖ * ‖u‖ : ℝ) : EReal)) := hscalar_eq
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hinner_eq.symm

-- Proof sketch: apply the owner membership theorem of Example 16.31 to `φ.toEReal`, then rewrite
-- `SameRay ℝ x u` with `x ≠ 0` as membership in the pointwise scalar action of the singleton
-- `{‖x‖⁻¹ • x}`. This eliminates the local image wrapper and exposes the canonical set action.
/-- Example 16 73 (2): for every nonzero `x`, the subdifferential of the radial function
`y ↦ φ ‖y‖` at `x` is the scalar subdifferential at `‖x‖` acting on the normalized ray through
`x`. -/
theorem subdifferential_comp_norm_eq_scaled_ray_image_of_ne
    (hconv : _root_.ConvexOn ℝ Set.univ φ) (heven : Function.Even φ)
    (x : H) (hx : x ≠ 0) :
    (∂ (fun y : H ↦ φ ‖y‖).toEReal) x =
      ((∂ φ.toEReal) ‖x‖) • ({‖x‖⁻¹ • x} : Set H) := by
  have hcont : Continuous φ := continuous_of_convexOn_univ φ hconv
  have hφ_gamma :
      φ.toEReal ∈ Γ₀(ℝ) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ (φ := φ) hcont hconv
  have htoEven : Function.Even φ.toEReal := by
    intro t
    apply Subtype.ext
    simp [Function.toEReal_apply, heven t]
  ext u
  rw [mem_subdifferential_comp_norm_toEReal_iff_norm_mem_subdifferential_and_same_ray
    (H := H) (φ := φ) hφ_gamma htoEven x u]
  constructor
  · rintro ⟨hu_norm, hu_ray⟩
    rcases (sameRay_iff_eq_nonneg_smul_inv_norm_of_ne (x := x) (u := u) hx).1 hu_ray with
      ⟨a, ha_nonneg, rfl⟩
    have ha_mem : a ∈ (∂ φ.toEReal) ‖x‖ := by
      have hnorm_u : ‖a • (‖x‖⁻¹ • x)‖ = a := by
        have hdir_norm : ‖‖x‖⁻¹ • x‖ = 1 := by
          simpa using norm_smul_inv_norm hx
        calc
          ‖a • (‖x‖⁻¹ • x)‖ = a * ‖‖x‖⁻¹ • x‖ := by
            rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
          _ = a := by simp [hdir_norm]
      -- The radial owner theorem records the scalar factor through the norm of `u`.
      simpa [hnorm_u] using hu_norm
    exact Set.mem_smul.mpr ⟨a, ha_mem, ‖x‖⁻¹ • x, by simp, rfl⟩
  · intro hu
    rcases Set.mem_smul.mp hu with ⟨a, ha_mem, v, hv, rfl⟩
    have hv_eq : v = ‖x‖⁻¹ • x := by
      simpa using hv
    subst hv_eq
    have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have ha_nonneg : 0 ≤ a :=
      subgradient_nonneg_of_even_at_pos (φ := φ) heven hx_norm_pos ha_mem
    have hnorm_u : ‖a • (‖x‖⁻¹ • x)‖ = a := by
      have hdir_norm : ‖‖x‖⁻¹ • x‖ = 1 := by
        simpa using norm_smul_inv_norm hx
      calc
        ‖a • (‖x‖⁻¹ • x)‖ = a * ‖‖x‖⁻¹ • x‖ := by
          rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
        _ = a := by simp [hdir_norm]
    refine ⟨?_, ?_⟩
    · -- Rewrite the scalar factor back as the norm of the radial point.
      simpa [hnorm_u] using ha_mem
    · -- Package the explicit nonnegative multiple as the required same-ray relation.
      exact
        (sameRay_iff_eq_nonneg_smul_inv_norm_of_ne
          (x := x) (u := a • (‖x‖⁻¹ • x)) hx).2 ⟨a, ha_nonneg, rfl⟩

-- Proof sketch: combine the explicit scalar interval input `hρ` with the convex radial
-- subdifferential owner at `0`. Example 16.32 identifies the norm subdifferential with the closed
-- unit ball, so scaling by the scalar interval `[-ρ, ρ]` yields `B(0; ρ)`.
/-- Example 16 73 (3): if `ρ` realizes the symmetric scalar subdifferential description from
clause `(1)`, then the subdifferential of `y ↦ φ ‖y‖` at `0` is the closed ball `B(0; ρ)`. -/
theorem subdifferential_comp_norm_zero_eq_closedBall_of_subdifferential_zero_eq_interval
    (hconv : _root_.ConvexOn ℝ Set.univ φ)
    {ρ : NNReal} (hρ : (∂ φ.toEReal) 0 = Set.Icc (-(ρ : ℝ)) (ρ : ℝ)) :
    (∂ (fun y : H ↦ φ ‖y‖).toEReal) 0 =
      Metric.closedBall (0 : H) (ρ : ℝ) := by
  -- Route correction: avoid the broken `Example_16_31` owner import and prove the origin branch
  -- directly by identifying radial subgradient membership with the norm bound `‖u‖ ≤ ρ`.
  let _ : Continuous φ := continuous_of_convexOn_univ φ hconv
  ext u
  rw [mem_subdifferential_comp_norm_zero_iff_norm_le_radius (φ := φ) hρ]
  simp [Metric.mem_closedBall, dist_eq_norm]

end RadialSubdifferential

end ERealFunction
