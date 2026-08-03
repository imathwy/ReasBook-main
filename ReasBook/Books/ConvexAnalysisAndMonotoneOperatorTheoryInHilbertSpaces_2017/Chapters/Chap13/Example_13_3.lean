import Mathlib
import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap06.Definition_6_22
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Example_7_15
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set
open Metric

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 13 3: positive scaling preserves membership in a cone. -/
lemma smul_mem_of_isCone {K : Set H} (hK_cone : IsCone K) {x : H} (hx : x ∈ K) {t : ℝ}
    (ht : 0 < t) :
    t • x ∈ K := by
  -- Rewrite the cone predicate as positive-scalar invariance and use the displayed witness.
  rw [isCone_iff] at hK_cone
  have htx : t • x ∈ (Set.Ioi (0 : ℝ) : Set ℝ) • K :=
    Set.mem_smul.mpr ⟨t, ht, x, hx, rfl⟩
  exact hK_cone.symm ▸ htx

/-- Helper for Example 13 3: the conjugate of an indicator is the supremum of the inner products
over the underlying set. -/
lemma conjugate_indicator_apply_eq_sSup_inner_image
    (C : Set H) (u : H) :
    ((ι[C]).asEReal)∗ u = sSup ((fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) '' C) := by
  -- Expand the conjugate, then split the indicator term according to membership in `C`.
  rw [conjugate_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    by_cases hx : x ∈ C
    · simpa [indicator_apply, hx] using
        (le_sSup (Set.mem_image_of_mem (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal)) hx))
    · simp [indicator_apply, hx]
  · refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    -- On `C`, the indicator term vanishes, so the corresponding affine defect is realized in the
    -- supremum defining the conjugate.
    simpa [indicator_apply, hx] using
      (le_iSup (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - ((ι[C] x : Set.Ioi (⊥ : EReal)) : EReal))
        x)

/-- Helper for Example 13 3: the normalized nonzero vector has unit norm. -/
lemma normalized_norm_eq_one {u : H} (hu : u ≠ 0) :
    ‖‖u‖⁻¹ • u‖ = 1 := by
  have hnorm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  calc
    ‖‖u‖⁻¹ • u‖ = |‖u‖⁻¹| * ‖u‖ := norm_smul _ _
    _ = ‖u‖⁻¹ * ‖u‖ := by
      rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
    _ = 1 := by simpa using inv_mul_cancel₀ hnorm_ne

/-- Helper for Example 13 3: the normalized nonzero vector lies in the closed unit ball. -/
lemma normalized_mem_closedUnitBall {u : H} (hu : u ≠ 0) :
    ‖u‖⁻¹ • u ∈ closedBall (0 : H) 1 := by
  -- Membership in the centered closed ball is exactly the unit-norm estimate.
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (normalized_norm_eq_one hu).le

/-- Helper for Example 13 3: pairing a nonzero vector with its normalization recovers its norm. -/
lemma normalized_inner_eq_norm {u : H} (hu : u ≠ 0) :
    ⟪‖u‖⁻¹ • u, u⟫_ℝ = ‖u‖ := by
  have hnorm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  calc
    ⟪‖u‖⁻¹ • u, u⟫_ℝ = ‖u‖⁻¹ * ⟪u, u⟫_ℝ := by
      rw [real_inner_smul_left]
    _ = ‖u‖⁻¹ * ‖u‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq]
    _ = ‖u‖⁻¹ * (‖u‖ * ‖u‖) := by rw [pow_two]
    _ = (‖u‖⁻¹ * ‖u‖) * ‖u‖ := by ring
    _ = ‖u‖ := by rw [inv_mul_cancel₀ hnorm_ne, one_mul]

/-- Helper for Example 13 3: along the normalized ray through a nonzero vector, the affine defect
for the norm is exactly `t * (‖u‖ - 1)`. -/
lemma normalized_ray_affine_defect_eq
    {u : H} (hu : u ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (((⟪t • (‖u‖⁻¹ • u), u⟫_ℝ : ℝ) : EReal) - (‖t • (‖u‖⁻¹ • u)‖ : EReal)) =
      ((t * (‖u‖ - 1) : ℝ) : EReal) := by
  -- Rewrite both the inner product and the norm through the normalized vector identities.
  calc
    (((⟪t • (‖u‖⁻¹ • u), u⟫_ℝ : ℝ) : EReal) - (‖t • (‖u‖⁻¹ • u)‖ : EReal)) =
        (((t * ‖u‖ : ℝ) : EReal) - ((t : ℝ) : EReal)) := by
      rw [real_inner_smul_left, normalized_inner_eq_norm hu, norm_smul,
        normalized_norm_eq_one hu, Real.norm_of_nonneg ht]
      simp
    _ = ((t * ‖u‖ - t : ℝ) : EReal) := by
      norm_num
    _ = ((t * (‖u‖ - 1) : ℝ) : EReal) := by
      congr 1
      ring

/-- Helper for Example 13 3: the support function of a nonempty cone is the indicator of its polar
cone. -/
lemma supportFunction_eq_indicator_polarCone_of_nonempty_isCone
    (K : Set H) (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) :
    σ[K] = (ι[Kᵒ⊖]).asEReal := by
  ext u
  by_cases hu : u ∈ Kᵒ⊖
  · -- On the polar cone, every inner product is nonpositive and positive scalings force the
    -- supremum back up to `0`.
    have hu_nonpos : ∀ x ∈ K, ⟪x, u⟫_ℝ ≤ 0 :=
      (Set.mem_polarCone_iff_forall_inner_nonpos).mp hu
    have hzero_indicator : ((ι[Kᵒ⊖]).asEReal) u = 0 := by
      simp [indicator_apply, hu]
    rw [supportFunction_eq_sSup_image, hzero_indicator]
    have hsSup :
        sSup ((fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) '' K) = 0 := by
      refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact (show (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ 0) by
          exact_mod_cast hu_nonpos x hx)
      · intro w hw
        rcases hK_nonempty with ⟨x₀, hx₀⟩
        cases w with
        | bot =>
            refine ⟨((⟪x₀, u⟫_ℝ : ℝ) : EReal), ?_, EReal.bot_lt_coe _⟩
            exact Set.mem_image_of_mem _ hx₀
        | top =>
            exfalso
            exact not_lt_of_ge le_top hw
        | coe r =>
            have hr : r < 0 := by
              exact_mod_cast hw
            let t : ℝ := (-r) / (|⟪x₀, u⟫_ℝ| + 1)
            have ht : 0 < t := by
              dsimp [t]
              have hneg_r : 0 < -r := by linarith
              exact div_pos hneg_r (by positivity)
            have ha_lower : -(|⟪x₀, u⟫_ℝ| + 1) < ⟪x₀, u⟫_ℝ := by
              calc
                -(|⟪x₀, u⟫_ℝ| + 1) < -|⟪x₀, u⟫_ℝ| := by linarith
                _ ≤ ⟪x₀, u⟫_ℝ := by exact neg_abs_le _
            have hmul :
                t * (-(|⟪x₀, u⟫_ℝ| + 1)) < t * ⟪x₀, u⟫_ℝ :=
              mul_lt_mul_of_pos_left ha_lower ht
            have hw_eq : t * (-(|⟪x₀, u⟫_ℝ| + 1)) = r := by
              dsimp [t]
              field_simp
            have hlt : r < t * ⟪x₀, u⟫_ℝ := by
              rw [← hw_eq]
              exact hmul
            refine ⟨((⟪t • x₀, u⟫_ℝ : ℝ) : EReal), ?_, ?_⟩
            · exact Set.mem_image_of_mem _ (smul_mem_of_isCone hK_cone hx₀ ht)
            · exact (show ((r : EReal) < (((t * ⟪x₀, u⟫_ℝ : ℝ) : EReal)) ) by
                exact_mod_cast hlt).trans_eq (by simp [real_inner_smul_left])
    exact hsSup
  · -- Off the polar cone, some inner product is positive; scaling that witness forces the support
    -- function to diverge to `⊤`.
    have htop_indicator : ((ι[Kᵒ⊖]).asEReal) u = ⊤ := by
      simp [indicator_apply, hu]
    rw [supportFunction_eq_sSup_image, htop_indicator, EReal.eq_top_iff_forall_lt]
    intro y
    have hpos_witness : ∃ x ∈ K, 0 < ⟪x, u⟫_ℝ := by
      by_contra hpos
      apply hu
      rw [Set.mem_polarCone_iff_forall_inner_nonpos]
      intro x hx
      exact le_of_not_gt fun hx_pos ↦ hpos ⟨x, hx, hx_pos⟩
    rcases hpos_witness with ⟨x₀, hx₀, hx₀_pos⟩
    let t : ℝ := |y| / ⟪x₀, u⟫_ℝ + 1
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hmul :
        t * ⟪x₀, u⟫_ℝ = |y| + ⟪x₀, u⟫_ℝ := by
      dsimp [t]
      field_simp [hx₀_pos.ne']
    have hy_lt : y < t * ⟪x₀, u⟫_ℝ := by
      rw [hmul]
      have hy_abs : y ≤ |y| := le_abs_self y
      linarith
    have himage :
        (((⟪t • x₀, u⟫_ℝ : ℝ) : EReal)) ∈
          (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) '' K :=
      Set.mem_image_of_mem _ (smul_mem_of_isCone hK_cone hx₀ ht)
    have hy_lt_ereal :
        (y : EReal) < (((⟪t • x₀, u⟫_ℝ : ℝ) : EReal)) := by
      exact (show (y : EReal) < (((t * ⟪x₀, u⟫_ℝ : ℝ) : EReal)) by
          exact_mod_cast hy_lt).trans_eq (by simp [real_inner_smul_left])
    exact lt_of_lt_of_le hy_lt_ereal (le_sSup himage)

/-- Helper for Example 13 3: the support function of the closed unit ball is the norm. -/
lemma supportFunction_closedUnitBall_eq_norm :
    σ[closedBall (0 : H) 1] = fun u : H ↦ (‖u‖ : EReal) := by
  ext u
  by_cases hu : u = 0
  · -- At the origin, the support value of any nonempty set is `0`.
    simp [hu, supportFunction_zero_eq_zero_of_nonempty]
  · -- Away from the origin, use Cauchy--Schwarz for the upper bound and the normalized vector for
    -- the matching lower bound.
    rw [supportFunction_eq_sSup_image]
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      have hx_norm : ‖x‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hinner_le : ⟪x, u⟫_ℝ ≤ ‖u‖ := by
        calc
          ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
          _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hx_norm (norm_nonneg u)
          _ = ‖u‖ := by ring
      exact (show (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (‖u‖ : EReal)) by
        exact_mod_cast hinner_le)
    · -- The normalized vector belongs to the closed unit ball and attains the support value.
      have hmem : ‖u‖⁻¹ • u ∈ closedBall (0 : H) 1 :=
        normalized_mem_closedUnitBall hu
      have hle :
          ((‖u‖ : ℝ) : EReal) ≤
            sSup ((fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) '' closedBall (0 : H) 1) :=
        by
          refine le_sSup ?_
          exact ⟨‖u‖⁻¹ • u, hmem, by simp [normalized_inner_eq_norm hu]⟩
      simpa [normalized_inner_eq_norm hu] using hle

/-- Helper for Example 13 3: on the closed unit ball, the conjugate of the norm vanishes. -/
lemma conjugate_norm_eq_zero_on_closedUnitBall
    {u : H} (hu : u ∈ closedBall (0 : H) 1) :
    (fun x : H ↦ (‖x‖ : EReal))∗ u = 0 := by
  -- Bound every affine defect by `0`, then realize `0` at the origin.
  rw [conjugate_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    have hu_norm : ‖u‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu
    have hinner_le : ⟪x, u⟫_ℝ ≤ ‖x‖ := by
      calc
        ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
        _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hu_norm (norm_nonneg x)
        _ = ‖x‖ := by ring
    exact_mod_cast sub_nonpos.mpr hinner_le
  · -- The zero vector makes the affine defect equal to `0`.
    simpa using
      (le_iSup (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - ((‖x‖ : ℝ) : EReal)) (0 : H))

/-- Helper for Example 13 3: off the closed unit ball, the conjugate of the norm is `⊤`. -/
lemma conjugate_norm_eq_top_off_closedUnitBall
    {u : H} (hu : u ∉ closedBall (0 : H) 1) :
    (fun x : H ↦ (‖x‖ : EReal))∗ u = ⊤ := by
  have hu_ne : u ≠ 0 := by
    intro hu0
    apply hu
    simp [hu0, Metric.mem_closedBall]
  have hgap : 0 < ‖u‖ - 1 := by
    have hu_norm : ¬ ‖u‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu
    linarith
  -- Test the conjugate along the normalized ray through `u`.
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro y
  let t : ℝ := |y| / (‖u‖ - 1) + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hmul :
      t * (‖u‖ - 1) = |y| + (‖u‖ - 1) := by
    dsimp [t]
    field_simp [hgap.ne']
  have hy_lt : y < t * (‖u‖ - 1) := by
    rw [hmul]
    have hy_abs : y ≤ |y| := le_abs_self y
    linarith
  calc
    (y : EReal) < ((t * (‖u‖ - 1) : ℝ) : EReal) := by
      exact_mod_cast hy_lt
    _ = (((⟪t • (‖u‖⁻¹ • u), u⟫_ℝ : ℝ) : EReal) - (‖t • (‖u‖⁻¹ • u)‖ : EReal)) := by
      symm
      exact normalized_ray_affine_defect_eq hu_ne ht.le
    _ ≤ ⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - (‖x‖ : EReal) := by
      exact le_iSup (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - (‖x‖ : EReal))
        (t • (‖u‖⁻¹ • u))

-- Proof sketch: expand `conjugate` for the complement indicator of `C`. On `C` the indicator
-- term vanishes, and outside `C` it contributes `⊤`, so only points of `C` survive in the
-- defining supremum; what remains is exactly the support function `σ[C]`.
/-- Example 13 3 (1): clause (i). The conjugate of the indicator `ι[C]` is the support
function `σ[C]`. -/
theorem conjugate_indicator_eq_supportFunction
    (C : Set H) :
    ((ι[C]).asEReal)∗ = σ[C] := by
  ext u
  -- Compute both sides as the same supremum over the inner-product image of `C`.
  simpa [supportFunction_eq_sSup_image] using conjugate_indicator_apply_eq_sSup_inner_image C u

-- Proof sketch: combine clause (i) with the cone-specific identity that the support function of a
-- nonempty cone is the indicator of its polar cone.
/-- Example 13 3 (2): clause (ii). If `K` is a nonempty cone, then the conjugate of `ι[K]` is the
indicator `ι[Kᵒ⊖]`. -/
theorem conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone
    (K : Set H) (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) :
    ((ι[K]).asEReal)∗ = (ι[Kᵒ⊖]).asEReal := by
  -- Clause (i) identifies the conjugate with the support function, and the cone geometry turns
  -- that support function into the indicator of the polar cone.
  rw [conjugate_indicator_eq_supportFunction]
  exact supportFunction_eq_indicator_polarCone_of_nonempty_isCone K hK_nonempty hK_cone

-- Proof sketch: apply clause (ii) to the cone underlying the submodule `V`, then identify the
-- polar cone of a linear subspace with its orthogonal complement.
/-- Example 13 3 (3): clause (iii). If `V` is a linear subspace, then the conjugate of `ι[V]` is
the indicator `ι[Vᗮ]`. -/
theorem conjugate_indicator_submodule_eq_indicator_orthogonal
    (V : Submodule ℝ H) :
    ((ι[(V : Set H)]).asEReal)∗ = (ι[(Vᗮ : Set H)]).asEReal := by
  -- Specialize clause (ii) to the cone coming from the submodule and rewrite its polar cone as
  -- the orthogonal complement.
  have hV_nonempty : (V : Set H).Nonempty := ⟨0, V.zero_mem⟩
  rw [conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone
    (K := (V : Set H)) hV_nonempty (Set.submodule_isCone V)]
  exact congrArg (fun S : Set H ↦ (ι[S]).asEReal)
    (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule V).2

-- Proof sketch: use clause (i) for the closed unit ball and identify its support function with
-- the norm via Cauchy--Schwarz and the extremal choice of the normalized vector.
/-- Example 13 3 (4): clause (iv). The conjugate of the indicator `ι[B(0;1)]` is the norm. -/
theorem conjugate_indicator_closedUnitBall_eq_norm :
    ((ι[closedBall (0 : H) 1]).asEReal)∗ =
      fun u : H ↦ (‖u‖ : EReal) := by
  -- Combine clause (i) with the explicit support-function computation for the closed unit ball.
  rw [conjugate_indicator_eq_supportFunction]
  exact supportFunction_closedUnitBall_eq_norm

-- Proof sketch: compute the conjugate of the norm by splitting on whether `‖u‖ ≤ 1`; the
-- Cauchy--Schwarz inequality gives the finite value `0` on the closed unit ball, while testing on
-- rays `x = λu` makes the defining supremum diverge to `⊤` when `‖u‖ > 1`.
/-- Example 13 3 (5): clause (v). The conjugate of the norm is the indicator `ι[B(0;1)]`. -/
theorem conjugate_norm_eq_indicator_closedUnitBall :
    (fun x : H ↦ (‖x‖ : EReal))∗ =
      (ι[closedBall (0 : H) 1]).asEReal := by
  ext u
  by_cases hu : u ∈ closedBall (0 : H) 1
  · -- Inside the closed unit ball, the conjugate value is `0`.
    rw [conjugate_norm_eq_zero_on_closedUnitBall hu]
    simp [indicator_apply, hu]
  · -- Outside the closed unit ball, the conjugate value is `⊤`.
    rw [conjugate_norm_eq_top_off_closedUnitBall hu]
    simp [indicator_apply, hu]

end Conjugation

end ERealFunction
