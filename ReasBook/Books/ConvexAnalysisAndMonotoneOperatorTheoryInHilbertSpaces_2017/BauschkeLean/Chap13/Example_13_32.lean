import Mathlib
import BauschkeLean.Chap07.Exercise_7_9
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp
open scoped ENNReal InnerProductSpace

namespace ERealFunction

noncomputable section

/-- Helper for Example 13 32: the coordinate `ℓ^p` norm is homogeneous under real scalar
multiplication. -/
lemma lpNorm_smul
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace.lpNorm N p (a • x) = ‖a‖ * EuclideanSpace.lpNorm N p x := by
  -- Unfold the coordinate model and use the built-in `WithLp.toLp` scalar compatibility.
  simp only [EuclideanSpace.lpNorm_apply, map_smul, WithLp.toLp_smul]
  simpa using norm_smul a (WithLp.toLp p ((EuclideanSpace.equiv (Fin N) ℝ) x))

/-- Helper for Example 13 32: the coordinate `ℓ^p` norm vanishes exactly at the zero vector. -/
lemma lpNorm_eq_zero_iff
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace.lpNorm N p x = 0 ↔ x = 0 := by
  -- Transport the zero test to coordinates, where `WithLp.toLp` is injective.
  constructor
  · intro hx
    have htoLp_zero : WithLp.toLp p ((EuclideanSpace.equiv (Fin N) ℝ) x) = 0 := by
      exact norm_eq_zero.mp <| by simpa [EuclideanSpace.lpNorm_apply] using hx
    apply (EuclideanSpace.equiv (Fin N) ℝ).injective
    simpa using (WithLp.toLp_eq_zero (p := p)).1 htoLp_zero
  · intro hx
    subst hx
    simp [EuclideanSpace.lpNorm_apply]

/-- Helper for Example 13 32: every vector in the conjugate `ℓ^q` unit ball defines a support
functional bounded by the coordinate `ℓ^p` norm. -/
lemma inner_le_lpNorm_of_mem_conj_ball
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {u : EuclideanSpace ℝ (Fin N)} (hu : u ∈ Set.lpClosedUnitBall N p.conjExponent)
    (x : EuclideanSpace ℝ (Fin N)) :
    ⟪x, u⟫_ℝ ≤ EuclideanSpace.lpNorm N p x := by
  -- Rewrite the conjugate-ball membership as a polar-set statement on the primal unit ball.
  have hu_polar : u ∈ Set.polarSet (Set.lpClosedUnitBall N p) := by
    rw [Set.polarSet_lpClosedUnitBall_eq_conj_unitBall]
    exact hu
  have hu_inner :
      ∀ z ∈ Set.lpClosedUnitBall N p, ⟪z, u⟫_ℝ ≤ 1 :=
    (Set.mem_polarSet_iff_forall_inner_le_one (C := Set.lpClosedUnitBall N p) (u := u)).1 hu_polar
  by_cases hx : x = 0
  · -- The zero vector gives the trivial support inequality.
    subst hx
    simp
  · -- Normalize a nonzero vector onto the primal unit ball and rescale the polar inequality.
    let c : ℝ := (EuclideanSpace.lpNorm N p x)⁻¹
    let z : EuclideanSpace ℝ (Fin N) := c • x
    have hnorm_ne_zero : EuclideanSpace.lpNorm N p x ≠ 0 := by
      exact fun hzero ↦ hx ((lpNorm_eq_zero_iff N p x).1 hzero)
    have hnorm_nonneg : 0 ≤ EuclideanSpace.lpNorm N p x := by
      rw [EuclideanSpace.lpNorm_apply]
      exact norm_nonneg _
    have hnorm_pos : 0 < EuclideanSpace.lpNorm N p x := by
      exact lt_of_le_of_ne hnorm_nonneg (by simpa using hnorm_ne_zero.symm)
    have hc_pos : 0 < c := by
      simpa [c] using inv_pos.mpr hnorm_pos
    have hz_mem : z ∈ Set.lpClosedUnitBall N p := by
      -- The chosen scaling makes the coordinate `ℓ^p` norm equal to `1`.
      rw [Set.mem_lpClosedUnitBall_iff]
      have hscale :
          ‖c‖ * EuclideanSpace.lpNorm N p x = 1 := by
        simpa [c, EuclideanSpace.lpNorm_apply, Real.norm_eq_abs, abs_of_pos hc_pos] using
          inv_mul_cancel₀ hnorm_ne_zero
      calc
        EuclideanSpace.lpNorm N p z = EuclideanSpace.lpNorm N p (c • x) := by
          rfl
        _ = ‖c‖ * EuclideanSpace.lpNorm N p x := lpNorm_smul N p c x
        _ = 1 := hscale
        _ ≤ 1 := le_rfl
    have hz_le : ⟪z, u⟫_ℝ ≤ 1 := hu_inner z hz_mem
    have hz_le' : ⟪x, u⟫_ℝ / EuclideanSpace.lpNorm N p x ≤ 1 := by
      simpa [z, c, div_eq_mul_inv, real_inner_smul_left, mul_comm, mul_left_comm, mul_assoc]
        using hz_le
    have hmul :
        (⟪x, u⟫_ℝ / EuclideanSpace.lpNorm N p x) * EuclideanSpace.lpNorm N p x ≤
          1 * EuclideanSpace.lpNorm N p x :=
      mul_le_mul_of_nonneg_right hz_le' hnorm_nonneg
    have hmul' :
        ⟪x, u⟫_ℝ *
            ((EuclideanSpace.lpNorm N p x)⁻¹ * EuclideanSpace.lpNorm N p x) ≤
          EuclideanSpace.lpNorm N p x := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hinv : (EuclideanSpace.lpNorm N p x)⁻¹ * EuclideanSpace.lpNorm N p x = 1 := by
      exact inv_mul_cancel₀ hnorm_ne_zero
    calc
      ⟪x, u⟫_ℝ = ⟪x, u⟫_ℝ * ((EuclideanSpace.lpNorm N p x)⁻¹ * EuclideanSpace.lpNorm N p x) := by
        rw [hinv, mul_one]
      _ ≤ EuclideanSpace.lpNorm N p x := hmul'

/-- Helper for Example 13 32: on the conjugate `ℓ^q` unit ball, the Fenchel conjugate of the
coordinate `ℓ^p` norm is zero. -/
lemma conjugate_lpNorm_eq_zero_on_conj_ball
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {u : EuclideanSpace ℝ (Fin N)} (hu : u ∈ Set.lpClosedUnitBall N p.conjExponent) :
    (fun x : EuclideanSpace ℝ (Fin N) ↦ (‖x‖_[p] : EReal))∗ u = 0 := by
  -- The polar inequality bounds every affine defect by `0`, and the test point `x = 0` attains it.
  rw [conjugate_apply]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x ↦ ?_
    rw [EReal.sub_nonpos]
    exact_mod_cast inner_le_lpNorm_of_mem_conj_ball N p hu x
  · have hzero :
        (0 : EReal) ≤
          (((⟪(0 : EuclideanSpace ℝ (Fin N)), u⟫_ℝ : ℝ) : EReal) -
            ((‖(0 : EuclideanSpace ℝ (Fin N))‖_[p] : ℝ) : EReal)) := by
      simp
    exact hzero.trans <| le_iSup
      (fun x : EuclideanSpace ℝ (Fin N) ↦
        (((⟪x, u⟫_ℝ : ℝ) : EReal) - ((‖x‖_[p] : ℝ) : EReal)))
      0

/-- Helper for Example 13 32: off the conjugate `ℓ^q` unit ball, the Fenchel conjugate of the
coordinate `ℓ^p` norm diverges to `+∞` along a ray. -/
lemma conjugate_lpNorm_eq_top_off_conj_ball
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {u : EuclideanSpace ℝ (Fin N)} (hu : u ∉ Set.lpClosedUnitBall N p.conjExponent) :
    (fun x : EuclideanSpace ℝ (Fin N) ↦ (‖x‖_[p] : EReal))∗ u = ⊤ := by
  -- Convert non-membership in the conjugate ball into a violating primal unit-ball witness.
  have hu_polar : u ∉ Set.polarSet (Set.lpClosedUnitBall N p) := by
    rw [Set.polarSet_lpClosedUnitBall_eq_conj_unitBall]
    exact hu
  rw [Set.mem_polarSet_iff_forall_inner_le_one (C := Set.lpClosedUnitBall N p) (u := u)] at hu_polar
  push Not at hu_polar
  rcases hu_polar with ⟨x0, hx0_mem, hx0_gt⟩
  have hx0_norm_le : EuclideanSpace.lpNorm N p x0 ≤ 1 := by
    rw [Set.mem_lpClosedUnitBall_iff] at hx0_mem
    exact hx0_mem
  let δ : ℝ := ⟪x0, u⟫_ℝ - EuclideanSpace.lpNorm N p x0
  have hδ_pos : 0 < δ := by
    have hnorm_lt : EuclideanSpace.lpNorm N p x0 < ⟪x0, u⟫_ℝ := by
      exact lt_of_le_of_lt hx0_norm_le hx0_gt
    linarith [hnorm_lt]
  rw [conjugate_apply]
  exact (EReal.eq_top_iff_forall_lt _).2 <| fun M ↦ by
    -- Choose a positive scaling whose defect dominates the prescribed real bound `M`.
    let t : ℝ := |M| / δ + 1
    have ht_pos : 0 < t := by
      have hnonneg : 0 ≤ |M| / δ := by
        exact div_nonneg (abs_nonneg M) hδ_pos.le
      linarith
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have hδ_ne_zero : δ ≠ 0 := hδ_pos.ne'
    have htdelta : t * δ = |M| + δ := by
      calc
        t * δ = (|M| / δ + 1) * δ := by rfl
        _ = (|M| / δ) * δ + δ := by ring_nf
        _ = |M| + δ := by
          rw [div_mul_eq_mul_div, mul_comm |M| δ, mul_div_cancel_left₀ _ hδ_ne_zero]
    have hM_lt : M < t * δ := by
      calc
        M ≤ |M| := le_abs_self M
        _ < |M| + δ := lt_add_of_pos_right _ hδ_pos
        _ = t * δ := htdelta.symm
    have hdefect :
        ((((⟪t • x0, u⟫_ℝ : ℝ) : EReal) - ((‖t • x0‖_[p] : ℝ) : EReal))) =
          ((t * δ : ℝ) : EReal) := by
      -- Rewrite the affine defect on the ray `t • x0` as the positive linear expression `t * δ`.
      rw [← EReal.coe_sub]
      have hnorm_t : ‖t‖ = t := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
      calc
        ((⟪t • x0, u⟫_ℝ - ‖t • x0‖_[p] : ℝ) : EReal)
            = ((t * ⟪x0, u⟫_ℝ - ‖t • x0‖_[p] : ℝ) : EReal) := by
                rw [real_inner_smul_left]
        _ = ((t * ⟪x0, u⟫_ℝ - ‖t‖ * EuclideanSpace.lpNorm N p x0 : ℝ) : EReal) := by
              rw [lpNorm_smul N p t x0]
        _ = ((t * (⟪x0, u⟫_ℝ - EuclideanSpace.lpNorm N p x0) : ℝ) : EReal) := by
              rw [hnorm_t]
              ring_nf
        _ = ((t * δ : ℝ) : EReal) := by rfl
    have hterm_lt :
        (M : EReal) <
          ((((⟪t • x0, u⟫_ℝ : ℝ) : EReal) - ((‖t • x0‖_[p] : ℝ) : EReal))) := by
      rw [hdefect]
      exact_mod_cast hM_lt
    exact lt_of_lt_of_le hterm_lt <| le_iSup
      (fun x : EuclideanSpace ℝ (Fin N) ↦
        (((⟪x, u⟫_ℝ : ℝ) : EReal) - ((‖x‖_[p] : ℝ) : EReal)))
      (t • x0)

/-- Helper for Example 13 32: the indicator of the conjugate `ℓ^q` unit ball is `0` on the
ball itself. -/
lemma indicator_lpClosedUnitBall_conjExponent_asEReal_eq_zero
    (N : ℕ) (p : ℝ≥0∞) {u : EuclideanSpace ℝ (Fin N)}
    (hu : u ∈ Set.lpClosedUnitBall N p.conjExponent) :
    ((ι[Set.lpClosedUnitBall N p.conjExponent]).asEReal u) = 0 := by
  -- Inside the set, the textbook indicator takes the finite value `0`.
  simp [Function.asEReal_apply, indicator_apply, hu]

/-- Helper for Example 13 32: the indicator of the conjugate `ℓ^q` unit ball is `⊤` off the
ball. -/
lemma indicator_lpClosedUnitBall_conjExponent_asEReal_eq_top
    (N : ℕ) (p : ℝ≥0∞) {u : EuclideanSpace ℝ (Fin N)}
    (hu : u ∉ Set.lpClosedUnitBall N p.conjExponent) :
    ((ι[Set.lpClosedUnitBall N p.conjExponent]).asEReal u) = ⊤ := by
  -- Outside the set, the textbook indicator takes the value `⊤`.
  simp [Function.asEReal_apply, indicator_apply, hu]

-- Proof sketch: identify the support function of the `ℓ^p` unit ball with the Chapter 7 owner
-- `EuclideanSpace.lpNorm N p.conjExponent` using Hölder's inequality and the extremal vectors
-- from Exercise 7.9, then apply the norm-conjugate formula from Example 13.3 to conclude that
-- the conjugate is the indicator of the conjugate-exponent unit ball, expressed through the
-- owner `Set.lpClosedUnitBall`.
/-- Example 13 32: on `ℝ^N`, for `p ∈ [1,+∞]`, the conjugate of the coordinate `ℓ^p` norm is the
indicator of the conjugate-exponent unit ball `B_{p*}`. -/
theorem conjugate_lpNorm_eq_indicator_lpClosedUnitBall_conjExponent
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (fun x : EuclideanSpace ℝ (Fin N) ↦ (‖x‖_[p] : EReal))∗ =
      (ι[Set.lpClosedUnitBall N p.conjExponent]).asEReal := by
  ext u
  by_cases hu : u ∈ Set.lpClosedUnitBall N p.conjExponent
  · -- On the conjugate ball, the conjugate vanishes and matches the indicator value `0`.
    rw [conjugate_lpNorm_eq_zero_on_conj_ball N p hu]
    exact (indicator_lpClosedUnitBall_conjExponent_asEReal_eq_zero N p hu).symm
  · -- Outside the conjugate ball, the ray argument gives `⊤`, again matching the indicator.
    rw [conjugate_lpNorm_eq_top_off_conj_ball N p hu]
    exact (indicator_lpClosedUnitBall_conjExponent_asEReal_eq_top N p hu).symm

end

end ERealFunction
