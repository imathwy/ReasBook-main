import Mathlib
import BauschkeLean.Chap03.Corollary_3_38
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap09.Theorem_9_1
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Definition_12_5
import BauschkeLean.Chap12.Proposition_12_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section Proposition1214

variable (f g : H → Set.Ioi (⊥ : EReal))
variable (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
-- Clause (ii) is kept in the source-facing bounded-below form; the zero-slope affine-minorant
-- owner is only an internal bridge.
variable
  (hcase :
    Supercoercive f.asEReal ∨
      (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x))

omit [CompleteSpace H] in
private theorem hasContinuousAffineMinorantWithSlope_zero_of_bddBelow
    (hg_bddBelow : ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x) :
    HasContinuousAffineMinorantWithSlope g.asEReal 0 := by
  simpa [HasContinuousAffineMinorantWithSlope]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: a `Γ₀(H)` function is bounded below by a global affine
function of the norm. -/
private theorem exists_linear_lower_bound_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) :
    ∃ R C : ℝ, ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (φ x : EReal)) := by
  -- Recover the global affine minorant from one local lower bound and convexity at a finite point.
  rcases hφ.2.nonempty with ⟨p, hp⟩
  let ξ : ℝ := (φ p : EReal).toReal - 1
  have hp_top : (φ p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hp_bot : (φ p : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (φ p : EReal) from (φ p).2)
  have hξ_lt_fp : (ξ : EReal) < (φ p : EReal) := by
    rw [show (φ p : EReal) = (((φ p : EReal).toReal : ℝ) : EReal) by
      symm
      exact EReal.coe_toReal hp_top hp_bot]
    exact_mod_cast (show ξ < (φ p : EReal).toReal by
      dsimp [ξ]
      linarith)
  have hopen : IsOpen (φ.asEReal ⁻¹' Set.Ioi (ξ : EReal)) := hφ.1.isOpen_preimage (ξ : EReal)
  have hp_mem : p ∈ φ.asEReal ⁻¹' Set.Ioi (ξ : EReal) := by
    simpa [Function.asEReal] using hξ_lt_fp
  rcases Metric.isOpen_iff.mp hopen p hp_mem with ⟨r, hr_pos, hr_subset⟩
  let δ : ℝ := r / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨δ⁻¹, 1 + ‖p‖ / δ - (φ p : EReal).toReal, ?_⟩
  intro x
  by_cases hx : x ∈ effectiveDomain φ
  · have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (φ x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (φ x : EReal) from (φ x).2)
    by_cases hnear : ‖x - p‖ < δ
    · -- Near `p`, the local open lower bound already dominates the target affine function.
      have hball : x ∈ Metric.ball p r := by
        have : ‖x - p‖ < r := by
          dsimp [δ] at hnear
          linarith
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hξ_lt_fx : (ξ : EReal) < (φ x : EReal) := hr_subset hball
      have hbound_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) ≤ ξ := by
        dsimp [ξ]
        have hnonneg : 0 ≤ δ⁻¹ * ‖x‖ + ‖p‖ / δ := by
          positivity
        linarith
      have hbound_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) : ℝ) : EReal)) ≤
            (ξ : EReal) := by
        exact_mod_cast hbound_real
      exact le_trans hbound_ereal hξ_lt_fx.le
    · -- Far from `p`, move back onto the local neighborhood by convex interpolation.
      have hfar : δ ≤ ‖x - p‖ := le_of_not_gt hnear
      have hxp_pos : 0 < ‖x - p‖ := lt_of_lt_of_le hδ_pos hfar
      let t : ℝ := δ / ‖x - p‖
      let y : H := t • x + (1 - t) • p
      have ht_pos : 0 < t := by
        dsimp [t]
        exact div_pos hδ_pos hxp_pos
      have ht_le_one : t ≤ 1 := by
        dsimp [t]
        exact (div_le_iff₀ hxp_pos).2 (by simpa [one_mul] using hfar)
      have hy_sub : y - p = t • (x - p) := by
        dsimp [y]
        calc
          t • x + (1 - t) • p - p = t • x + ((1 - t) • p - p) := by abel
          _ = t • x + ((1 - t) • p - (1 : ℝ) • p) := by simp
          _ = t • x + ((1 - t - 1) • p) := by
                rw [← sub_smul]
          _ = t • x + (-t) • p := by ring_nf
          _ = t • x - t • p := by rw [sub_eq_add_neg, neg_smul]
          _ = t • (x - p) := by rw [smul_sub]
      have hy_ball : y ∈ Metric.ball p r := by
        have hnorm : ‖y - p‖ < r := by
          calc
            ‖y - p‖ = ‖t • (x - p)‖ := by rw [hy_sub]
            _ = |t| * ‖x - p‖ := norm_smul t (x - p)
            _ = t * ‖x - p‖ := by rw [abs_of_pos ht_pos]
            _ = δ := by
                  dsimp [t]
                  field_simp [hxp_pos.ne']
            _ < r := by
                  dsimp [δ]
                  linarith
        simpa [Metric.mem_ball, dist_eq_norm] using hnorm
      have hξ_lt_fy : (ξ : EReal) < (φ y : EReal) := hr_subset hy_ball
      have hconv :
          (φ y : EReal) ≤ (t : EReal) * (φ x : EReal) + ((1 - t : ℝ) : EReal) * (φ p : EReal) := by
        by_cases ht_one : t = 1
        · simp [y, ht_one]
        · have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht_one
          simpa [y] using hφ.2.ineq (x := x) hx (y := p) hp (α := t) ht_pos ht_lt_one
      have hterm1_ne_top : (t : EReal) * (φ x : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot t), Or.inl ?_, Or.inl (EReal.coe_ne_top t), Or.inr hx_top⟩
        exact_mod_cast ht_pos.le
      have hterm2_ne_top : ((1 - t : ℝ) : EReal) * (φ p : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - t)), Or.inl ?_,
          Or.inl (EReal.coe_ne_top (1 - t)), Or.inr hp_top⟩
        exact_mod_cast sub_nonneg.mpr ht_le_one
      have hright_ne_top :
          (t : EReal) * (φ x : EReal) + ((1 - t : ℝ) : EReal) * (φ p : EReal) ≠ ⊤ :=
        EReal.add_ne_top hterm1_ne_top hterm2_ne_top
      have hy_top : (φ y : EReal) ≠ ⊤ := by
        intro hy_top
        have : (⊤ : EReal) ≤
            (t : EReal) * (φ x : EReal) + ((1 - t : ℝ) : EReal) * (φ p : EReal) := by
          simpa [hy_top] using hconv
        exact hright_ne_top (top_unique this)
      have hy_bot : (φ y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (φ y : EReal) from (φ y).2)
      have hξ_lt_fy_real : ξ < (φ y : EReal).toReal := by
        rw [← EReal.coe_toReal hy_top hy_bot] at hξ_lt_fy
        exact EReal.coe_lt_coe_iff.1 hξ_lt_fy
      have hconv_real :
          (φ y : EReal).toReal ≤ t * (φ x : EReal).toReal + (1 - t) * (φ p : EReal).toReal := by
        have hconv_cast :
            (((φ y : EReal).toReal : ℝ) : EReal) ≤
              (t : EReal) * (((φ x : EReal).toReal : ℝ) : EReal) +
                ((1 - t : ℝ) : EReal) * (((φ p : EReal).toReal : ℝ) : EReal) := by
          simpa [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot,
            EReal.coe_toReal hp_top hp_bot] using hconv
        exact EReal.coe_le_coe_iff.1 (by
          simpa [EReal.coe_mul, EReal.coe_add] using hconv_cast)
      have hfx_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) < (φ x : EReal).toReal := by
        have hdist : ‖x - p‖ ≤ ‖x‖ + ‖p‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x p
        have hmain : (φ p : EReal).toReal - 1 / t < (φ x : EReal).toReal := by
          have haux : ξ < t * (φ x : EReal).toReal + (1 - t) * (φ p : EReal).toReal :=
            lt_of_lt_of_le hξ_lt_fy_real hconv_real
          have hsub : -1 < t * ((φ x : EReal).toReal - (φ p : EReal).toReal) := by
            dsimp [ξ] at haux
            linarith
          have hdiv : -1 / t < (φ x : EReal).toReal - (φ p : EReal).toReal := by
            exact (div_lt_iff₀ ht_pos).2 (by simpa [mul_comm] using hsub)
          have hmain_shift :
              (φ p : EReal).toReal + (-1 / t) <
                (φ p : EReal).toReal + ((φ x : EReal).toReal - (φ p : EReal).toReal) :=
            add_lt_add_right hdiv (φ p : EReal).toReal
          calc
            (φ p : EReal).toReal - 1 / t = (φ p : EReal).toReal + (-1 / t) := by ring
            _ < (φ p : EReal).toReal + ((φ x : EReal).toReal - (φ p : EReal).toReal) :=
              hmain_shift
            _ = (φ x : EReal).toReal := by ring
        have ht_inv : 1 / t = ‖x - p‖ / δ := by
          dsimp [t]
          field_simp [hxp_pos.ne', hδ_pos.ne']
        rw [ht_inv] at hmain
        have hratio : ‖x - p‖ / δ ≤ ‖x‖ / δ + ‖p‖ / δ := by
          have := div_le_div_of_nonneg_right hdist hδ_pos.le
          simpa [add_div] using this
        have hleft_le :
            (φ p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) ≤
              (φ p : EReal).toReal - ‖x - p‖ / δ := by
          linarith
        have hfinal :
            (φ p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) < (φ x : EReal).toReal :=
          lt_of_le_of_lt hleft_le hmain
        have hrewrite :
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) =
              (φ p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [hrewrite]
        exact hfinal
      have hfx_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) : ℝ) : EReal)) <
            (φ x : EReal) := by
        rw [show (φ x : EReal) = (((φ x : EReal).toReal : ℝ) : EReal) by
          symm
          exact EReal.coe_toReal hx_top hx_bot]
        exact_mod_cast hfx_real
      exact hfx_ereal.le
  · have hx_top : (φ x : EReal) = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hxtop
      exact hx (mem_effectiveDomain_iff.mpr hxtop)
    simp [hx_top]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 14: a global linear lower bound yields a tail lower bound on the
normalized values `φ x / ‖x‖`. -/
private theorem linear_lower_bound_div_norm
    {φ : H → Set.Ioi (⊥ : EReal)} {R C : ℝ}
    (hbound : ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (φ x : EReal)))
    {x : H} (hnorm : (1 : ℝ) ≤ ‖x‖) :
    ((-(R + |C|) : ℝ) : EReal) ≤ (φ x : EReal) / ‖x‖ := by
  -- Divide the affine lower bound by the positive norm and absorb the constant term with `|C|`.
  have hnorm_pos_real : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact EReal.coe_pos.2 hnorm_pos_real
  have hreal :
      (-(R + |C|)) * ‖x‖ ≤ -R * ‖x‖ - C := by
    have hC_le : C ≤ ‖x‖ * |C| := by
      have habs_le : |C| ≤ ‖x‖ * |C| := by
        simpa [one_mul, mul_comm] using mul_le_mul_of_nonneg_right hnorm (abs_nonneg C)
      exact le_trans (le_abs_self C) habs_le
    calc
      (-(R + |C|)) * ‖x‖ = -(R * ‖x‖) + -(‖x‖ * |C|) := by ring
      _ ≤ -R * ‖x‖ - C := by linarith
  have hcast :
      ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hmul_le :
      (((( -(R + |C|) : ℝ) : EReal) * ‖x‖)) ≤ (φ x : EReal) := by
    calc
      (((( -(R + |C|) : ℝ) : EReal) * ‖x‖))
          = ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) := by
              rw [← EReal.coe_mul]
      _ ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := hcast
      _ ≤ (φ x : EReal) := hbound x
  exact (EReal.le_div_iff_mul_le hnorm_pos (by simp)).2 hmul_le

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 14: adding a summand with a global linear lower bound to a
supercoercive summand preserves supercoercivity. -/
private theorem pointwiseAdd_supercoercive_of_linear_lower_bound
    {φ ψ : H → Set.Ioi (⊥ : EReal)}
    (hφ_bound : ∃ R C : ℝ, ∀ x, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ φ.asEReal x))
    (hψ_super : Supercoercive ψ.asEReal) :
    Supercoercive (φ + ψ).asEReal := by
  -- Combine the supercoercive tail of `ψ` with the bounded error coming from the linear minorant.
  rcases hφ_bound with ⟨R, C, hbound⟩
  rw [Supercoercive, EReal.tendsto_nhds_top_iff_real] at hψ_super ⊢
  intro ξ
  have hnorm_tail : ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖ := by
    simpa using
      (eventually_cobounded_le_norm (1 : ℝ) :
        ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖)
  have hψ_tail :
      ∀ᶠ x in Bornology.cobounded H, ((ξ + (R + |C|) : ℝ) : EReal) < ψ.asEReal x / ‖x‖ :=
    hψ_super (ξ + (R + |C|))
  filter_upwards [hnorm_tail, hψ_tail] with x hnorm hxψ
  have hφ_tail :
      ((-(R + |C|) : ℝ) : EReal) ≤ φ.asEReal x / ‖x‖ :=
    linear_lower_bound_div_norm (φ := φ) hbound hnorm
  have hquot_split :
      ((φ + ψ).asEReal x) / ‖x‖ = φ.asEReal x / ‖x‖ + ψ.asEReal x / ‖x‖ := by
    have hnorm_nonneg : (0 : EReal) ≤ (‖x‖ : EReal) := by
      exact_mod_cast norm_nonneg x
    change (((φ x : EReal) + (ψ x : EReal)) / (‖x‖ : EReal) =
      (φ x : EReal) / (‖x‖ : EReal) + (ψ x : EReal) / (‖x‖ : EReal))
    simpa using
      (EReal.add_div_of_nonneg_right (a := φ.asEReal x) (b := ψ.asEReal x) (c := (‖x‖ : EReal))
        hnorm_nonneg)
  have hleft_bot : φ.asEReal x / ‖x‖ ≠ ⊥ := by
    exact ne_bot_of_le_ne_bot (by simp) hφ_tail
  have hadd :
      ((-(R + |C|) : ℝ) : EReal) + ((ξ + (R + |C|) : ℝ) : EReal) <
        φ.asEReal x / ‖x‖ + ψ.asEReal x / ‖x‖ := by
    have hadd' :
        ((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal) <
          ψ.asEReal x / ‖x‖ + φ.asEReal x / ‖x‖ := by
      exact EReal.add_lt_add_of_lt_of_le' hxψ hφ_tail hleft_bot (by
        intro _ hz
        exact (EReal.coe_ne_top _ hz).elim)
    simpa [add_comm, add_left_comm, add_assoc] using hadd'
  calc
    (ξ : EReal)
        = (((-(R + |C|) : ℝ) : EReal) + ((ξ + (R + |C|) : ℝ) : EReal)) := by
            rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
            ring
    _ < φ.asEReal x / ‖x‖ + ψ.asEReal x / ‖x‖ := hadd
    _ = ((φ + ψ).asEReal x) / ‖x‖ := hquot_split.symm

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: adding a summand with a zero-slope affine minorant to a
coercive summand preserves coercivity. -/
private theorem pointwiseAdd_coercive_of_coercive_of_zeroSlopeAffineMinorant
    {φ ψ : H → Set.Ioi (⊥ : EReal)}
    (hφ_coe : Coercive φ.asEReal)
    (hψ_minor : HasContinuousAffineMinorantWithSlope ψ.asEReal 0) :
    Coercive (φ + ψ).asEReal := by
  -- Expand the affine minorant into a real lower bound and add it to the coercive tail of `φ`.
  rw [Coercive, EReal.tendsto_nhds_top_iff_real] at hφ_coe ⊢
  rcases hψ_minor with ⟨η, hη⟩
  intro ξ
  have hφ_tail :
      ∀ᶠ x in Bornology.cobounded H, ((ξ - η : ℝ) : EReal) < φ.asEReal x :=
    hφ_coe (ξ - η)
  filter_upwards [hφ_tail] with x hx
  have hψx : (η : EReal) ≤ ψ.asEReal x := by
    simpa using hη x
  have hsum :
      (ξ : EReal) = ((ξ - η : ℝ) : EReal) + (η : EReal) := by
    rw [← EReal.coe_add]
    ring_nf
  calc
    (ξ : EReal) = ((ξ - η : ℝ) : EReal) + (η : EReal) := hsum
    _ < φ.asEReal x + ψ.asEReal x := by
      exact EReal.add_lt_add_of_lt_of_le' hx hψx (by
        exact ne_of_gt (show (⊥ : EReal) < ψ.asEReal x from (ψ x).2)) <| by
          intro htop hbot
          simp at hbot
    _ = (φ + ψ).asEReal x := by simp [Function.asEReal]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 14: a supercoercive summand stays coercive after adding a summand
with a global linear lower bound. -/
private theorem pointwiseAdd_coercive_of_supercoercive_of_linear_lower_bound
    {φ ψ : H → Set.Ioi (⊥ : EReal)}
    (hψ_super : Supercoercive ψ.asEReal)
    (hφ_bound : ∃ R C : ℝ, ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ φ.asEReal x)) :
    Coercive (ψ + φ).asEReal := by
  -- First upgrade the sum to supercoercive, then use the owner-level implication to coercivity.
  convert coercive_of_supercoercive
      (pointwiseAdd_supercoercive_of_linear_lower_bound (φ := φ) (ψ := ψ) hφ_bound hψ_super) using 1
  ext x
  simp [add_comm]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: translating the second infimal-convolution summand by
`y ↦ x - y` preserves membership in `Γ₀(H)`. -/
private theorem sub_right_mem_gammaZero
    (hg : g ∈ Γ₀(H)) (x : H) :
    (fun y : H ↦ g (x - y)) ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity is stable under the continuous translation-reflection map.
    have hsub : Continuous fun y : H ↦ x - y := continuous_const.sub continuous_id
    simpa using hg.1.comp hsub
  · -- Rewrite the reflected translate into the convex-combination shape used by `g`.
    refine ⟨?_, subset_rfl, ?_⟩
    · rcases hg.2.nonempty with ⟨z, hz⟩
      refine ⟨x - z, ?_⟩
      simpa [mem_effectiveDomain_iff] using hz
    · intro y₁ hy₁ y₂ hy₂ a ha0 ha1
      have hy₁' : x - y₁ ∈ effectiveDomain g := by
        simpa [mem_effectiveDomain_iff] using hy₁
      have hy₂' : x - y₂ ∈ effectiveDomain g := by
        simpa [mem_effectiveDomain_iff] using hy₂
      have hcombo :
          a • (x - y₁) + (1 - a) • (x - y₂) = x - (a • y₁ + (1 - a) • y₂) := by
        have hxsplit : a • x + (1 - a) • x = x := by
          calc
            a • x + (1 - a) • x = (a + (1 - a)) • x := by rw [← add_smul]
            _ = (1 : ℝ) • x := by ring_nf
            _ = x := by simp
        calc
          a • (x - y₁) + (1 - a) • (x - y₂)
              = a • x + (1 - a) • x - (a • y₁ + (1 - a) • y₂) := by
                  rw [smul_sub, smul_sub]
                  abel
          _ = x - (a • y₁ + (1 - a) • y₂) := by
                rw [hxsplit]
      simpa [hcombo] using
        hg.2.ineq hy₁' hy₂' ha0 ha1

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: members of `Γ₀(H)` are weakly sequentially lower
semicontinuous. -/
private theorem weak_seq_tendsto_le_liminf_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    {x : H} {u : ℕ → H}
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (nhds (toWeakSpace ℝ H x))) :
    φ.asEReal x ≤ liminf (φ.asEReal ∘ u) atTop := by
  -- Read the weak-sequential clause directly from Theorem 9.1 using the convex epigraph of `φ`.
  have htfae :
      List.TFAE
        [ (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
              Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (nhds (toWeakSpace ℝ H x)) →
                φ.asEReal x ≤ liminf (φ.asEReal ∘ xₙ) atTop),
          (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
              Tendsto xₙ atTop (nhds x) →
                φ.asEReal x ≤ liminf (φ.asEReal ∘ xₙ) atTop),
          LowerSemicontinuous φ.asEReal,
          WeaklyLowerSemicontinuous φ.asEReal ] := by
    exact convex_lowerSemicontinuity_tfae
      (convex_epigraph_asEReal_of_mem_gammaZero hφ)
  have hweak_seq :
      (∀ ⦃xₙ : ℕ → H⦄ ⦃x : H⦄,
          Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (nhds (toWeakSpace ℝ H x)) →
            φ.asEReal x ≤ liminf (φ.asEReal ∘ xₙ) atTop) := by
    exact (List.TFAE.out htfae 0 2).2 hφ.1
  exact hweak_seq hu

/-- Helper for Proposition 12 14: for each base point `x`, the translated minimization problem
`y ↦ f y + g (x - y)` attains the infimum defining `(f □ g) x`. -/
private theorem infimalConvolution_exactAt_of_supercoercive_or_coercive_bddBelow
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x))
    (x : H) :
    infimalConvolution.ExactAt f g x := by
  let gx : H → Set.Ioi (⊥ : EReal) := fun y ↦ g (x - y)
  have hgx : gx ∈ Γ₀(H) := by
    -- Translate the second summand so the minimizing problem is an ordinary pointwise sum.
    simpa [gx] using sub_right_mem_gammaZero (g := g) hg x
  by_cases hdom : (effectiveDomain f ∩ effectiveDomain gx).Nonempty
  · have hsum : f + gx ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f gx hf hgx hdom
    have hcoe : Coercive (f + gx).asEReal := by
      rcases hcase with hf_super | ⟨hf_coe, hg_bddBelow⟩
      · -- The translated `g` summand still has a global linear lower bound, so the sum stays
        -- coercive by the supercoercive source route.
        rcases exists_linear_lower_bound_of_mem_gammaZero (φ := gx) hgx with ⟨R, C, hbound⟩
        exact
          pointwiseAdd_coercive_of_supercoercive_of_linear_lower_bound
            (φ := gx) (ψ := f) hf_super ⟨R, C, hbound⟩
      · have hgx_minor : HasContinuousAffineMinorantWithSlope gx.asEReal 0 := by
          -- The translated bounded-below summand keeps the same zero-slope affine minorant.
          apply hasContinuousAffineMinorantWithSlope_zero_of_bddBelow
          rcases hg_bddBelow with ⟨η, hη⟩
          refine ⟨η, ?_⟩
          intro y
          simpa [gx, Function.asEReal] using hη (x - y)
        exact
          pointwiseAdd_coercive_of_coercive_of_zeroSlopeAffineMinorant
            (φ := f) (ψ := gx) hf_coe hgx_minor
    rcases
      argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded hsum
        isClosed_univ convex_univ Set.univ_nonempty (Or.inl hcoe) with
      ⟨y, hy⟩
    have hymin : IsMinOn (f + gx).asEReal Set.univ y := (mem_argmin_iff).1 hy
    refine ⟨y, le_antisymm ?_ ?_⟩
    · -- The defining infimum is bounded above by the minimizing translated decomposition.
      calc
        (f □ g) x ≤ ((f + gx).asEReal y) := by
          rw [infimalConvolution_apply]
          exact iInf_le _ y
        _ = (f y : EReal) + (g (x - y) : EReal) := by
          simp [gx, Function.asEReal]
    · -- Global minimality of `y` gives the reverse inequality against every decomposition.
      rw [infimalConvolution_apply]
      refine le_iInf fun z ↦ ?_
      simpa [gx, Function.asEReal, pointwiseAdd_apply] using
        (isMinOn_univ_iff.mp hymin) z
  · rcases hf.2.nonempty with ⟨y, hy⟩
    refine ⟨y, le_antisymm ?_ ?_⟩
    · -- The infimum is always below the value at the chosen feasible point.
      calc
        (f □ g) x ≤ ((f + gx).asEReal y) := by
          rw [infimalConvolution_apply]
          exact iInf_le _ y
        _ = (f y : EReal) + (g (x - y) : EReal) := by
          simp [gx, Function.asEReal]
    · -- Empty domain intersection forces every translated sum value to be `⊤`.
      rw [infimalConvolution_apply]
      refine le_iInf fun z ↦ ?_
      have hz_top : (f + gx).asEReal z = ⊤ := by
        apply le_antisymm le_top
        apply not_lt.mp
        intro hz
        exact hdom ⟨z, ((mem_effectiveDomain_pointwiseAdd_iff f gx z).1 hz).1,
          ((mem_effectiveDomain_pointwiseAdd_iff f gx z).1 hz).2⟩
      have hy_gx_not_dom : y ∉ effectiveDomain gx := by
        intro hy_gx
        exact hdom ⟨y, hy, hy_gx⟩
      have hy_gx_top : gx.asEReal y = ⊤ := by
        apply le_antisymm le_top
        exact not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy_gx_not_dom)
      have hy_sum_top : (f y : EReal) + (g (x - y) : EReal) = ⊤ := by
        have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from
          (f y).2)
        calc
          (f y : EReal) + (g (x - y) : EReal) = (f y : EReal) + gx.asEReal y := by
            simp [gx, Function.asEReal]
          _ = ⊤ := by
            rw [hy_gx_top]
            exact EReal.add_top_of_ne_bot hfy_bot
      have hz_sum_top : (f z : EReal) + (g (x - z) : EReal) = ⊤ := by
        simpa [gx, Function.asEReal] using hz_top
      rw [hy_sum_top, hz_sum_top]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: convexity of the real-height epigraph yields owner-level
Jensen convexity once the function is known to avoid the value `-∞`. -/
private theorem isConvex_of_convex_epigraph_of_ne_bot
    {h : H → EReal} (h_ne_bot : ∀ x : H, h x ≠ ⊥)
    (hconv_epi : Convex ℝ (epigraph h)) :
    IsConvex h := by
  -- Route correction: first use the epigraph criterion on finite-domain points, then handle the
  -- `⊤` endpoint cases separately so the owner-level statement holds on all of `H`.
  intro x y a ha0 ha1
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp
  by_cases ha_one : a = 1
  · subst ha_one
    have hx1 : ((1 : ℝ) • x + (1 - (1 : ℝ)) • y) = x := by
      simp
    rw [hx1]
    have hzero : (1 - (1 : EReal)) * h y = 0 := by
      have hcoef_zero : (1 - (1 : EReal)) = 0 := by
        exact EReal.sub_self (x := (1 : EReal)) (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
      rw [hcoef_zero]
      simp
    simp [hzero]
  have ha_pos : 0 < a := lt_of_le_of_ne ha0 (by
    intro h
    exact ha_zero h.symm)
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha1 ha_one
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  change h (a • x + (1 - a) • y) ≤
    (a : EReal) * h x + (1 - (a : EReal)) * h y
  by_cases hx : x ∈ dom h
  · by_cases hy : y ∈ dom h
    · rw [hcoef_eq]
      exact (convex_epigraph_iff_jensen_on_dom h).1 hconv_epi hx hy ha_pos ha_lt_one
    · have hy_top : h y = ⊤ := le_antisymm le_top (not_lt.mp hy)
      have hx_term_ne_bot : (a : EReal) * h x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inr (h_ne_bot x), Or.inl (EReal.coe_ne_top a),
          Or.inl (EReal.coe_nonneg.mpr ha0)⟩
      rw [hy_top, hcoef_eq, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one)),
        EReal.add_top_of_ne_bot hx_term_ne_bot]
      exact le_top
  · have hx_top : h x = ⊤ := le_antisymm le_top (not_lt.mp hx)
    have hcoef_nonneg : (0 : EReal) ≤ 1 - (a : EReal) := by
      exact_mod_cast sub_nonneg.mpr ha1
    have hy_term_ne_bot : (1 - (a : EReal)) * h y ≠ ⊥ := by
      have hcoef_ne_bot : (1 - (a : EReal)) ≠ ⊥ := by
        rw [hcoef_eq]
        exact EReal.coe_ne_bot (1 - a)
      have hcoef_ne_top : (1 - (a : EReal)) ≠ ⊤ := by
        rw [hcoef_eq]
        exact EReal.coe_ne_top (1 - a)
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl hcoef_ne_bot, Or.inr (h_ne_bot y), Or.inl hcoef_ne_top,
        Or.inl hcoef_nonneg⟩
    rw [hx_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos),
      EReal.top_add_of_ne_bot hy_term_ne_bot]
    exact le_top

/-- Under the hypotheses of Proposition 12.14, the infimal convolution never attains the value
`-∞`. -/
-- Proof sketch: for points in the effective domain of `f □ g`, use Proposition 12.6 to obtain a
-- decomposition `x = y + z` with finite summands, then apply Corollary 11.16 to the translated sum
-- `u ↦ f u + g (x - u)` to get a minimizer, so `(f □ g) x` is a real value. Outside the effective
-- domain, the value of `f □ g` is `⊤`.
private theorem infimalConvolution_mem_Ioi_bot_of_supercoercive_or_coercive_bddBelow
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x))
    (x : H) :
    (f □ g) x ∈ Set.Ioi (⊥ : EReal) := by
  -- The exact decomposition writes `(f □ g) x` as a sum of two values that are both `> ⊥`.
  rcases infimalConvolution_exactAt_of_supercoercive_or_coercive_bddBelow
      (f := f) (g := g) hf hg hcase x with ⟨y, hy⟩
  rw [Set.mem_Ioi, hy, bot_lt_iff_ne_bot]
  exact (EReal.add_ne_bot_iff).2 ⟨ne_of_gt (f y).2, ne_of_gt (g (x - y)).2⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 14: a linear lower bound for `g` stays uniform after translating by a
bounded base sequence. -/
private theorem translated_linear_minorant_of_bounded_base
    {xSeq : ℕ → H}
    (hx_bdd : Bornology.IsBounded (Set.range xSeq))
    {R C : ℝ}
    (hbound : ∀ z : H, (((-R * ‖z‖ - C : ℝ) : EReal) ≤ g.asEReal z)) :
    ∃ D : ℝ, ∀ n : ℕ, ∀ y : H,
      (((-(|R|) * ‖y‖ - D : ℝ) : EReal) ≤ g.asEReal (xSeq n - y)) := by
  -- Put the bounded base sequence inside one closed ball, then absorb the translation error into a
  -- single constant.
  obtain ⟨B, hB⟩ := hx_bdd.subset_closedBall (0 : H)
  refine ⟨|R| * B + C, ?_⟩
  intro n y
  have hx_norm : ‖xSeq n‖ ≤ B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hB (Set.mem_range_self n)
  have hnorm :
      ‖xSeq n - y‖ ≤ B + ‖y‖ := by
    calc
      ‖xSeq n - y‖ ≤ ‖xSeq n‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ B + ‖y‖ := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hx_norm ‖y‖
  have htranslate :
      (-(|R|) : ℝ) * (B + ‖y‖) ≤ (-(|R|) : ℝ) * ‖xSeq n - y‖ := by
    have hnonpos : (-(|R|) : ℝ) ≤ 0 := by
      nlinarith [abs_nonneg R]
    exact mul_le_mul_of_nonpos_left hnorm hnonpos
  have habs_term :
      (-(|R|) : ℝ) * ‖xSeq n - y‖ ≤ (-R : ℝ) * ‖xSeq n - y‖ := by
    have hcoef : (-(|R|) : ℝ) ≤ -R := by
      linarith [le_abs_self R]
    exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hreal :
      -(|R|) * ‖y‖ - (|R| * B + C) ≤ -R * ‖xSeq n - y‖ - C := by
    calc
      -(|R|) * ‖y‖ - (|R| * B + C) = (-(|R|) : ℝ) * (B + ‖y‖) - C := by ring
      _ ≤ (-(|R|) : ℝ) * ‖xSeq n - y‖ - C := sub_le_sub_right htranslate C
      _ ≤ (-R : ℝ) * ‖xSeq n - y‖ - C := sub_le_sub_right habs_term C
  have hcast :
      (((-(|R|) * ‖y‖ - (|R| * B + C) : ℝ) : EReal)) ≤
        (((-R * ‖xSeq n - y‖ - C : ℝ) : EReal)) := by
    exact_mod_cast hreal
  exact le_trans hcast (hbound (xSeq n - y))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 14: in the supercoercive branch, the translated objectives
`y ↦ f y + g (xₙ - y)` eventually lie above any fixed real level outside one ball, uniformly in
`n`. -/
private theorem translated_sum_eventually_above_level_of_supercoercive_branch
    {xSeq : ℕ → H}
    (hf_super : Supercoercive f.asEReal)
    {A D ξ : ℝ}
    (hbound :
      ∀ n : ℕ, ∀ y : H, (((-A * ‖y‖ - D : ℝ) : EReal) ≤ g.asEReal (xSeq n - y))) :
    ∃ ρ : ℝ, ∀ n : ℕ, ∀ y : H, ρ ≤ ‖y‖ →
      (ξ : EReal) < (f y : EReal) + (g (xSeq n - y) : EReal) := by
  -- Route correction: bound the translated sum itself, not `f y` alone, because the source proof
  -- controls the minimizers through the whole translated objective.
  rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real] at hf_super
  let M : ℝ := max ξ 0 + A + |D| + 1
  have hquot :
      ∀ᶠ y in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
        ((M : ℝ) : EReal) < f.asEReal y / ‖y‖ :=
    hf_super M
  have hnorm :
      ∀ᶠ y in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop, (1 : ℝ) ≤ ‖y‖ := by
    simpa using
      (Filter.Tendsto.eventually_ge_atTop
        (Filter.tendsto_comap : Filter.Tendsto (fun y : H ↦ ‖y‖)
          (Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop) Filter.atTop) 1)
  have htail :
      ∀ᶠ y in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop,
        ∀ n : ℕ, (ξ : EReal) < (f y : EReal) + (g (xSeq n - y) : EReal) := by
    filter_upwards [hquot, hnorm] with y hyquot hnorm n
    have hnorm_pos : (0 : EReal) < ‖y‖ := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hnorm
    have hg_tail :
        ((-(A + |D|) : ℝ) : EReal) ≤ (g (xSeq n - y) : EReal) / ‖y‖ := by
      exact
        linear_lower_bound_div_norm
          (φ := fun u : H ↦ g (xSeq n - u))
          (hbound n) hnorm
    have hquot_split :
        (((f y : EReal) + (g (xSeq n - y) : EReal)) / ‖y‖) =
          (f y : EReal) / ‖y‖ + (g (xSeq n - y) : EReal) / ‖y‖ := by
      have hnorm_nonneg : (0 : EReal) ≤ (‖y‖ : EReal) := by
        exact_mod_cast norm_nonneg y
      simpa using
        (EReal.add_div_of_nonneg_right
          (a := (f y : EReal)) (b := (g (xSeq n - y) : EReal)) (c := (‖y‖ : EReal))
          hnorm_nonneg)
    have hg_bot : (g (xSeq n - y) : EReal) / ‖y‖ ≠ ⊥ := by
      exact ne_bot_of_le_ne_bot (by simp) hg_tail
    have hadd :
        ((M : ℝ) : EReal) + ((-(A + |D|) : ℝ) : EReal) <
          (f y : EReal) / ‖y‖ + (g (xSeq n - y) : EReal) / ‖y‖ := by
      exact EReal.add_lt_add_of_lt_of_le' hyquot hg_tail hg_bot (by
        intro _ hz
        exact (EReal.coe_ne_top _ hz).elim)
    have hquot_sum :
        (((max ξ 0 + 1 : ℝ) : EReal)) <
          (((f y : EReal) + (g (xSeq n - y) : EReal)) / ‖y‖) := by
      calc
        (((max ξ 0 + 1 : ℝ) : EReal))
            = ((M : ℝ) : EReal) + ((-(A + |D|) : ℝ) : EReal) := by
                rw [show ((max ξ 0 + 1 : ℝ) : EReal) =
                    (((M - (A + |D|) : ℝ) : ℝ) : EReal) by
                    congr 1
                    dsimp [M]
                    ring]
                rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
                dsimp [M]
                ring
        _ < (f y : EReal) / ‖y‖ + (g (xSeq n - y) : EReal) / ‖y‖ := hadd
        _ = (((f y : EReal) + (g (xSeq n - y) : EReal)) / ‖y‖) := hquot_split.symm
    have hmul :
        (((max ξ 0 + 1 : ℝ) : EReal) * ‖y‖) <
          (f y : EReal) + (g (xSeq n - y) : EReal) := by
      exact (EReal.lt_div_iff hnorm_pos (by simp)).1 hquot_sum
    have hξ_le :
        (ξ : EReal) ≤ (((max ξ 0 + 1 : ℝ) : EReal) * ‖y‖) := by
      have hξ_le_base : (ξ : EReal) ≤ ((max ξ 0 + 1 : ℝ) : EReal) := by
        exact_mod_cast (show ξ ≤ max ξ 0 + 1 by
          have : ξ ≤ max ξ 0 := le_max_left _ _
          linarith)
      have hbase_mul :
          (((max ξ 0 + 1 : ℝ) : EReal)) ≤
            (((max ξ 0 + 1 : ℝ) : EReal) * ‖y‖) := by
        calc
          (((max ξ 0 + 1 : ℝ) : EReal)) = (((max ξ 0 + 1 : ℝ) : EReal) * 1) := by simp
          _ ≤ (((max ξ 0 + 1 : ℝ) : EReal) * ‖y‖) := by
              exact mul_le_mul_of_nonneg_left
                (by exact_mod_cast hnorm)
                (by
                  have : (0 : ℝ) ≤ max ξ 0 + 1 := by positivity
                  exact_mod_cast this)
      exact le_trans hξ_le_base hbase_mul
    exact lt_of_le_of_lt hξ_le hmul
  rcases Filter.mem_comap.mp htail with ⟨s, hs, hs_sub⟩
  rcases Filter.mem_atTop_sets.mp hs with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  intro n y hy
  exact (hs_sub (hρ ‖y‖ hy)) n

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: exact minimizing decompositions stay in a bounded set once the
base points stay bounded and the infimal-convolution values stay below a fixed real level. -/
private theorem bounded_exact_minimizers_of_bounded_base_and_values
    (hg : g ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x))
    {xSeq ySeq : ℕ → H} {ξ : ℝ}
    (hx_bdd : Bornology.IsBounded (Set.range xSeq))
    (hy_exact :
      ∀ n, (f □ g) (xSeq n) = (f (ySeq n) : EReal) + (g (xSeq n - ySeq n) : EReal))
    (hval : ∀ n, (f □ g) (xSeq n) ≤ (ξ : EReal)) :
    Bornology.IsBounded (Set.range ySeq) := by
  rcases hcase with hf_super | ⟨hf_coe, hg_bddBelow⟩
  · -- In the supercoercive branch, bound the translated objective uniformly outside one ball.
    rcases exists_linear_lower_bound_of_mem_gammaZero (φ := g) hg with ⟨R, C, hbound⟩
    rcases
        translated_linear_minorant_of_bounded_base (g := g) hx_bdd hbound with
      ⟨D, htranslated⟩
    rcases
        translated_sum_eventually_above_level_of_supercoercive_branch
          (f := f) (g := g) hf_super (A := |R|) (D := D) (ξ := ξ) htranslated with
      ⟨ρ, hρ⟩
    refine (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : H) ρ)).subset
      ?_
    intro z hz
    rcases hz with ⟨n, rfl⟩
    -- Exactness plus the level bound forbid `‖yₙ‖` from crossing the radius `ρ`.
    have hnot_ge : ¬ρ ≤ ‖ySeq n‖ := by
      intro hy_norm
      have hgt :
          (ξ : EReal) < (f (ySeq n) : EReal) + (g (xSeq n - ySeq n) : EReal) :=
        hρ n (ySeq n) hy_norm
      exact (not_lt_of_ge (le_trans (Eq.le (hy_exact n).symm) (hval n))) hgt
    simp [Metric.mem_closedBall, dist_eq_norm, le_of_lt (lt_of_not_ge hnot_ge)]
  · -- In the coercive branch, the lower bound for `g` puts every exact minimizer in one lower
    -- level set of `f`.
    rcases hg_bddBelow with ⟨η, hη⟩
    have hlevel_bdd :
        Bornology.IsBounded (lowerLevelSet f.asEReal (ξ - η)) :=
      (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hf_coe (ξ - η)
    refine hlevel_bdd.subset ?_
    intro z hz
    rcases hz with ⟨n, rfl⟩
    rw [mem_lowerLevelSet_iff]
    have hsum_le :
        (f (ySeq n) : EReal) + (η : EReal) ≤ (ξ : EReal) := by
      calc
        (f (ySeq n) : EReal) + (η : EReal) ≤
            (f (ySeq n) : EReal) + (g (xSeq n - ySeq n) : EReal) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left (hη (xSeq n - ySeq n)) (f (ySeq n) : EReal)
        _ = (f □ g) (xSeq n) := (hy_exact n).symm
        _ ≤ (ξ : EReal) := hval n
    have hfy_bot : (f (ySeq n) : EReal) ≠ ⊥ := ne_of_gt (f (ySeq n)).2
    have hfy_top : (f (ySeq n) : EReal) ≠ ⊤ := by
      intro hfy_top
      have : (⊤ : EReal) ≤ (ξ : EReal) := by
        rw [hfy_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot η)] at hsum_le
        exact hsum_le
      exact (EReal.coe_ne_top ξ) (top_unique this)
    have hsum_real :
        (f (ySeq n) : EReal).toReal + η ≤ ξ := by
      have hcast :
          (((((f (ySeq n) : EReal).toReal + η : ℝ)) : EReal)) ≤ (ξ : EReal) := by
        simpa [EReal.coe_add, EReal.coe_toReal hfy_top hfy_bot] using hsum_le
      exact EReal.coe_le_coe_iff.1 hcast
    have hlevel_real : (f (ySeq n) : EReal).toReal ≤ ξ - η := by
      linarith
    simpa [Function.asEReal, EReal.coe_toReal hfy_top hfy_bot] using
      (show ((((f (ySeq n) : EReal).toReal : ℝ) : EReal) ≤ (ξ - η : EReal)) from by
        exact_mod_cast hlevel_real)

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: strong convergence of one sequence and weak convergence of a
second sequence imply weak convergence of their difference. -/
private theorem tendsto_toWeakSpace_sub_of_tendsto_of_tendsto_toWeakSpace
    {u v : ℕ → H} {uLim vLim : H}
    (hu : Tendsto u atTop (nhds uLim))
    (hv :
      Tendsto (fun n ↦ toWeakSpace ℝ H (v n)) atTop
        (nhds (toWeakSpace ℝ H vLim))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (u n - v n)) atTop
      (nhds (toWeakSpace ℝ H (uLim - vLim))) := by
  -- Send the strong limit through the canonical continuous map to `WeakSpace`, then subtract there.
  have huWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop
        (nhds (toWeakSpace ℝ H uLim)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto uLim).comp hu
  simpa using huWeak.sub hv

omit [CompleteSpace H] in
/-- Helper for Proposition 12 14: an exact minimizing sequence over a strongly convergent base
sequence already gives the liminf inequality at the limit point. -/
private theorem infimalConvolution_le_liminf_of_exact_minimizer_subsequence
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    {x : H} {u ySeq : ℕ → H} {y : H}
    (hu : Tendsto u atTop (nhds x))
    (hy :
      Tendsto (fun n ↦ toWeakSpace ℝ H (ySeq n)) atTop
        (nhds (toWeakSpace ℝ H y)))
    (hexact :
      ∀ n, (f □ g) (u n) = (f (ySeq n) : EReal) + (g (u n - ySeq n) : EReal)) :
    (f □ g) x ≤ liminf ((f □ g) ∘ u) atTop := by
  -- Route correction: package the final liminf comparison once, instead of rebuilding the same
  -- weak-subsequence algebra inside the contradiction proof.
  have hsub :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n - ySeq n)) atTop
        (nhds (toWeakSpace ℝ H (x - y))) :=
    tendsto_toWeakSpace_sub_of_tendsto_of_tendsto_toWeakSpace hu hy
  have hsum_eq :
      (f.asEReal ∘ ySeq) + (g.asEReal ∘ fun n ↦ u n - ySeq n) = ((f □ g) ∘ u) := by
    funext n
    simpa [Function.comp, Function.asEReal] using (hexact n).symm
  -- Compare `(f □ g) x` with the exact decomposition at the weak limit `y`, then pass to liminf.
  calc
    (f □ g) x ≤ (f y : EReal) + (g (x - y) : EReal) := by
      rw [infimalConvolution_apply]
      exact iInf_le _ y
    _ ≤ liminf (f.asEReal ∘ ySeq) atTop + liminf (g.asEReal ∘ fun n ↦ u n - ySeq n) atTop := by
      exact add_le_add
        (weak_seq_tendsto_le_liminf_of_mem_gammaZero (φ := f) hf hy)
        (weak_seq_tendsto_le_liminf_of_mem_gammaZero (φ := g) hg hsub)
    _ ≤ liminf ((f.asEReal ∘ ySeq) + (g.asEReal ∘ fun n ↦ u n - ySeq n)) atTop := by
      simpa using
        (EReal.le_liminf_add :
          liminf (f.asEReal ∘ ySeq) atTop +
              liminf (g.asEReal ∘ fun n ↦ u n - ySeq n) atTop ≤
            liminf ((f.asEReal ∘ ySeq) + (g.asEReal ∘ fun n ↦ u n - ySeq n)) atTop)
    _ = liminf ((f □ g) ∘ u) atTop := by
      rw [hsum_eq]

/-- Helper for Proposition 12 14: along every strongly convergent base sequence, the infimal
convolution satisfies the liminf inequality required for lower semicontinuity. -/
private theorem seq_tendsto_le_liminf_infimalConvolution_of_supercoercive_or_coercive_bddBelow
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ g.asEReal x))
    {x : H} {xSeq : ℕ → H}
    (hx : Tendsto xSeq atTop (nhds x)) :
    (f □ g) x ≤ liminf ((f □ g) ∘ xSeq) atTop := by
  -- Route correction: follow the source proof literally via exact minimizers of a strict sublevel
  -- subsequence, then pass to a weakly convergent bounded subsubsequence of minimizers.
  by_contra hnot
  have hlt : liminf ((f □ g) ∘ xSeq) atTop < (f □ g) x := lt_of_not_ge hnot
  obtain ⟨ξ, hξ_left, hξ_right⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  let p : H → Prop := fun z ↦ (f □ g) z < (ξ : EReal)
  have hfreq :
      ∃ᶠ n in atTop, p (xSeq n) := by
    simpa [p, Function.comp] using
      (Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hξ_left)
  obtain ⟨σ, hσ_tendsto, hσ_mem⟩ := Filter.subseq_forall_of_frequently hx hfreq
  have hxσ_bdd : Bornology.IsBounded (Set.range (fun n ↦ xSeq (σ n))) := by
    exact Metric.isBounded_range_of_tendsto _ hσ_tendsto
  have hexactAt :
      ∀ n, infimalConvolution.ExactAt f g (xSeq (σ n)) := by
    intro n
    exact
      infimalConvolution_exactAt_of_supercoercive_or_coercive_bddBelow
        (f := f) (g := g) hf hg hcase (xSeq (σ n))
  classical
  choose y hy_exact using hexactAt
  have hy_bdd : Bornology.IsBounded (Set.range y) := by
    -- The earlier bounded-minimizer lemma applies to the exact minimizers of the strict sublevel
    -- subsequence.
    refine
      bounded_exact_minimizers_of_bounded_base_and_values
        (f := f) (g := g) (ξ := ξ) hg hcase hxσ_bdd hy_exact ?_
    intro n
    exact le_of_lt (hσ_mem n)
  obtain ⟨r, hrange_subset⟩ := hy_bdd.subset_closedBall (0 : H)
  obtain ⟨yLim, -, φ, hφ, hyLim⟩ :=
    exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex
      Metric.isBounded_closedBall Metric.isClosed_closedBall (convex_closedBall (0 : H) r) y
      (fun n ↦ hrange_subset (Set.mem_range_self n))
  have hbaseSub :
      Tendsto (fun n ↦ xSeq (σ (φ n))) atTop (nhds x) := by
    -- Passing to the weakly convergent minimizer subsubsequence preserves convergence of the base
    -- sequence to `x`.
    exact hσ_tendsto.comp hφ.tendsto_atTop
  have hmain :
      (f □ g) x ≤ liminf ((f □ g) ∘ fun n ↦ xSeq (σ (φ n))) atTop :=
    infimalConvolution_le_liminf_of_exact_minimizer_subsequence
      (f := f) (g := g) hf hg hbaseSub hyLim (fun n ↦ hy_exact (φ n))
  have hsubseq_liminf_le :
      liminf ((f □ g) ∘ fun n ↦ xSeq (σ (φ n))) atTop ≤ (ξ : EReal) := by
    -- Every term of the extracted subsubsequence lies below the separating real level `ξ`.
    calc
      liminf ((f □ g) ∘ fun n ↦ xSeq (σ (φ n))) atTop ≤
          liminf (fun _ : ℕ ↦ (ξ : EReal)) atTop := by
            refine Filter.liminf_le_liminf <| Filter.Eventually.of_forall fun n ↦ ?_
            exact le_of_lt (hσ_mem (φ n))
      _ = (ξ : EReal) := tendsto_const_nhds.liminf_eq
  exact (not_le_of_gt hξ_right) (le_trans hmain hsubseq_liminf_le)

include hf hg hcase

-- Proof sketch: the companion exactness lemma gives attainment for the translated sum
-- `u ↦ f u + g (x - u)`, Proposition 12.11 gives convexity of the real-height epigraph, and the
-- Chapter 9 lower-semicontinuity result applies to the `EReal`-valued infimal convolution
-- itself. Together with the previous exclusion of `-∞`, these ingredients give the canonical
-- owner-level conclusion `IsProper (f □ g) ∧ (f □ g) ∈ gamma H`.
/-- Proposition 12 14 (Proposition 12.14): if `f, g ∈ Γ₀(H)` and either (i) `f` is supercoercive
or (ii) `f` is
coercive while `g` is bounded below, then the raw infimal convolution `f □ g` is proper,
convex, and lower semicontinuous. In the project's owner-level API this is expressed as
`IsProper (f □ g)` together with `(f □ g) ∈ gamma H`. -/
theorem isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
    :
    IsProper (f □ g) ∧ (f □ g) ∈ gamma H := by
  refine ⟨?_, ?_⟩
  · -- Properness is the conjunction of the no-`⊥` statement and a single finite witness.
    refine ⟨?_, ?_⟩
    · intro x
      exact ne_of_gt <|
        infimalConvolution_mem_Ioi_bot_of_supercoercive_or_coercive_bddBelow
          f g hf hg hcase x
    · rcases hf.2.nonempty with ⟨y, hy⟩
      rcases hg.2.nonempty with ⟨z, hz⟩
      refine ⟨y + z, ?_⟩
      rw [mem_dom_iff]
      calc
        (f □ g) (y + z) ≤ (f y : EReal) + (g ((y + z) - y) : EReal) := by
          rw [infimalConvolution_apply]
          exact iInf_le _ y
        _ = (f y : EReal) + (g z : EReal) := by simp
        _ < ⊤ := by
          exact EReal.add_lt_top
            (ne_of_lt (mem_effectiveDomain_iff.mp hy))
            (ne_of_lt (mem_effectiveDomain_iff.mp hz))
  · rw [mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · -- Proposition 12.11 supplies convexity of the real-height epigraph, and the no-`⊥` theorem
      -- upgrades it to the owner-level Jensen inequality.
      refine isConvex_of_convex_epigraph_of_ne_bot ?_ ?_
      · intro x
        exact ne_of_gt <|
          infimalConvolution_mem_Ioi_bot_of_supercoercive_or_coercive_bddBelow
            f g hf hg hcase x
      · exact convex_epigraph_infimalConvolution f g hf.2 hg.2
    · -- The source-faithful subsequence argument gives the sequence-liminf criterion.
      refine (lowerSemicontinuous_iff_seq_tendsto_le_liminf (f □ g)).2 ?_
      intro x xSeq hxSeq
      exact
        seq_tendsto_le_liminf_infimalConvolution_of_supercoercive_or_coercive_bddBelow
          (f := f) (g := g) hf hg hcase hxSeq

/-- Thin `Γ₀(H)` companion to Proposition 12.14, obtained by repackaging the raw owner
`f □ g : H → EReal` into its canonical `]-∞,+∞]`-valued view. -/
theorem infimalConvolution_mem_gammaZero_of_supercoercive_or_coercive_bddBelow
    :
    (fun x ↦
      ⟨(f □ g) x,
        infimalConvolution_mem_Ioi_bot_of_supercoercive_or_coercive_bddBelow
          f g hf hg hcase x⟩) ∈ Γ₀(H) := by
  -- Repackage the raw proper `gamma` owner through the canonical `properIoi` view.
  obtain ⟨hproper, hgamma⟩ :=
    isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
      (f := f) (g := g) hf hg hcase
  simpa [properIoi] using
    (properIoi_mem_gammaZero_of_mem_gamma (H := H) (f := f □ g) hproper hgamma)

-- Proof sketch: fix `x ∈ dom (f □ g)` and apply Corollary 11.16 to the translated sum
-- `u ↦ f u + g (x - u)` to obtain a minimizer; this is precisely
-- `infimalConvolution.ExactAt f g x`.
/-- Companion lemma to Proposition 12.14: under the same hypotheses, the infimal convolution is
exact. -/
lemma infimalConvolution_exact_of_supercoercive_or_coercive_bddBelow
    :
    infimalConvolution.Exact f g := by
  intro x _hx
  -- The pointwise attainment theorem is stronger than the domain-restricted exactness owner.
  exact infimalConvolution_exactAt_of_supercoercive_or_coercive_bddBelow
    (f := f) (g := g) hf hg hcase x

end Proposition1214

end ERealFunction
