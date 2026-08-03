import Mathlib
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 11 14: use the canonical pointwise sum as the local additive structure
on `]-∞,+∞]`-valued functions. -/
private noncomputable instance : Add (H → Set.Ioi (⊥ : EReal)) :=
  ⟨pointwiseAdd⟩

/-- Helper for Proposition 11 14: a `Γ₀(H)` function is bounded below by a global affine function
of the norm. -/
private theorem exists_linear_lower_bound_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ R C : ℝ, ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)) := by
  let _ : CompleteSpace H := inferInstance
  rcases hf.2.nonempty with ⟨p, hp⟩
  let ξ : ℝ := (f p : EReal).toReal - 1
  have hp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hp_bot : (f p : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hξ_lt_fp : (ξ : EReal) < (f p : EReal) := by
    rw [show (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) by
      symm
      exact EReal.coe_toReal hp_top hp_bot]
    exact_mod_cast (show ξ < (f p : EReal).toReal by
      dsimp [ξ]
      linarith)
  have hopen : IsOpen (f.asEReal ⁻¹' Set.Ioi (ξ : EReal)) := hf.1.isOpen_preimage (ξ : EReal)
  have hp_mem : p ∈ f.asEReal ⁻¹' Set.Ioi (ξ : EReal) := by
    simpa [Function.asEReal] using hξ_lt_fp
  rcases Metric.isOpen_iff.mp hopen p hp_mem with ⟨r, hr_pos, hr_subset⟩
  let δ : ℝ := r / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨δ⁻¹, 1 + ‖p‖ / δ - (f p : EReal).toReal, ?_⟩
  intro x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    by_cases hnear : ‖x - p‖ < δ
    · have hball : x ∈ Metric.ball p r := by
        have : ‖x - p‖ < r := by
          dsimp [δ] at hnear
          linarith
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hξ_lt_fx : (ξ : EReal) < (f x : EReal) := by
        exact hr_subset hball
      have hbound_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤ ξ := by
        dsimp [ξ]
        have hnonneg : 0 ≤ δ⁻¹ * ‖x‖ + ‖p‖ / δ := by
          positivity
        linarith
      have hbound_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤ (ξ : EReal) := by
        exact_mod_cast hbound_real
      exact le_trans hbound_ereal hξ_lt_fx.le
    · have hfar : δ ≤ ‖x - p‖ := le_of_not_gt hnear
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
          _ = t • x + (((1 - t) - 1) • p) := by
            congr 1
            calc
              (1 - t) • p - p = (1 - t) • p - (1 : ℝ) • p := by rw [one_smul]
              _ = (((1 - t) - 1) : ℝ) • p := by rw [← sub_smul]
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
      have hξ_lt_fy : (ξ : EReal) < (f y : EReal) := hr_subset hy_ball
      have hconv :
          (f y : EReal) ≤ (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) := by
        by_cases ht_one : t = 1
        · simp [y, ht_one]
        · have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht_one
          simpa [y] using hf.2.ineq (x := x) hx (y := p) hp (α := t) ht_pos ht_lt_one
      have hterm1_ne_top : (t : EReal) * (f x : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot t), Or.inl ?_, Or.inl (EReal.coe_ne_top t), Or.inr hx_top⟩
        exact_mod_cast ht_pos.le
      have hterm2_ne_top : ((1 - t : ℝ) : EReal) * (f p : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - t)), Or.inl ?_,
          Or.inl (EReal.coe_ne_top (1 - t)), Or.inr hp_top⟩
        exact_mod_cast sub_nonneg.mpr ht_le_one
      have hright_ne_top :
          (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) ≠ ⊤ :=
        EReal.add_ne_top hterm1_ne_top hterm2_ne_top
      have hy_top : (f y : EReal) ≠ ⊤ := by
        intro hy_top
        have : (⊤ : EReal) ≤
            (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) := by
          simpa [hy_top] using hconv
        exact hright_ne_top (top_unique this)
      have hy_dom : y ∈ effectiveDomain f := by
        exact mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hy_top)
      have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
      have hξ_lt_fy_real : ξ < (f y : EReal).toReal := by
        rw [← EReal.coe_toReal hy_top hy_bot] at hξ_lt_fy
        exact EReal.coe_lt_coe_iff.1 hξ_lt_fy
      have hconv_real :
          (f y : EReal).toReal ≤ t * (f x : EReal).toReal + (1 - t) * (f p : EReal).toReal := by
        have hconv_cast :
            (((f y : EReal).toReal : ℝ) : EReal) ≤
              (t : EReal) * (((f x : EReal).toReal : ℝ) : EReal) +
                ((1 - t : ℝ) : EReal) * (((f p : EReal).toReal : ℝ) : EReal) := by
          simpa [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot,
            EReal.coe_toReal hp_top hp_bot] using hconv
        exact EReal.coe_le_coe_iff.1 (by
          simpa [EReal.coe_mul, EReal.coe_add] using hconv_cast)
      have hfx_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) < (f x : EReal).toReal := by
        have hdist : ‖x - p‖ ≤ ‖x‖ + ‖p‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x p
        have hmain : (f p : EReal).toReal - 1 / t < (f x : EReal).toReal := by
          have haux : ξ < t * (f x : EReal).toReal + (1 - t) * (f p : EReal).toReal :=
            lt_of_lt_of_le hξ_lt_fy_real hconv_real
          have hsub : -1 < t * ((f x : EReal).toReal - (f p : EReal).toReal) := by
            dsimp [ξ] at haux
            linarith
          have hdiv : -1 / t < (f x : EReal).toReal - (f p : EReal).toReal := by
            exact (div_lt_iff₀ ht_pos).2 (by simpa [mul_comm] using hsub)
          have hmain_shift :
              (f p : EReal).toReal + (-1 / t) <
                (f p : EReal).toReal + ((f x : EReal).toReal - (f p : EReal).toReal) :=
            add_lt_add_right hdiv (f p : EReal).toReal
          calc
            (f p : EReal).toReal - 1 / t = (f p : EReal).toReal + (-1 / t) := by ring
            _ < (f p : EReal).toReal + ((f x : EReal).toReal - (f p : EReal).toReal) :=
              hmain_shift
            _ = (f x : EReal).toReal := by ring
        have ht_inv : 1 / t = ‖x - p‖ / δ := by
          dsimp [t]
          field_simp [hxp_pos.ne', hδ_pos.ne']
        rw [ht_inv] at hmain
        have hratio : ‖x - p‖ / δ ≤ ‖x‖ / δ + ‖p‖ / δ := by
          have := div_le_div_of_nonneg_right hdist hδ_pos.le
          simpa [add_div] using this
        have hleft_le :
            (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) ≤
              (f p : EReal).toReal - ‖x - p‖ / δ := by
          linarith
        have hfinal :
            (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) < (f x : EReal).toReal :=
          lt_of_le_of_lt hleft_le hmain
        have hrewrite :
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) =
              (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [hrewrite]
        exact hfinal
      have hfx_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) <
            (f x : EReal) := by
        rw [show (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) by
          symm
          exact EReal.coe_toReal hx_top hx_bot]
        exact_mod_cast hfx_real
      exact hfx_ereal.le
  · have hx_top : (f x : EReal) = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hxtop
      exact hx (mem_effectiveDomain_iff.mpr hxtop)
    simp [hx_top]

section

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Proposition 11 14: a global linear lower bound yields a uniform lower bound for
the normalized values `f x / ‖x‖` on the tail `‖x‖ ≥ 1`. -/
private theorem linear_lower_bound_div_norm
    {f : H → Set.Ioi (⊥ : EReal)} {R C : ℝ}
    (hbound : ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)))
    {x : H} (hnorm : (1 : ℝ) ≤ ‖x‖) :
    ((-(R + |C|) : ℝ) : EReal) ≤ (f x : EReal) / ‖x‖ := by
  have hnorm_pos_real : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact EReal.coe_pos.2 hnorm_pos_real
  have hC_scaled : -(‖x‖ * |C|) ≤ -C := by
    have hC_le : C ≤ ‖x‖ * |C| := by
      have habs_le : |C| ≤ ‖x‖ * |C| := by
        simpa [one_mul, mul_comm] using mul_le_mul_of_nonneg_right hnorm (abs_nonneg C)
      exact le_trans (le_abs_self C) habs_le
    simpa [mul_comm] using neg_le_neg hC_le
  have hreal :
      (-(R + |C|)) * ‖x‖ ≤ -R * ‖x‖ - C := by
    -- Expand the target lower bound into the norm part and the constant part.
    calc
      (-(R + |C|)) * ‖x‖ = -(R * ‖x‖) + -(‖x‖ * |C|) := by ring
      _ ≤ -R * ‖x‖ - C := by linarith
  have hcast :
      ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) ≤
        (((-R * ‖x‖ - C : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hmul_le :
      ((((-(R + |C|) : ℝ) : EReal) * ‖x‖)) ≤ (f x : EReal) := by
    -- Cast the linear lower bound to `EReal` and divide by the positive norm.
    calc
      (((-(R + |C|) : ℝ) : EReal) * ‖x‖)
          = ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) := by
              rw [← EReal.coe_mul]
      _ ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := hcast
      _ ≤ (f x : EReal) := hbound x
  -- Divide the affine lower bound by the positive norm to reach the supercoercive quotient.
  exact (EReal.le_div_iff_mul_le hnorm_pos (by simp)).2 hmul_le

end

section

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Proposition 11 14: adding a summand with a global linear lower bound to a
supercoercive summand preserves supercoercivity. -/
private theorem pointwiseAdd_supercoercive_of_linear_lower_bound
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hbound : ∃ R C : ℝ, ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)))
    (hg_super : Supercoercive g.asEReal) :
    Supercoercive (f + g).asEReal := by
  rcases hbound with ⟨R, C, hbound⟩
  rw [Supercoercive, EReal.tendsto_nhds_top_iff_real] at hg_super ⊢
  intro ξ
  have hnorm_tail : ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖ := by
    simpa using
      (eventually_cobounded_le_norm (1 : ℝ) :
        ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖)
  have hg_tail :
      ∀ᶠ x in Bornology.cobounded H, ((ξ + (R + |C|) : ℝ) : EReal) < g.asEReal x / ‖x‖ :=
    hg_super (ξ + (R + |C|))
  filter_upwards [hnorm_tail, hg_tail] with x hnorm hxg
  have hf_tail :
      ((-(R + |C|) : ℝ) : EReal) ≤ (f x : EReal) / ‖x‖ :=
    linear_lower_bound_div_norm hbound hnorm
  have hsum :
      (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) = (ξ : EReal) := by
    -- The linear lower bound contributes a bounded error that cancels in the target level.
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  have hquot_split :
      ((f + g).asEReal x) / ‖x‖ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by
    -- The canonical `Γ₀` wrapper only hides the ordinary pointwise `EReal` sum.
    have hnorm_nonneg : (0 : EReal) ≤ (‖x‖ : EReal) := by
      exact_mod_cast norm_nonneg x
    have happly : (((f + g) x : Set.Ioi (⊥ : EReal)) : EReal) = (f x : EReal) + (g x : EReal) :=
      rfl
    rw [Function.asEReal_apply, happly]
    simpa using
      (EReal.add_div_of_nonneg_right
        (a := (f x : EReal)) (b := (g x : EReal)) (c := (‖x‖ : EReal)) hnorm_nonneg)
  have hadd :
      ((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal) <
        (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := by
    have hright_bot : (f x : EReal) / ‖x‖ ≠ ⊥ := by
      exact ne_bot_of_le_ne_bot (by simp) hf_tail
    -- Combine the supercoercive tail of `g` with the linear lower bound for `f`.
    exact EReal.add_lt_add_of_lt_of_le' hxg hf_tail hright_bot (by
      intro _ hz
      exact (EReal.coe_ne_top _ hz).elim)
  -- Reassemble the quotient of the pointwise sum from the two normalized summands.
  calc
    (ξ : EReal)
        = (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) := hsum.symm
    _ < (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := hadd
    _ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by rw [add_comm]
    _ = ((f + g).asEReal x) / ‖x‖ := hquot_split.symm

end

-- Proof sketch: use lower semicontinuity at one finite point to get a neighborhood on which `f`
-- is bounded below, propagate that local bound to a global linear lower bound via convexity, then
-- divide by `‖x‖` and combine the resulting tail estimate with the supercoercive growth of `g`.
-- The `Γ₀(H)`-valued wrapper `pointwiseAdd f g` is only a bridge; the supercoercive owner lives
-- on the underlying
-- `EReal`-valued sum.
/-- Proposition 11 14: if `f ∈ Γ₀(H)` and `g` is supercoercive, then the canonical underlying
extended-real-valued pointwise sum `(f + g).asEReal` is supercoercive. -/
theorem pointwiseAdd_supercoercive_of_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hg_super : Supercoercive g.asEReal) :
    Supercoercive (f + g).asEReal := by
  let _ : CompleteSpace H := inferInstance
  -- Obtain a global linear lower bound on `f` from convexity plus lower semicontinuity at one
  -- finite point, then combine it with the supercoercive tail of `g`.
  rcases exists_linear_lower_bound_of_mem_gammaZero hf with ⟨R, C, hbound⟩
  exact pointwiseAdd_supercoercive_of_linear_lower_bound ⟨R, C, hbound⟩ hg_super

end ERealFunction
