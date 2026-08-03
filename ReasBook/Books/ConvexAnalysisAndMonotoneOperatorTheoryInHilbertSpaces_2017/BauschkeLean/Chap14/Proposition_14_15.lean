import Mathlib
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap14.Proposition_14_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 14 15: a `Γ₀(H)` function is bounded below by a global affine
function of the norm. -/
lemma exists_linear_lower_bound_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ R C : ℝ, 0 ≤ R ∧ ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)) := by
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
  refine ⟨|δ⁻¹|, 1 + ‖p‖ / δ - (f p : EReal).toReal, abs_nonneg _, ?_⟩
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
      have hξ_lt_fx : (ξ : EReal) < (f x : EReal) := hr_subset hball
      have hbound_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤ ξ := by
        dsimp [ξ]
        have hnonneg : 0 ≤ δ⁻¹ * ‖x‖ + ‖p‖ / δ := by
          positivity
        linarith
      have hbound_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤
            (ξ : EReal) := by
        exact_mod_cast hbound_real
      have hbound_abs :
          (((-|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤
            (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) := by
        have hreal : -|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) := by
          have hmul : -|δ⁻¹| * ‖x‖ ≤ -δ⁻¹ * ‖x‖ := by
            have hneg : -|δ⁻¹| ≤ -δ⁻¹ := by
              nlinarith [le_abs_self (δ⁻¹)]
            exact mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
          linarith
        exact_mod_cast hreal
      exact le_trans hbound_abs (le_trans hbound_ereal hξ_lt_fx.le)
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
          _ = t • x + ((1 - t) • p - (1 : ℝ) • p) := by simp
          _ = t • x + ((1 - t - 1) • p) := by rw [← sub_smul]
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
        exact EReal.coe_le_coe_iff.1 (by simpa [EReal.coe_mul, EReal.coe_add] using hconv_cast)
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
            _ < (f p : EReal).toReal + ((f x : EReal).toReal - (f p : EReal).toReal) := hmain_shift
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
      have hbound_abs :
          (((-|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤
            (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) := by
        have hreal : -|δ⁻¹| * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) := by
          have hmul : -|δ⁻¹| * ‖x‖ ≤ -δ⁻¹ * ‖x‖ := by
            have hneg : -|δ⁻¹| ≤ -δ⁻¹ := by
              nlinarith [le_abs_self (δ⁻¹)]
            exact mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
          linarith
        exact_mod_cast hreal
      exact le_trans hbound_abs hfx_ereal.le
  · have hx_top : (f x : EReal) = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hxtop
      exact hx (mem_effectiveDomain_iff.mpr hxtop)
    simp [hx_top]

-- Proof sketch: for `(i) → (ii)`, combine supercoercive growth with the Fenchel conjugate formula
-- to get a uniform real upper bound on each bounded set. For `(ii) → (i)`, apply the bounded-set
-- hypothesis to large closed balls in the dual space and use the standard dual characterization of
-- supercoercivity for functions in `Γ₀(H)`.
/-- Proposition 14 15 (1): for `f ∈ Γ₀(H)`, supercoercivity of `f` is equivalent to the Fenchel
conjugate `f*` being bounded above on every bounded subset of `H`. -/
theorem supercoercive_iff_conjugate_boundedOnEveryBoundedSet
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Supercoercive f.asEReal ↔
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u ≤ M := by
  constructor
  · intro hsuper B hB
    rcases hB.subset_closedBall (0 : H) with ⟨R, hR⟩
    rcases exists_linear_lower_bound_of_mem_gammaZero hf with ⟨L, C, hL_nonneg, hlower⟩
    have hα_nonneg : 0 ≤ max R 0 := le_max_right R 0
    let α : NNReal := ⟨max R 0, hα_nonneg⟩
    rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real] at hsuper
    let ρ : ℝ := (α : ℝ) + L + 1
    have hρ_eventually :
        ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop,
          (ρ : EReal) < f.asEReal x / ‖x‖ := hsuper ρ
    rcases Filter.mem_comap.1 hρ_eventually with ⟨s, hs, hs_subset⟩
    rcases Filter.mem_atTop_sets.1 hs with ⟨S0, hS0⟩
    let S : ℝ := max S0 1
    have houtside :
        ∀ x : H, S ≤ ‖x‖ → (((ρ * ‖x‖ : ℝ) : EReal) ≤ f.asEReal x) := by
      intro x hx
      have hxS0 : S0 ≤ ‖x‖ := le_trans (le_max_left _ _) hx
      have hxone : (1 : ℝ) ≤ ‖x‖ := le_trans (le_max_right _ _) hx
      have hxmem : ‖x‖ ∈ s := hS0 _ hxS0
      have hquotx : (ρ : EReal) < f.asEReal x / ‖x‖ := hs_subset hxmem
      have hnorm_pos : (0 : EReal) < ‖x‖ := by
        exact_mod_cast lt_of_lt_of_le zero_lt_one hxone
      exact le_of_lt <| (EReal.lt_div_iff hnorm_pos (by simp)).1 hquotx
    let β : ℝ := min ((L + 1) * S) (-(((α : ℝ) + L) * S) - C)
    have hminorant :
        (scaledNormKernel α).asEReal + (fun _ : H ↦ (β : EReal)) ≤ f.asEReal := by
      intro x
      by_cases hxS : ‖x‖ ≤ S
      · have hβ_right : β ≤ -(((α : ℝ) + L) * S) - C := min_le_right _ _
        have hreal :
            (α : ℝ) * ‖x‖ + β ≤ -L * ‖x‖ - C := by
          have hα_term :
              (α : ℝ) * ‖x‖ + β ≤ (α : ℝ) * ‖x‖ + (-(((α : ℝ) + L) * S) - C) := by
            linarith
          have hα_drop :
              (α : ℝ) * ‖x‖ + (-(((α : ℝ) + L) * S) - C) ≤ -L * S - C := by
            have hmul_nonpos : (α : ℝ) * (‖x‖ - S) ≤ 0 := by
              exact mul_nonpos_of_nonneg_of_nonpos α.2 (sub_nonpos.mpr hxS)
            have haux : (α : ℝ) * ‖x‖ - ((α : ℝ) + L) * S ≤ -L * S := by
              linarith
            linarith
          have hL_step : -L * S - C ≤ -L * ‖x‖ - C := by
            have hLS : -L * S ≤ -L * ‖x‖ := by
              nlinarith [hxS, hL_nonneg]
            linarith
          exact le_trans hα_term (le_trans hα_drop hL_step)
        have hcast :
            ((((α : ℝ) * ‖x‖ + β : ℝ) : EReal)) ≤ (((-L * ‖x‖ - C : ℝ) : EReal)) := by
          exact_mod_cast hreal
        have hscaled :
            ((scaledNormKernel α).asEReal x + (β : EReal)) ≤ (((-L * ‖x‖ - C : ℝ) : EReal)) := by
          simpa [scaledNormKernel_apply, add_comm, add_left_comm, add_assoc] using hcast
        exact le_trans hscaled (hlower x)
      · have hSx : S ≤ ‖x‖ := le_of_not_ge hxS
        have hβ_left : β ≤ (L + 1) * S := min_le_left _ _
        have hreal : (α : ℝ) * ‖x‖ + β ≤ ρ * ‖x‖ := by
          have hL1_nonneg : 0 ≤ L + 1 := by linarith
          have hS_bound : (L + 1) * S ≤ (L + 1) * ‖x‖ := by
            exact mul_le_mul_of_nonneg_left hSx hL1_nonneg
          dsimp [ρ]
          linarith
        have hcast :
            ((((α : ℝ) * ‖x‖ + β : ℝ) : EReal)) ≤ (((ρ * ‖x‖ : ℝ) : EReal)) := by
          exact_mod_cast hreal
        have htail : (((ρ * ‖x‖ : ℝ) : EReal)) ≤ f.asEReal x := houtside x hSx
        have hscaled :
            ((scaledNormKernel α).asEReal x + (β : EReal)) ≤ (((ρ * ‖x‖ : ℝ) : EReal)) := by
          simpa [scaledNormKernel_apply, add_comm, add_left_comm, add_assoc] using hcast
        exact le_trans hscaled htail
    rcases
        (exists_affine_norm_lowerBound_iff_conjugate_boundedAbove_on_closedBall
          (H := H) f α).1 ⟨β, hminorant⟩ with
      ⟨M, hM⟩
    have hRα : R ≤ (α : ℝ) := by
      dsimp [α]
      exact le_max_left R 0
    refine ⟨M, ?_⟩
    intro u hu
    have hu_ball_R : u ∈ Metric.closedBall (0 : H) R := hR hu
    have hu_ball_α : u ∈ Metric.closedBall (0 : H) (α : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hu_ball_R ⊢
      exact le_trans hu_ball_R hRα
    exact hM u hu_ball_α
  · intro hbounded
    rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
    intro ξ
    have hα_pos : 0 < max ξ 0 + 1 := by
      linarith [le_max_right ξ 0]
    let α : NNReal := ⟨max ξ 0 + 1, le_of_lt hα_pos⟩
    rcases hbounded (Metric.closedBall (0 : H) (α : ℝ)) Metric.isBounded_closedBall with
      ⟨M, hM⟩
    have hα_le :
        (((α : ℝ) : EReal)) ≤
          Filter.liminf (fun x : H ↦ f.asEReal x / ‖x‖)
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) := by
      exact le_liminf_div_norm_of_conjugate_boundedAbove_on_closedBall (H := H) f α ⟨M, hM⟩
    have hξ_lt_α : (ξ : EReal) < (((α : ℝ) : EReal)) := by
      have hreal : ξ < (α : ℝ) := by
        dsimp [α]
        linarith [le_max_left ξ 0]
      exact_mod_cast hreal
    exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hξ_lt_α hα_le)

-- Proof sketch: apply the bounded-set hypothesis to each singleton `{u}`. Since a singleton is
-- bounded, `conjugate f u` is dominated by some real number, hence lies in the domain.
/-- Proposition 14 15 (2): if the Fenchel conjugate `f*` is bounded above on every bounded subset
of `H`, then `dom f* = H`. -/
theorem dom_conjugate_eq_univ_of_conjugate_boundedOnEveryBoundedSet
    (f : H → Set.Ioi (⊥ : EReal))
    (hbounded :
      ∀ B : Set H, Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, f.asEReal∗ u ≤ M) :
    dom f.asEReal∗ = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    -- A singleton is bounded, so the global hypothesis yields a finite real upper bound at `u`.
    have hsingleton : Bornology.IsBounded ({u} : Set H) := by
      exact Bornology.isBounded_singleton (x := u)
    rcases hbounded ({u} : Set H) hsingleton with ⟨M, hM⟩
    rw [mem_dom_iff]
    exact lt_of_le_of_lt (hM u (by simp)) (EReal.coe_lt_top M)

end Conjugation

end ERealFunction
