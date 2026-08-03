import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Proposition_12_14
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap13.Example_13_4
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap13.Proposition_13_29
import BauschkeLean.Chap14.Definition_14_6
import BauschkeLean.Chap14.Remark_14_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

-- Semantic recall note: Corollary 14.8 follows the textbook `Θ` route:
-- normalize `pav(f, g)` as `Θ(f, g) - q`, compute `Θ(f, g)∗`, and then transport the result
-- through Proposition 13.29 at `γ = 1`.

section ProximalAverage

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 14.8: the scalar `2 : ℝ` is nonzero. -/
lemma two_ne_zero_real : (2 : ℝ) ≠ 0 := by
  norm_num

/-- Helper for Corollary 14.8: multiplication by `2` is a continuous linear equivalence. -/
noncomputable abbrev double_scale_equiv : H ≃L[ℝ] H :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero_real)

/-- Helper for Corollary 14.8: adding a finite real constant commutes with an indexed infimum in
`EReal`. -/
lemma iInf_add_real_const (Φ : H → EReal) (c : ℝ) :
    (⨅ y : H, Φ y + ((c : ℝ) : EReal)) = (⨅ y : H, Φ y) + ((c : ℝ) : EReal) := by
  have hright :
      (⨅ y : H, Φ y) + ((c : ℝ) : EReal) ≤ (⨅ y : H, Φ y + ((c : ℝ) : EReal)) := by
    refine le_iInf fun y ↦ ?_
    exact add_le_add (iInf_le Φ y) le_rfl
  have hleft_sub :
      (⨅ y : H, Φ y + ((c : ℝ) : EReal)) - ((c : ℝ) : EReal) ≤ (⨅ y : H, Φ y) := by
    refine le_iInf fun y ↦ ?_
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).2
      (iInf_le (fun y ↦ Φ y + ((c : ℝ) : EReal)) y)
  have hleft :
      (⨅ y : H, Φ y + ((c : ℝ) : EReal)) ≤ (⨅ y : H, Φ y) + ((c : ℝ) : EReal) := by
    exact (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).1 hleft_sub
  exact le_antisymm hleft hright

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 14.8: the unit quadratic kernel belongs to `Γ₀(H)`. -/
lemma halfSquaredNorm_mem_gammaZero [NormedSpace ℝ H] :
    (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
  let q : H → ℝ := fun x : H ↦ ‖x‖ ^ 2 / 2
  have hq_eq :
      q.toEReal = (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    funext x
    simp [q, halfSquaredNorm, moreauQuadraticKernel, div_eq_mul_inv, mul_comm]
  rw [← hq_eq]
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha0 ha1
    have hnorm_sq :
        _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖ ^ 2) :=
      (convexOn_univ_norm :
          _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖)).pow
        (fun z _ ↦ norm_nonneg z) 2
    have hquad :
        ‖a • x + (1 - a) • y‖ ^ 2 / 2 ≤
          a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) := by
      have hquad' :
          ‖a • x + (1 - a) • y‖ ^ 2 ≤
            a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 := by
        simpa [smul_eq_mul] using
          hnorm_sq.2 (by simp) (by simp) ha0 (sub_nonneg.mpr ha1) (by ring)
      nlinarith
    change (((‖a • x + (1 - a) • y‖ ^ 2) / 2 : ℝ) : EReal) ≤
      ((a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) : ℝ) : EReal)
    exact_mod_cast hquad
  · have hcont : Continuous q := by
      simpa [q, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_norm.pow 2).const_mul (1 / 2 : ℝ)
    simpa [q] using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-- Helper for Corollary 14.8: the shifted owner `f + q` again belongs to `Γ₀(H)`. -/
lemma pointwiseAdd_halfSquaredNorm_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    f + halfSquaredNorm ∈ Γ₀(H) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  have hhalf_dom : x ∈ effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top _
  exact pointwiseAdd_mem_gammaZero
    f halfSquaredNorm hf halfSquaredNorm_mem_gammaZero ⟨x, hx, hhalf_dom⟩

/-- Helper for Corollary 14.8: every `Γ₀(H)` function has a global affine lower bound in the
norm. -/
lemma exists_linear_lower_bound_of_mem_gammaZero_local
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ R C : ℝ, 0 ≤ R ∧ ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)) := by
  rcases hf.2.nonempty with ⟨p, hp⟩
  let ξ : ℝ := (f p : EReal).toReal - 1
  have hp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
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
  refine ⟨δ⁻¹, 1 + ‖p‖ / δ - (f p : EReal).toReal, by positivity, ?_⟩
  intro x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    by_cases hnear : ‖x - p‖ < δ
    · -- Near the reference point `p`, the local strict lower bound already dominates the target.
      have hball : x ∈ Metric.ball p r := by
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
      exact le_trans hbound_ereal hξ_lt_fx.le
    · -- Far from `p`, convex interpolation moves back into the local neighborhood around `p`.
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
      have hy_bot : (f y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
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

/-- Helper for Corollary 14.8: a linear lower bound survives division by the norm on the tail
`‖x‖ ≥ 1`. -/
lemma linear_lower_bound_div_norm_local
    {f : H → Set.Ioi (⊥ : EReal)} {R C : ℝ}
    (hbound : ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)))
    {x : H} (hnorm : (1 : ℝ) ≤ ‖x‖) :
    ((-(R + |C|) : ℝ) : EReal) ≤ (f x : EReal) / ‖x‖ := by
  have hnorm_pos_real : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact EReal.coe_pos.2 hnorm_pos_real
  have hreal :
      (-(R + |C|)) * ‖x‖ ≤ -R * ‖x‖ - C := by
    have hC_le : C ≤ ‖x‖ * |C| := by
      have habs_le : |C| ≤ ‖x‖ * |C| := by
        simpa [one_mul, mul_comm] using mul_le_mul_of_nonneg_right hnorm (abs_nonneg C)
      exact le_trans (le_abs_self C) habs_le
    have hC_scaled : -(‖x‖ * |C|) ≤ -C := by
      simpa [mul_comm] using neg_le_neg hC_le
    calc
      (-(R + |C|)) * ‖x‖ = -(R * ‖x‖) + -(‖x‖ * |C|) := by ring
      _ ≤ -R * ‖x‖ - C := by linarith
  have hcast :
      ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hmul_le :
      ((((-(R + |C|) : ℝ) : EReal) * ‖x‖)) ≤ (f x : EReal) := by
    calc
      (((-(R + |C|) : ℝ) : EReal) * ‖x‖)
          = ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) := by
              rw [← EReal.coe_mul]
      _ ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := hcast
      _ ≤ (f x : EReal) := hbound x
  exact (EReal.le_div_iff_mul_le hnorm_pos (by simp)).2 hmul_le

/-- Helper for Corollary 14.8: adding a summand with a linear minorant preserves
supercoercivity of the dominant summand. -/
lemma pointwiseAdd_supercoercive_of_linear_lower_bound_local
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
    linear_lower_bound_div_norm_local hbound hnorm
  have hsum :
      (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) = (ξ : EReal) := by
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  have hquot_split :
      ((f + g).asEReal x) / ‖x‖ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by
    have hnorm_nonneg : (0 : EReal) ≤ (‖x‖ : EReal) := by
      exact_mod_cast norm_nonneg x
    rw [Function.asEReal_apply]
    simpa using
      (EReal.add_div_of_nonneg_right
        (a := (f x : EReal)) (b := (g x : EReal)) (c := (‖x‖ : EReal)) hnorm_nonneg)
  have hadd :
      (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) <
        (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := by
    have hright_bot : (f x : EReal) / ‖x‖ ≠ ⊥ := by
      exact ne_bot_of_le_ne_bot (by simp) hf_tail
    exact EReal.add_lt_add_of_lt_of_le' hxg hf_tail hright_bot (by
      intro _ hz
      exact (EReal.coe_ne_top _ hz).elim)
  calc
    (ξ : EReal)
        = (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) := hsum.symm
    _ < (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := hadd
    _ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by rw [add_comm]
    _ = ((f + g).asEReal x) / ‖x‖ := hquot_split.symm

/-- Helper for Corollary 14.8: the unit quadratic kernel is supercoercive. -/
lemma halfSquaredNorm_supercoercive_local :
    Supercoercive ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal) := by
  let pTwo : Set.Ici (1 : ℝ) := ⟨(2 : ℝ), by norm_num⟩
  have hpTwo : (1 : ℝ) < pTwo := by
    change (1 : ℝ) < (2 : ℝ)
    norm_num
  have hkernel_eq :
      normPowerKernel (H := H) pTwo (1 : PosReal) = halfSquaredNorm := by
    ext x
    rw [normPowerKernel_apply, halfSquaredNorm_apply]
    congr 1
    norm_num [Real.rpow_natCast]
  simpa [hkernel_eq] using
    (supercoercive_normPowerKernel (H := H) pTwo (1 : PosReal) hpTwo :
      Supercoercive ((normPowerKernel (H := H) pTwo (1 : PosReal) : H → Set.Ioi (⊥ : EReal)).asEReal))

/-- Helper for Corollary 14.8: the shifted owner `f + q` is supercoercive. -/
lemma pointwiseAdd_halfSquaredNorm_supercoercive
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Supercoercive (f + halfSquaredNorm).asEReal := by
  rcases exists_linear_lower_bound_of_mem_gammaZero_local hf with ⟨R, C, _, hbound⟩
  exact pointwiseAdd_supercoercive_of_linear_lower_bound_local
    ⟨R, C, hbound⟩ halfSquaredNorm_supercoercive_local

/-- Helper for Corollary 14.8: the infimal-convolution core `((f + q) □ (g + q))` is proper and
belongs to `Γ(H)`. -/
lemma proximal_average_theta_core_isProper_and_mem_gamma
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    IsProper ((f + halfSquaredNorm) □ (g + halfSquaredNorm)) ∧
      ((f + halfSquaredNorm) □ (g + halfSquaredNorm)) ∈ gamma H := by
  have hf_shift : f + halfSquaredNorm ∈ Γ₀(H) :=
    pointwiseAdd_halfSquaredNorm_mem_gammaZero f hf
  have hg_shift : g + halfSquaredNorm ∈ Γ₀(H) :=
    pointwiseAdd_halfSquaredNorm_mem_gammaZero g hg
  have hsuper : Supercoercive (f + halfSquaredNorm).asEReal :=
    pointwiseAdd_halfSquaredNorm_supercoercive f hf
  simpa using
    (isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
      (f := f + halfSquaredNorm)
      (g := g + halfSquaredNorm)
      (hf := hf_shift)
      (hg := hg_shift)
      (hcase := Or.inl hsuper))

/-- Helper for Corollary 14.8: the packaged core owner `((f + q) □ (g + q))`. -/
noncomputable abbrev proximal_average_theta_core
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi
    ((f + halfSquaredNorm) □ (g + halfSquaredNorm))
    (proximal_average_theta_core_isProper_and_mem_gamma f g hf hg).1

/-- Helper for Corollary 14.8: the raw textbook owner
`Θ(f, g) = (1 / 2) * ((f + q) □ (g + q)) ∘ (2 Id)`. -/
noncomputable abbrev proximal_average_theta
    (f g : H → Set.Ioi (⊥ : EReal)) (_hf : f ∈ Γ₀(H)) (_hg : g ∈ Γ₀(H)) :
    H → EReal :=
  fun x : H ↦
    ((1 / 2 : ℝ) : EReal) *
      (((f + halfSquaredNorm) □ (g + halfSquaredNorm)) ((2 : ℝ) • x))

/-- Helper for Corollary 14.8: the canonical `Γ₀(H)` packaging of `Θ(f, g)`. -/
noncomputable abbrev proximal_average_theta_packaged
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  ((((⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal) • proximal_average_theta_core f g hf hg) ∘
    double_scale_equiv))

/-- Helper for Corollary 14.8: coercing the packaged theta owner recovers the raw `Θ(f, g)`. -/
@[simp] lemma proximal_average_theta_packaged_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (x : H) :
    (proximal_average_theta_packaged f g hf hg x : EReal) = proximal_average_theta f g hf hg x := by
  simp [proximal_average_theta_packaged, proximal_average_theta, proximal_average_theta_core,
    Function.comp]

/-- Helper for Corollary 14.8: the packaged theta owner has the expected `EReal` coercion. -/
@[simp] lemma proximal_average_theta_packaged_asEReal
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (proximal_average_theta_packaged f g hf hg).asEReal = proximal_average_theta f g hf hg := by
  funext x
  simpa [Function.asEReal_apply] using proximal_average_theta_packaged_apply f g hf hg x

/-- Helper for Corollary 14.8: `Θ(f, g)` belongs to `Γ₀(H)`. -/
lemma proximal_average_theta_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    proximal_average_theta_packaged f g hf hg ∈ Γ₀(H) := by
  have hcore :
      proximal_average_theta_core f g hf hg ∈ Γ₀(H) := by
    exact properIoi_mem_gammaZero_of_mem_gamma
      (proximal_average_theta_core_isProper_and_mem_gamma f g hf hg).1
      (proximal_average_theta_core_isProper_and_mem_gamma f g hf hg).2
  have hscaled :
      (((⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal) • proximal_average_theta_core f g hf hg)) ∈
        Γ₀(H) := by
    simpa using
      (smul_mem_gammaZero
        (proximal_average_theta_core f g hf hg)
        hcore
        (⟨(1 / 2 : ℝ), one_half_pos⟩ : PosReal))
  simpa [proximal_average_theta_packaged] using
    (mem_gammaZero_comp_continuousLinearEquiv
      (hf := hscaled)
      (e := double_scale_equiv))

/-- Helper for Corollary 14.8: the midpoint quadratic identity
`q(y) + q(2x - y) = ‖x - y‖² + q(x)`. -/
lemma doubled_shift_quadratic_identity
    (x y : H) :
    ‖y‖ ^ 2 / 2 + ‖(2 : ℝ) • x - y‖ ^ 2 / 2 = ‖x - y‖ ^ 2 + ‖x‖ ^ 2 := by
  have hy : y = x + (y - x) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hy]
  have hshift : (2 : ℝ) • x - (x + (y - x)) = x - (y - x) := by
    simp [two_smul, sub_eq_add_neg, add_assoc]
  rw [hshift]
  have hright : x - (x + (y - x)) = -(y - x) := by
    simp [sub_eq_add_neg, add_assoc]
  rw [hright, norm_neg]
  have hadd : ‖x + (y - x)‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    simpa using norm_add_sq_real x (y - x)
  have hsub : ‖x - (y - x)‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    simpa using norm_sub_sq_real x (y - x)
  nlinarith

/-- Helper for Corollary 14.8: evaluating `Θ(f, g)` rewrites the shifted infimal-convolution
integrand into the midpoint form. -/
lemma proximal_average_theta_pointwise_normalization
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) (x : H) :
    proximal_average_theta f g hf hg x =
      ((1 / 2 : ℝ) : EReal) *
        (⨅ y : H, (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          (((‖x - y‖ ^ 2 + ‖x‖ ^ 2 : ℝ) : EReal))) := by
  rw [proximal_average_theta, infimalConvolution_apply]
  congr 1
  refine iInf_congr fun y ↦ ?_
  have hleft :
      ((pointwiseAdd f halfSquaredNorm y : Set.Ioi (⊥ : EReal)) : EReal) =
        (f y : EReal) + ((((‖y‖ ^ 2) / 2 : ℝ) : EReal)) := by
    simpa [halfSquaredNorm_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      pointwiseAdd_apply f halfSquaredNorm y
  have hright :
      ((pointwiseAdd g halfSquaredNorm ((2 : ℝ) • x - y) : Set.Ioi (⊥ : EReal)) : EReal) =
        (g ((2 : ℝ) • x - y) : EReal) +
          ((((‖(2 : ℝ) • x - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
    simpa [halfSquaredNorm_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      pointwiseAdd_apply g halfSquaredNorm ((2 : ℝ) • x - y)
  have hquad :
      ((((‖y‖ ^ 2) / 2 : ℝ) : EReal) +
          ((((‖(2 : ℝ) • x - y‖ ^ 2) / 2 : ℝ) : EReal))) =
        (((‖x - y‖ ^ 2 + ‖x‖ ^ 2 : ℝ) : EReal)) := by
    rw [← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ (t : EReal))
      (doubled_shift_quadratic_identity (x := x) (y := y))
  calc
    ((pointwiseAdd f halfSquaredNorm y : Set.Ioi (⊥ : EReal)) : EReal) +
        ((pointwiseAdd g halfSquaredNorm ((2 : ℝ) • x - y) : Set.Ioi (⊥ : EReal)) : EReal) =
        (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          ((((‖y‖ ^ 2) / 2 : ℝ) : EReal) +
            ((((‖(2 : ℝ) • x - y‖ ^ 2) / 2 : ℝ) : EReal))) := by
          rw [hleft, hright]
          simp [add_assoc, add_left_comm, add_comm]
    _ = (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
          (((‖x - y‖ ^ 2 + ‖x‖ ^ 2 : ℝ) : EReal)) := by
          rw [hquad]

/-- Helper for Corollary 14.8: multiplication by `1 / 2` distributes over adding a finite real
constant in `EReal`. -/
lemma ereal_one_half_mul_add_real_const
    (a : EReal) (c : ℝ) :
    ((1 / 2 : ℝ) : EReal) * (a + ((c : ℝ) : EReal)) =
      ((1 / 2 : ℝ) : EReal) * a + (((c / 2 : ℝ) : EReal)) := by
  have hhalf_nonneg : (0 : EReal) ≤ (((1 / 2 : ℝ) : EReal)) := by
    exact_mod_cast (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
  calc
    ((1 / 2 : ℝ) : EReal) * (a + ((c : ℝ) : EReal)) =
        ((1 / 2 : ℝ) : EReal) * a + ((1 / 2 : ℝ) : EReal) * ((c : ℝ) : EReal) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg (EReal.coe_ne_top (1 / 2 : ℝ))]
    _ = ((1 / 2 : ℝ) : EReal) * a + (((c / 2 : ℝ) : EReal)) := by
          congr 1
          rw [← EReal.coe_mul]
          norm_num [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Corollary 14.8: the source identity `Θ(f, g) = pav(f, g) + q`. -/
lemma proximal_average_theta_eq_add_halfSquaredNorm
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    proximal_average_theta f g hf hg =
      fun x : H ↦ pav(f, g) x + halfSquaredNorm.asEReal x := by
  funext x
  calc
    proximal_average_theta f g hf hg x =
        ((1 / 2 : ℝ) : EReal) *
          (⨅ y : H, ((f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
              (((‖x - y‖ ^ 2 : ℝ) : EReal))) + ((‖x‖ ^ 2 : ℝ) : EReal)) := by
            rw [proximal_average_theta_pointwise_normalization f g hf hg]
            congr 1
            refine iInf_congr fun y ↦ ?_
            rw [EReal.coe_add]
            ac_rfl
    _ = ((1 / 2 : ℝ) : EReal) *
          ((⨅ y : H, (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
              (((‖x - y‖ ^ 2 : ℝ) : EReal))) + ((‖x‖ ^ 2 : ℝ) : EReal)) := by
            rw [iInf_add_real_const
              (Φ := fun y : H ↦ (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
                (((‖x - y‖ ^ 2 : ℝ) : EReal)))
              (c := ‖x‖ ^ 2)]
    _ = ((1 / 2 : ℝ) : EReal) *
          (⨅ y : H, (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
            (((‖x - y‖ ^ 2 : ℝ) : EReal))) + (((‖x‖ ^ 2) / 2 : ℝ) : EReal) := by
            rw [ereal_one_half_mul_add_real_const]
    _ = pav(f, g) x + (((‖x‖ ^ 2) / 2 : ℝ) : EReal) := by
          rw [proximalAverage_apply]
    _ = pav(f, g) x + halfSquaredNorm.asEReal x := by
          rw [Function.asEReal_apply, halfSquaredNorm_apply]

/-- Helper for Corollary 14.8: the normalized form `pav(f, g) = Θ(f, g) - q`. -/
lemma proximal_average_eq_theta_sub_halfSquaredNorm
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g) =
      fun x : H ↦ proximal_average_theta f g hf hg x - halfSquaredNorm.asEReal x := by
  funext x
  rw [congrFun (proximal_average_theta_eq_add_halfSquaredNorm f g hf hg) x]
  rw [Function.asEReal_apply, halfSquaredNorm_apply]
  simpa using
    (EReal.add_sub_cancel_right (a := pav(f, g) x) (b := ‖x‖ ^ (2 : ℕ) / 2)).symm

/-- Helper for Corollary 14.8: `(f + q)^*` is the unit Moreau envelope of `f^*`. -/
lemma conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (f + halfSquaredNorm).asEReal∗ = {}^[(1 : PosReal)] (gammaZeroConjugate f hf) := by
  let fstar := gammaZeroConjugate f hf
  have hfstar : fstar ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hmoreau :
      IsProper ({}^[(1 : PosReal)] fstar) ∧ ({}^[(1 : PosReal)] fstar) ∈ gamma H := by
    -- The unit Moreau envelope of `f*` is proper because the quadratic kernel is supercoercive.
    simpa [moreauEnvelope, infimalConvolution_comm] using
      (isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
        (f := halfSquaredNorm)
        (g := fstar)
        (hf := halfSquaredNorm_mem_gammaZero)
        (hg := hfstar)
        (hcase := Or.inl halfSquaredNorm_supercoercive_local))
  have hmoreau_biconj :
      ({}^[(1 : PosReal)] fstar)∗∗ = {}^[(1 : PosReal)] fstar :=
    (mem_gamma_iff_eq_biconjugate_of_is_proper hmoreau.1).mp hmoreau.2
  have hfstar_conj : fstar.asEReal∗ = f.asEReal := by
    funext x
    simpa [fstar] using congrFun (biconjugate_eq_of_mem_gammaZero hf) x
  have hconj_moreau :
      ({}^[(1 : PosReal)] fstar)∗ = (f + halfSquaredNorm).asEReal := by
    -- Compute the conjugate of the Moreau envelope of `f*`, then collapse the biconjugate of `f`.
    have htmp : ({}^[(1 : PosReal)] fstar)∗ = f.asEReal + halfSquaredNorm.asEReal := by
      calc
        ({}^[(1 : PosReal)] fstar)∗ = fstar.asEReal∗ + halfSquaredNorm.asEReal := by
          simpa using conjugate_moreauEnvelope_eq (f := fstar) (γ := (1 : PosReal))
        _ = f.asEReal + halfSquaredNorm.asEReal := by
          rw [hfstar_conj]
    simpa [Function.asEReal_apply, Pi.add_apply] using htmp
  -- Fenchel--Moreau on the proper Moreau envelope turns the previous conjugate computation around.
  calc
    (f + halfSquaredNorm).asEReal∗ = (({}^[(1 : PosReal)] fstar)∗)∗ := by
      rw [hconj_moreau]
    _ = ({}^[(1 : PosReal)] fstar)∗∗ := rfl
    _ = {}^[(1 : PosReal)] fstar := hmoreau_biconj
    _ = {}^[(1 : PosReal)] (gammaZeroConjugate f hf) := rfl

/-- Helper for Corollary 14.8: the unit Moreau envelope of a `Γ₀(H)` function is finite. -/
lemma unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero_local
    (h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (x : H) :
    ({}^[(1 : PosReal)] h) x ≠ ⊤ ∧ ({}^[(1 : PosReal)] h) x ≠ ⊥ := by
  have hmoreau_proper :
      IsProper ({}^[(1 : PosReal)] h) := by
    -- Properness supplies the global `≠ ⊥` branch for the unit Moreau envelope.
    simpa [moreauEnvelope, infimalConvolution_comm] using
      (isProper_and_mem_gamma_infimalConvolution_of_supercoercive_or_coercive_bddBelow
        (f := halfSquaredNorm)
        (g := h)
        (hf := halfSquaredNorm_mem_gammaZero)
        (hg := hh)
        (hcase := Or.inl halfSquaredNorm_supercoercive_local)).1
  rcases hh.2.nonempty with ⟨y, hy⟩
  have hy_top : (h y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hupper :
      ({}^[(1 : PosReal)] h) x ≤
        (h y : EReal) + ((((‖x - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
    -- Evaluate the defining infimum at one finite point of `h`.
    have hupper' :
        ({}^[(1 : PosReal)] h) x ≤
          (h y : EReal) +
            ((((1 / (2 * (1 : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
      rw [moreauEnvelope_apply]
      exact
        iInf_le
          (fun z : H ↦
            (h z : EReal) + ((((1 / (2 * (1 : ℝ))) * ‖x - z‖ ^ 2 : ℝ) : EReal)))
          y
    have hcoeff :
        ((((1 / (2 * (1 : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) =
          ((((‖x - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
      simpa using half_squared_norm_cast_at_one (x := x - y)
    exact hupper'.trans_eq (by rw [hcoeff])
  have hsum_ne_top :
      (h y : EReal) + ((((‖x - y‖ ^ 2) / 2 : ℝ) : EReal)) ≠ ⊤ :=
    EReal.add_ne_top hy_top (EReal.coe_ne_top _)
  constructor
  · intro htop
    exact hsum_ne_top (top_unique (htop ▸ hupper))
  · exact hmoreau_proper.1 x

/-- Helper for Corollary 14.8: subtracting the half-sum of two finite `EReal` values from a real
base splits into the half-sum of the corresponding defects. -/
lemma ereal_real_sub_half_sum
    (r : ℝ) (a b : EReal)
    (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥) :
    ((r : EReal) - (((1 / 2 : ℝ) : EReal) * a + ((1 / 2 : ℝ) : EReal) * b)) =
      ((1 / 2 : ℝ) : EReal) * ((r : EReal) - a) +
        ((1 / 2 : ℝ) : EReal) * ((r : EReal) - b) := by
  have hreal :
      r - ((1 / 2 : ℝ) * a.toReal + (1 / 2 : ℝ) * b.toReal) =
        (1 / 2 : ℝ) * (r - a.toReal) + (1 / 2 : ℝ) * (r - b.toReal) := by
    ring
  -- Convert the finite `EReal` values back to reals and finish by scalar arithmetic.
  calc
    ((r : EReal) - (((1 / 2 : ℝ) : EReal) * a + ((1 / 2 : ℝ) : EReal) * b)) =
        (((r - ((1 / 2 : ℝ) * a.toReal + (1 / 2 : ℝ) * b.toReal) : ℝ) : EReal)) := by
          rw [← EReal.coe_toReal ha_top ha_bot, ← EReal.coe_toReal hb_top hb_bot,
            ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub]
          simp
    _ =
        ((((1 / 2 : ℝ) * (r - a.toReal) + (1 / 2 : ℝ) * (r - b.toReal) : ℝ) : EReal)) := by
          exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    _ = ((1 / 2 : ℝ) : EReal) * ((r : EReal) - a) +
          ((1 / 2 : ℝ) : EReal) * ((r : EReal) - b) := by
          rw [← EReal.coe_toReal ha_top ha_bot, ← EReal.coe_toReal hb_top hb_bot,
            ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul,
            ← EReal.coe_add]
          simp

/-- Helper for Corollary 14.8: the conjugate of `Θ(f, g)` is the half-sum of the unit Moreau
envelopes of `f^*` and `g^*`. -/
lemma conjugate_proximal_average_theta_eq_half_sum_unitMoreau
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (proximal_average_theta f g hf hg)∗ =
      fun u : H ↦
        ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) u +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) u := by
  let α : Set.Ioi (0 : ℝ) := ⟨(1 / 2 : ℝ), by simpa using one_half_pos⟩
  have hcore_conj :
      (proximal_average_theta_core f g hf hg).asEReal∗ =
        (f + halfSquaredNorm).asEReal∗ + (g + halfSquaredNorm).asEReal∗ := by
    have hcore_eq :
        (proximal_average_theta_core f g hf hg).asEReal =
          ((f + halfSquaredNorm) □ (g + halfSquaredNorm)) := rfl
    -- Compute the conjugate at the infimal-convolution core before reintroducing the outer
    -- scaling and precomposition.
    rw [hcore_eq]
    exact conjugate_infimalConvolution_eq (f + halfSquaredNorm) (g + halfSquaredNorm)
  have hf_conj :
      (f + halfSquaredNorm).asEReal∗ = {}^[(1 : PosReal)] (gammaZeroConjugate f hf) :=
    conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate f hf
  have hg_conj :
      (g + halfSquaredNorm).asEReal∗ = {}^[(1 : PosReal)] (gammaZeroConjugate g hg) :=
    conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate g hg
  have hhalf_nonneg : (0 : EReal) ≤ ((α : ℝ) : EReal) := by
    exact_mod_cast (show (0 : ℝ) ≤ (α : ℝ) by exact le_of_lt α.2)
  have htheta_eq :
      proximal_average_theta f g hf hg =
        fun x : H ↦
          ((α : ℝ) : EReal) *
            (proximal_average_theta_core f g hf hg).asEReal (((α : ℝ)⁻¹) • x) := by
    funext x
    simp [proximal_average_theta, α, proximal_average_theta_core, Function.asEReal_apply]
  ext u
  -- Route correction: conjugate the already-packaged core first, then add back the outer
  -- positive scaling and inverse homothety in one Proposition 13.23 step.
  calc
    (proximal_average_theta f g hf hg)∗ u =
        ((α : ℝ) : EReal) * ((proximal_average_theta_core f g hf hg).asEReal∗ u) := by
          rw [htheta_eq]
          simpa using
            congrFun
              (conjugate_pos_smul_precompose_inv_smul
                (f := (proximal_average_theta_core f g hf hg).asEReal)
                α)
              u
    _ = ((α : ℝ) : EReal) *
          (((f + halfSquaredNorm).asEReal∗ + (g + halfSquaredNorm).asEReal∗) u) := by
            rw [hcore_conj]
    _ = ((α : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) u +
          ((α : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) u := by
            rw [Pi.add_apply, hf_conj, hg_conj,
              EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg (EReal.coe_ne_top (α : ℝ))]
    _ = ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) u +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) u := by
            simp [α]

/-- Helper for Corollary 14.8: the packaged biconjugate owner recovers the original `Γ₀(H)`
function. -/
lemma gammaZeroConjugate_gammaZeroConjugate_eq
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    gammaZeroConjugate
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate_mem_gammaZero hf) =
      f := by
  -- The packaged double conjugate agrees pointwise with the Fenchel biconjugate of `f`.
  funext x
  apply Subtype.ext
  simpa using congrFun (biconjugate_eq_of_mem_gammaZero hf) x

/-- Helper for Corollary 14.8: the unit quadratic gap against the Moreau envelope of `f*`
recovers the unit Moreau envelope of `f`. -/
lemma halfSquaredNorm_sub_unitMoreauEnvelope_gammaZeroConjugate_eq_unitMoreauEnvelope
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (fun x : H ↦ halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x) =
      {}^[(1 : PosReal)] f := by
  funext x
  -- Route correction: identify the quadratic-minus-envelope surface through Example 13.4 and
  -- then rewrite the resulting conjugate back through the local `(f + q)^* = e_1(f*)` bridge.
  calc
    halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x =
        (((gammaZeroConjugate f hf + halfSquaredNorm).asEReal)∗) x := by
          simpa [Function.asEReal_apply, halfSquaredNorm_apply] using
            (congrFun
              (conjugate_regularized_eq_scaledQuadratic_sub_moreauEnvelope
                (φ := gammaZeroConjugate f hf)
                (γ := (1 : PosReal)))
              x).symm
    _ =
        ({}^[(1 : PosReal)]
          (gammaZeroConjugate
            (gammaZeroConjugate f hf)
            (gammaZeroConjugate_mem_gammaZero hf))) x := by
          simpa using
            congrFun
              (conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate
                (f := gammaZeroConjugate f hf)
                (hf := gammaZeroConjugate_mem_gammaZero hf))
              x
    _ = ({}^[(1 : PosReal)] f) x := by
          rw [gammaZeroConjugate_gammaZeroConjugate_eq f hf]

/-- Helper for Corollary 14.8: the inner `q - Θ(f, g)^*` term in Proposition 13.29 is exactly
the conjugate of `Θ(f^*, g^*)`. -/
lemma halfSquaredNorm_sub_conjugate_proximal_average_theta_eq_conjugate_proximal_average_theta_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    (fun x : H ↦ halfSquaredNorm.asEReal x - (proximal_average_theta f g hf hg)∗ x) =
      (proximal_average_theta
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate g hg)
        (gammaZeroConjugate_mem_gammaZero hf)
        (gammaZeroConjugate_mem_gammaZero hg))∗ := by
  ext x
  have hleft_theta :
      (proximal_average_theta f g hf hg)∗ x =
        ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x := by
    exact
      congrFun
        (conjugate_proximal_average_theta_eq_half_sum_unitMoreau f g hf hg)
        x
  have hright_theta :
      (proximal_average_theta
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate g hg)
        (gammaZeroConjugate_mem_gammaZero hf)
        (gammaZeroConjugate_mem_gammaZero hg))∗ x =
        ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] f) x +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] g) x := by
    -- Collapse the double conjugates on the right-hand `Θ`-term back to `f` and `g`.
    simpa [gammaZeroConjugate_gammaZeroConjugate_eq f hf,
      gammaZeroConjugate_gammaZeroConjugate_eq g hg] using
      congrFun
        (conjugate_proximal_average_theta_eq_half_sum_unitMoreau
          (gammaZeroConjugate f hf)
          (gammaZeroConjugate g hg)
          (gammaZeroConjugate_mem_gammaZero hf)
          (gammaZeroConjugate_mem_gammaZero hg))
        x
  have hf_unit_finite :=
    unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero_local
      (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf) x
  have hg_unit_finite :=
    unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero_local
      (gammaZeroConjugate g hg) (gammaZeroConjugate_mem_gammaZero hg) x
  rcases hf_unit_finite with ⟨hf_unit_top, hf_unit_bot⟩
  rcases hg_unit_finite with ⟨hg_unit_top, hg_unit_bot⟩
  have hsplit :
      halfSquaredNorm.asEReal x -
          (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x +
            ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x) =
        ((1 / 2 : ℝ) : EReal) *
            (halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x) +
          ((1 / 2 : ℝ) : EReal) *
            (halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x) := by
    -- Convert the finite envelope values to reals so the half-sum subtraction is a scalar
    -- arithmetic identity.
    rw [Function.asEReal_apply, halfSquaredNorm_apply]
    exact
      ereal_real_sub_half_sum
        (((‖x‖ ^ 2) / 2 : ℝ))
        (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x)
        (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x)
        hf_unit_top hf_unit_bot hg_unit_top hg_unit_bot
  have hf_gap :
      halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x =
        ({}^[(1 : PosReal)] f) x := by
    exact
      congrFun
        (halfSquaredNorm_sub_unitMoreauEnvelope_gammaZeroConjugate_eq_unitMoreauEnvelope f hf)
        x
  have hg_gap :
      halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x =
        ({}^[(1 : PosReal)] g) x := by
    exact
      congrFun
        (halfSquaredNorm_sub_unitMoreauEnvelope_gammaZeroConjugate_eq_unitMoreauEnvelope g hg)
        x
  calc
    halfSquaredNorm.asEReal x - (proximal_average_theta f g hf hg)∗ x =
        halfSquaredNorm.asEReal x -
          (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x +
            ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x) := by
          rw [hleft_theta]
    _ = ((1 / 2 : ℝ) : EReal) *
            (halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x) +
          ((1 / 2 : ℝ) : EReal) *
            (halfSquaredNorm.asEReal x - ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x) := by
          exact hsplit
    _ = ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] f) x +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] g) x := by
          rw [hf_gap, hg_gap]
    _ =
        (proximal_average_theta
          (gammaZeroConjugate f hf)
          (gammaZeroConjugate g hg)
          (gammaZeroConjugate_mem_gammaZero hf)
          (gammaZeroConjugate_mem_gammaZero hg))∗ x := by
          exact hright_theta.symm

/-- Helper for Corollary 14.8: the Fenchel conjugate of the proximal average is the proximal
average of the Fenchel conjugates. -/
lemma proximal_average_conjugate_eq_proximal_average_conjugates
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g)∗ =
      pav(gammaZeroConjugate f hf, gammaZeroConjugate g hg) := by
  have htheta_gammaZero :
      proximal_average_theta_packaged f g hf hg ∈ Γ₀(H) :=
    proximal_average_theta_mem_gammaZero f g hf hg
  have htheta_proper :
      IsProper (proximal_average_theta_packaged f g hf hg).asEReal :=
    isProper_of_mem_gammaZero htheta_gammaZero
  have htheta_conj_gammaZero :
      proximal_average_theta_packaged
          (gammaZeroConjugate f hf)
          (gammaZeroConjugate g hg)
          (gammaZeroConjugate_mem_gammaZero hf)
          (gammaZeroConjugate_mem_gammaZero hg) ∈ Γ₀(H) :=
    proximal_average_theta_mem_gammaZero
      (gammaZeroConjugate f hf)
      (gammaZeroConjugate g hg)
      (gammaZeroConjugate_mem_gammaZero hf)
      (gammaZeroConjugate_mem_gammaZero hg)
  have hinner_conj :
      (fun v : H ↦ halfSquaredNorm.asEReal v - (proximal_average_theta f g hf hg)∗ v)∗ =
        proximal_average_theta
          (gammaZeroConjugate f hf)
          (gammaZeroConjugate g hg)
          (gammaZeroConjugate_mem_gammaZero hf)
          (gammaZeroConjugate_mem_gammaZero hg) := by
    -- Transport `q - Θ(f, g)^*` to the conjugate-side `Θ`, then collapse the resulting
    -- biconjugate through the packaged `Γ₀(H)` owner.
    calc
      (fun v : H ↦ halfSquaredNorm.asEReal v - (proximal_average_theta f g hf hg)∗ v)∗ =
          ((proximal_average_theta_packaged
              (gammaZeroConjugate f hf)
              (gammaZeroConjugate g hg)
              (gammaZeroConjugate_mem_gammaZero hf)
              (gammaZeroConjugate_mem_gammaZero hg)).asEReal∗)∗ := by
            rw [halfSquaredNorm_sub_conjugate_proximal_average_theta_eq_conjugate_proximal_average_theta_conjugates,
              proximal_average_theta_packaged_asEReal]
      _ =
          (proximal_average_theta_packaged
            (gammaZeroConjugate f hf)
            (gammaZeroConjugate g hg)
            (gammaZeroConjugate_mem_gammaZero hf)
            (gammaZeroConjugate_mem_gammaZero hg)).asEReal := by
              exact biconjugate_eq_of_mem_gammaZero htheta_conj_gammaZero
      _ =
          proximal_average_theta
            (gammaZeroConjugate f hf)
            (gammaZeroConjugate g hg)
            (gammaZeroConjugate_mem_gammaZero hf)
            (gammaZeroConjugate_mem_gammaZero hg) := by
              exact proximal_average_theta_packaged_asEReal
                (gammaZeroConjugate f hf)
                (gammaZeroConjugate g hg)
                (gammaZeroConjugate_mem_gammaZero hf)
                (gammaZeroConjugate_mem_gammaZero hg)
  -- Route correction: apply Proposition 13.29 only after packaging `Θ(f, g)` as a `Γ₀(H)`
  -- owner, so the source-side `q - Θ(f, g)^*` term can be biconjugated back cleanly.
  calc
    pav(f, g)∗ =
        (fun x : H ↦
          ((1 : ℝ) : EReal) * (proximal_average_theta_packaged f g hf hg).asEReal x -
            halfSquaredNorm.asEReal x)∗ := by
          congr 1
          funext x
          rw [proximal_average_eq_theta_sub_halfSquaredNorm f g hf hg,
            proximal_average_theta_packaged_asEReal]
          simp
    _ =
        fun u : H ↦
          ((1 : ℝ) : EReal) *
              ((fun v : H ↦
                  ((1 : ℝ) : EReal) * halfSquaredNorm.asEReal v -
                    (proximal_average_theta_packaged f g hf hg).asEReal∗ v)∗ u) -
            halfSquaredNorm.asEReal u := by
              simpa using
                conjugate_smul_sub_halfSquaredNorm_eq
                  (f := proximal_average_theta_packaged f g hf hg)
                  (γ := (1 : PosReal))
                  htheta_proper
    _ =
        fun u : H ↦
          ((fun v : H ↦ halfSquaredNorm.asEReal v - (proximal_average_theta f g hf hg)∗ v)∗ u) -
            halfSquaredNorm.asEReal u := by
              congr with u
              rw [proximal_average_theta_packaged_asEReal]
              simp
    _ =
        fun u : H ↦
          proximal_average_theta
              (gammaZeroConjugate f hf)
              (gammaZeroConjugate g hg)
              (gammaZeroConjugate_mem_gammaZero hf)
              (gammaZeroConjugate_mem_gammaZero hg) u -
            halfSquaredNorm.asEReal u := by
              congr with u
              rw [hinner_conj]
    _ =
        pav(gammaZeroConjugate f hf, gammaZeroConjugate g hg) := by
          symm
          exact proximal_average_eq_theta_sub_halfSquaredNorm
            (gammaZeroConjugate f hf)
            (gammaZeroConjugate g hg)
            (gammaZeroConjugate_mem_gammaZero hf)
            (gammaZeroConjugate_mem_gammaZero hg)

/-- Helper for Corollary 14.8: affine lower bounds for `f` and `g` induce a uniform lower bound
on the single-variable midpoint integrand defining `pav(f, g)`. -/
lemma proximal_average_midpoint_integrand_lower_bound
    (f g : H → Set.Ioi (⊥ : EReal))
    {Rf Cf Rg Cg : ℝ} (hRf : 0 ≤ Rf) (hRg : 0 ≤ Rg)
    (hf_lower : ∀ u : H, (((-Rf * ‖u‖ - Cf : ℝ) : EReal) ≤ (f u : EReal)))
    (hg_lower : ∀ u : H, (((-Rg * ‖u‖ - Cg : ℝ) : EReal) ≤ (g u : EReal)))
    (x y : H) :
    ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
      (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal) := by
  let z : H := (2 : ℝ) • x - y
  let d : ℝ := ‖x - y‖
  -- Control both endpoint norms by the center norm plus the displacement norm.
  have hy_norm : ‖y‖ ≤ ‖x‖ + d := by
    calc
      ‖y‖ = ‖x + (y - x)‖ := by
        congr 1
        abel_nf
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ = ‖x‖ + d := by
        simp [d, norm_sub_rev]
  have hz_norm : ‖z‖ ≤ ‖x‖ + d := by
    calc
      ‖z‖ = ‖x + (x - y)‖ := by
        dsimp [z]
        congr 1
        simp [two_smul, sub_eq_add_neg, add_assoc]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_add_le _ _
      _ = ‖x‖ + d := by
        simp [d]
  -- Absorb the linear tail in `d` with the completed square `(d - (Rf + Rg) / 2)^2`.
  have hreal :
      -(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) ≤
        (-Rf * ‖y‖ - Cf) + (-Rg * ‖z‖ - Cg) + d ^ 2 := by
    have hd_nonneg : 0 ≤ d := by
      simp [d]
    have hsquare : 0 ≤ (d - (Rf + Rg) / 2) ^ 2 := sq_nonneg _
    nlinarith [hy_norm, hz_norm, hRf, hRg, hd_nonneg, hsquare]
  have hreal_cast :
      ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
        (((-Rf * ‖y‖ - Cf) + (-Rg * ‖z‖ - Cg) + d ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hreal
  have hreal_sum :
      ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
        (((-Rf * ‖y‖ - Cf : ℝ) : EReal) + ((-Rg * ‖z‖ - Cg : ℝ) : EReal) +
          ((d ^ 2 : ℝ) : EReal)) := by
    simpa [EReal.coe_add, add_assoc] using hreal_cast
  have hmajorized :
      (((-Rf * ‖y‖ - Cf : ℝ) : EReal) + ((-Rg * ‖z‖ - Cg : ℝ) : EReal) +
          ((d ^ 2 : ℝ) : EReal)) ≤
        (f y : EReal) + (g z : EReal) + ((d ^ 2 : ℝ) : EReal) := by
    exact add_le_add (add_le_add (hf_lower y) (hg_lower z)) le_rfl
  exact le_trans hreal_sum (by simpa [z, d, add_assoc] using hmajorized)

/-- Helper for Corollary 14.8: the proximal average is proper as an `EReal`-valued function. -/
theorem isProper_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    IsProper (pav(f, g)) := by
  rcases exists_linear_lower_bound_of_mem_gammaZero_local hf with ⟨Rf, Cf, hRf, hf_lower⟩
  rcases exists_linear_lower_bound_of_mem_gammaZero_local hg with ⟨Rg, Cg, hRg, hg_lower⟩
  refine ⟨?_, ?_⟩
  · intro x
    let lowerConst : ℝ :=
      (1 / 2 : ℝ) * (-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4))
    -- Push the affine lower bound through the defining infimum formula for `pav(f, g)`.
    have hinf_lower :
        ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
          ⨅ y : H,
            (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal) := by
      refine le_iInf fun y ↦ ?_
      exact proximal_average_midpoint_integrand_lower_bound
        f g hRf hRg hf_lower hg_lower x y
    have hhalf_nonneg : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
      exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have hlower :
        ((lowerConst : EReal) ≤ pav(f, g) x) := by
      have hscaled_lower :
          (((1 / 2 : ℝ) : EReal) *
              ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal)) ≤
            ((1 / 2 : ℝ) : EReal) *
              (⨅ y : H,
                (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal)) :=
        mul_le_mul_of_nonneg_left hinf_lower hhalf_nonneg
      calc
        (lowerConst : EReal) =
            (((1 / 2 : ℝ) : EReal) *
              ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal)) := by
                simp [lowerConst, EReal.coe_mul]
        _ ≤ ((1 / 2 : ℝ) : EReal) *
              (⨅ y : H,
                (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal)) :=
              hscaled_lower
        _ = pav(f, g) x := by
              rw [proximalAverage_apply]
    have hbound_lt : (⊥ : EReal) < (lowerConst : EReal) := by
      exact EReal.bot_lt_coe _
    exact ne_of_gt (lt_of_lt_of_le hbound_lt hlower)
  · rcases hf.2.nonempty with ⟨y, hy⟩
    rcases hg.2.nonempty with ⟨z, hz⟩
    let x : H := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z
    refine ⟨x, ?_⟩
    rw [mem_dom_iff, proximalAverage_apply_eq_iInf_parameterized]
    have hle :
        (⨅ u : H, (proximalAverageKernel f g (u, (2 : ℝ) • x - u) : EReal)) ≤
          (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) :=
      iInf_le (fun u : H ↦ (proximalAverageKernel f g (u, (2 : ℝ) • x - u) : EReal)) y
    have hcompanion : (2 : ℝ) • x - y = z := by
      dsimp [x]
      simp [two_smul, smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hz_top : (g z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hkernel_lt :
        (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) < ⊤ := by
      rw [hcompanion, proximalAverageKernel_apply, lt_top_iff_ne_top]
      have hhalf_f_ne_top :
          (((1 / 2 : ℝ) : EReal) * (f y : EReal)) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl ?_,
          Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hy_top⟩
        exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      have hhalf_g_ne_top :
          (((1 / 2 : ℝ) : EReal) * (g z : EReal)) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl ?_,
          Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hz_top⟩
        exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      have hsum_ne_top :
          (((1 / 2 : ℝ) : EReal) * (f y : EReal)) +
            (((1 / 2 : ℝ) : EReal) * (g z : EReal)) +
            ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊤ := by
        have hfg_ne_top :
            (((1 / 2 : ℝ) : EReal) * (f y : EReal)) +
              (((1 / 2 : ℝ) : EReal) * (g z : EReal)) ≠ ⊤ :=
          EReal.add_ne_top hhalf_f_ne_top hhalf_g_ne_top
        exact EReal.add_ne_top hfg_ne_top (EReal.coe_ne_top _)
      simpa [add_assoc] using hsum_ne_top
    exact lt_of_le_of_lt hle hkernel_lt

/-- Corollary 14.8 (1): if `f, g ∈ Γ₀(H)`, then the canonical `Γ₀(H)` packaging
of `pav(f, g)` again belongs to `Γ₀(H)`. -/
theorem proximalAverage_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg) ∈ Γ₀(H) := by
  have hpav_proper : IsProper (pav(f, g)) :=
    isProper_proximalAverage f g hf hg
  have hpav_biconj :
      pav(f, g)∗∗ = pav(f, g) := by
    -- Apply clause (ii) twice and collapse the double conjugates of `f` and `g`.
    calc
      pav(f, g)∗∗ =
          pav(gammaZeroConjugate f hf, gammaZeroConjugate g hg)∗ := by
            rw [proximal_average_conjugate_eq_proximal_average_conjugates f g hf hg]
      _ =
          pav(
            gammaZeroConjugate (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf),
            gammaZeroConjugate (gammaZeroConjugate g hg) (gammaZeroConjugate_mem_gammaZero hg)) := by
              exact proximal_average_conjugate_eq_proximal_average_conjugates
                (gammaZeroConjugate f hf)
                (gammaZeroConjugate g hg)
                (gammaZeroConjugate_mem_gammaZero hf)
                (gammaZeroConjugate_mem_gammaZero hg)
      _ = pav(f, g) := by
            rw [gammaZeroConjugate_gammaZeroConjugate_eq f hf,
              gammaZeroConjugate_gammaZeroConjugate_eq g hg]
  have hpav_gamma : pav(f, g) ∈ gamma H :=
    (mem_gamma_iff_eq_biconjugate_of_is_proper hpav_proper).2 hpav_biconj
  exact properIoi_mem_gammaZero_of_mem_gamma hpav_proper hpav_gamma

/-- Corollary 14.8 (2): the Fenchel conjugate of the proximal average is the proximal average of
the Fenchel conjugates. -/
theorem gammaZeroConjugate_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g)∗ =
      pav(gammaZeroConjugate f hf, gammaZeroConjugate g hg) := by
  -- Reuse the local conjugacy engine proved in the source order above.
  exact proximal_average_conjugate_eq_proximal_average_conjugates f g hf hg

/-- Helper for Corollary 14.8: at `γ = 1`, the Moreau envelope is exactly infimal convolution
with `halfSquaredNorm`. -/
lemma unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one
    (h : H → Set.Ioi (⊥ : EReal)) :
    {}^[(1 : PosReal)] h = h □ halfSquaredNorm := by
  -- Normalize the unit quadratic kernel directly to the raw `q = (1 / 2) ‖·‖²` kernel.
  funext x
  rw [moreauEnvelope_apply, infimalConvolution_apply]
  refine iInf_congr fun y ↦ ?_
  rw [halfSquaredNorm_apply]
  simpa using
    congrArg
      (fun t : EReal ↦ (h y : EReal) + t)
      (half_squared_norm_cast_at_one (x := x - y))

/-- Helper for Corollary 14.8: the unit Moreau envelope of `(pav(f, g))^*` is the arithmetic
mean of the unit Moreau envelopes of `f^*` and `g^*`. -/
lemma proximal_average_conjugate_moreau_identity
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g)∗ □ halfSquaredNorm =
      fun x : H ↦
        ((1 / 2 : ℝ) : EReal) * (gammaZeroConjugate f hf □ halfSquaredNorm) x +
          ((1 / 2 : ℝ) : EReal) * (gammaZeroConjugate g hg □ halfSquaredNorm) x := by
  let pavOwner : H → Set.Ioi (⊥ : EReal) :=
    properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg)
  have hpav : pavOwner ∈ Γ₀(H) := proximalAverage_mem_gammaZero f g hf hg
  have hpav_unit :
      {}^[(1 : PosReal)] (gammaZeroConjugate pavOwner hpav) =
        pav(f, g)∗ □ halfSquaredNorm := by
    -- Route correction: first rewrite the unit Moreau envelope of the packaged conjugate owner
    -- back to the raw `□ q` surface appearing in clause `(iii)`.
    calc
      {}^[(1 : PosReal)] (gammaZeroConjugate pavOwner hpav) =
          (fun x : H ↦ (gammaZeroConjugate pavOwner hpav x : EReal)) □ halfSquaredNorm := by
            rw [unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one]
      _ = pav(f, g)∗ □ halfSquaredNorm := by
            congr 1
  have htheta_unit :
      {}^[(1 : PosReal)] (gammaZeroConjugate pavOwner hpav) =
        (proximal_average_theta f g hf hg)∗ := by
    -- Identify the packaged `pav(f, g)` owner with `Θ(f, g) - q`, then use `(f + q)^* = e₁(f*)`.
    calc
      {}^[(1 : PosReal)] (gammaZeroConjugate pavOwner hpav) =
          (pavOwner + halfSquaredNorm).asEReal∗ := by
            simpa using
              (conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate
                pavOwner hpav).symm
      _ = (fun x : H ↦ pav(f, g) x + halfSquaredNorm.asEReal x)∗ := by
            congr 1
      _ = (proximal_average_theta f g hf hg)∗ := by
            congr 1
            exact (proximal_average_theta_eq_add_halfSquaredNorm f g hf hg).symm
  have hf_unit :
      {}^[(1 : PosReal)] (gammaZeroConjugate f hf) =
        gammaZeroConjugate f hf □ halfSquaredNorm := by
    rw [unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one]
  have hg_unit :
      {}^[(1 : PosReal)] (gammaZeroConjugate g hg) =
        gammaZeroConjugate g hg □ halfSquaredNorm := by
    rw [unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one]
  -- Follow the source route `(14.16)`: rewrite `(pav(f,g) + q)^*` as `Θ(f,g)^*` and then insert
  -- the already computed half-sum formula for `Θ(f, g)^*`.
  ext x
  calc
    (pav(f, g)∗ □ halfSquaredNorm) x =
        ({}^[(1 : PosReal)] (gammaZeroConjugate pavOwner hpav)) x := by
          simpa using congrFun hpav_unit.symm x
    _ = (proximal_average_theta f g hf hg)∗ x := by
          simpa using congrFun htheta_unit x
    _ = ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x := by
            exact congrFun (conjugate_proximal_average_theta_eq_half_sum_unitMoreau f g hf hg) x
    _ = ((1 / 2 : ℝ) : EReal) * (gammaZeroConjugate f hf □ halfSquaredNorm) x +
          ((1 / 2 : ℝ) : EReal) * (gammaZeroConjugate g hg □ halfSquaredNorm) x := by
            rw [congrFun hf_unit x, congrFun hg_unit x]

/-- Corollary 14.8 (3): with `q = (1 / 2) ‖ · ‖²`, written as `halfSquaredNorm`, the infimal
convolution `pav(f, g) □ q` is the arithmetic mean of `f □ q` and `g □ q`. -/
theorem proximalAverage_infimalConvolution_unitMoreauQuadraticKernel
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g) □ halfSquaredNorm =
      fun x : H ↦
        ((1 / 2 : ℝ) : EReal) * (f □ halfSquaredNorm) x +
          ((1 / 2 : ℝ) : EReal) * (g □ halfSquaredNorm) x := by
  have hconj_pav :
      pav(f, g) =
        pav(gammaZeroConjugate f hf, gammaZeroConjugate g hg)∗ := by
    -- Replace `f` and `g` by their conjugates, then collapse the resulting double conjugates.
    symm
    simpa [gammaZeroConjugate_gammaZeroConjugate_eq f hf,
      gammaZeroConjugate_gammaZeroConjugate_eq g hg] using
      (gammaZeroConjugate_proximalAverage
        (gammaZeroConjugate f hf)
        (gammaZeroConjugate g hg)
        (gammaZeroConjugate_mem_gammaZero hf)
        (gammaZeroConjugate_mem_gammaZero hg))
  calc
    pav(f, g) □ halfSquaredNorm =
        pav(gammaZeroConjugate f hf, gammaZeroConjugate g hg)∗ □ halfSquaredNorm := by
          rw [hconj_pav]
    _ =
        fun x : H ↦
          ((1 / 2 : ℝ) : EReal) *
              (gammaZeroConjugate
                (gammaZeroConjugate f hf)
                (gammaZeroConjugate_mem_gammaZero hf) □ halfSquaredNorm) x +
            ((1 / 2 : ℝ) : EReal) *
              (gammaZeroConjugate
                (gammaZeroConjugate g hg)
                (gammaZeroConjugate_mem_gammaZero hg) □ halfSquaredNorm) x := by
              exact proximal_average_conjugate_moreau_identity
                (gammaZeroConjugate f hf)
                (gammaZeroConjugate g hg)
                (gammaZeroConjugate_mem_gammaZero hf)
                (gammaZeroConjugate_mem_gammaZero hg)
    _ =
        fun x : H ↦
          ((1 / 2 : ℝ) : EReal) * (f □ halfSquaredNorm) x +
            ((1 / 2 : ℝ) : EReal) * (g □ halfSquaredNorm) x := by
              congr with x
              rw [gammaZeroConjugate_gammaZeroConjugate_eq f hf,
                gammaZeroConjugate_gammaZeroConjugate_eq g hg]

/-- Helper for Corollary 14.8: after rewriting the left side of `(14.16)` as the unit Moreau
envelope of `(pav(f, g))^*`, the source identity becomes a real-valued half-sum formula. -/
lemma proximal_average_conjugate_unitMoreau_toReal_eq_half_sum
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    let pavOwner : H → Set.Ioi (⊥ : EReal) :=
      properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg)
    let hpav : pavOwner ∈ Γ₀(H) := proximalAverage_mem_gammaZero f g hf hg
    (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate pavOwner hpav)) y).toReal) =
      fun y : H ↦
        (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal +
          (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) y).toReal := by
  dsimp
  have hpav_unit :
      {}^[(1 : PosReal)]
          (gammaZeroConjugate
            (properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg))
            (proximalAverage_mem_gammaZero f g hf hg)) =
        pav(f, g)∗ □ halfSquaredNorm := by
    -- Rewrite the packaged conjugate owner back to the raw `pav(f, g)∗ □ q` surface.
    calc
      {}^[(1 : PosReal)]
          (gammaZeroConjugate
            (properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg))
            (proximalAverage_mem_gammaZero f g hf hg)) =
          gammaZeroConjugate
              (properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg))
              (proximalAverage_mem_gammaZero f g hf hg) □ halfSquaredNorm := by
                rw [unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one]
      _ = pav(f, g)∗ □ halfSquaredNorm := by
            funext x
            simp [gammaZeroConjugate_apply]
  funext x
  have hE :
      ({}^[(1 : PosReal)]
          (gammaZeroConjugate
            (properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg))
            (proximalAverage_mem_gammaZero f g hf hg))) x =
        ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x +
          ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x := by
    -- This is the source identity `(14.16)` rewritten entirely on the unit-Moreau surface.
    calc
      ({}^[(1 : PosReal)]
          (gammaZeroConjugate
            (properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg))
            (proximalAverage_mem_gammaZero f g hf hg))) x =
          (pav(f, g)∗ □ halfSquaredNorm) x := by
            simpa using congrFun hpav_unit x
      _ = ((1 / 2 : ℝ) : EReal) * (gammaZeroConjugate f hf □ halfSquaredNorm) x +
            ((1 / 2 : ℝ) : EReal) * (gammaZeroConjugate g hg □ halfSquaredNorm) x := by
              exact congrFun (proximal_average_conjugate_moreau_identity f g hf hg) x
      _ = ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x +
            ((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x := by
              rw [unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one,
                unit_moreauEnvelope_eq_infimalConvolution_halfSquaredNorm_at_one]
  have hf_unit_finite :=
    unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero_local
      (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf) x
  have hg_unit_finite :=
    unit_moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero_local
      (gammaZeroConjugate g hg) (gammaZeroConjugate_mem_gammaZero hg) x
  rcases hf_unit_finite with ⟨hf_unit_top, hf_unit_bot⟩
  rcases hg_unit_finite with ⟨hg_unit_top, hg_unit_bot⟩
  have hhalf_f_top :
      (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)),
        Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)),
        Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
        Or.inr hf_unit_top⟩
  have hhalf_g_top :
      (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)),
        Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)),
        Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
        Or.inr hg_unit_top⟩
  have hhalf_f_bot :
      (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) x) ≠ ⊥ := by
    exact
      (EReal.mul_ne_bot _ _).2
        ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)),
          Or.inr hf_unit_bot,
          Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
          Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num))⟩
  have hhalf_g_bot :
      (((1 / 2 : ℝ) : EReal) * ({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) x) ≠ ⊥ := by
    exact
      (EReal.mul_ne_bot _ _).2
        ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)),
          Or.inr hg_unit_bot,
          Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
          Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num))⟩
  have hEreal := congrArg EReal.toReal hE
  rw [EReal.toReal_add hhalf_f_top hhalf_f_bot hhalf_g_top hhalf_g_bot,
    EReal.toReal_mul, EReal.toReal_mul] at hEreal
  simpa using hEreal

/-- Helper for Corollary 14.8: differentiating the half-sum of the two unit Moreau envelopes of
`f^*` and `g^*` yields the arithmetic mean of `Prox_f` and `Prox_g`. -/
lemma gradient_half_sum_unitMoreau_toReal_eq_half_sum_prox
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    ∇ (fun y : H ↦
        (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal +
          (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) y).toReal) =
      fun x : H ↦
        (1 / 2 : ℝ) • Prox[f, hf] x +
          (1 / 2 : ℝ) • Prox[g, hg] x := by
  -- Differentiate each unit Moreau envelope through the canonical Remark 14.4 bridge.
  apply gradient_eq
  intro x
  have hf_grad :
      HasGradientAt
        (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal)
        (Prox[f, hf] x) x := by
    have hf_grad_raw :=
      moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
        (f := gammaZeroConjugate f hf)
        (γ := (1 : PosReal))
        (hf := gammaZeroConjugate_mem_gammaZero hf)
        (x := x)
    have hprox_eq_raw :=
      (congrFun
        (proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
          (f := f) (hf := hf))
        x).trans hf_grad_raw.gradient
    simpa [hprox_eq_raw] using hf_grad_raw
  have hg_grad :
      HasGradientAt
        (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) y).toReal)
        (Prox[g, hg] x) x := by
    have hg_grad_raw :=
      moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
        (f := gammaZeroConjugate g hg)
        (γ := (1 : PosReal))
        (hf := gammaZeroConjugate_mem_gammaZero hg)
        (x := x)
    have hprox_eq_raw :=
      (congrFun
        (proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
          (f := g) (hf := hg))
        x).trans hg_grad_raw.gradient
    simpa [hprox_eq_raw] using hg_grad_raw
  have hf_half :
      HasGradientAt
        (fun y : H ↦ (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal)
        ((1 / 2 : ℝ) • Prox[f, hf] x) x := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (hf_grad.hasFDerivAt.const_smul (1 / 2 : ℝ)).hasGradientAt
  have hg_half :
      HasGradientAt
        (fun y : H ↦ (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) y).toReal)
        ((1 / 2 : ℝ) • Prox[g, hg] x) x := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (hg_grad.hasFDerivAt.const_smul (1 / 2 : ℝ)).hasGradientAt
  -- Add the two differentiated halves to recover the gradient of the full half-sum.
  simpa [Pi.smul_apply, smul_eq_mul, add_assoc, add_left_comm, add_comm] using
    (hf_half.hasFDerivAt.add hg_half.hasFDerivAt).hasGradientAt

/-- Corollary 14.8 (4): the proximity operator of the canonical `Γ₀(H)` owner underlying
`pav(f, g)` is the arithmetic mean of `Prox[f, hf]` and `Prox[g, hg]`. -/
theorem proximityOperator_proximalAverage_eq_arithmeticMean
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    Prox[
      properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg),
      proximalAverage_mem_gammaZero f g hf hg] =
      fun x : H ↦
        (1 / 2 : ℝ) • Prox[f, hf] x +
          (1 / 2 : ℝ) • Prox[g, hg] x := by
  -- Route correction: finish the source step `(14.17)` by importing the canonical Remark 14.4
  -- bridge instead of rebuilding the Chapter 16 subdifferential route locally.
  let pavOwner : H → Set.Ioi (⊥ : EReal) :=
    properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg)
  let hpav : pavOwner ∈ Γ₀(H) := proximalAverage_mem_gammaZero f g hf hg
  -- Rewrite `Prox[pav]` as the gradient of the unit Moreau envelope of `(pav)^*`.
  calc
    Prox[pavOwner, hpav] =
        ∇ (fun y : H ↦ (({}^[(1 : PosReal)] (gammaZeroConjugate pavOwner hpav)) y).toReal) := by
          exact
            proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
              (f := pavOwner) (hf := hpav)
    _ =
        ∇ (fun y : H ↦
          (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate f hf)) y).toReal +
            (1 / 2 : ℝ) * (({}^[(1 : PosReal)] (gammaZeroConjugate g hg)) y).toReal) := by
              -- This is the real-valued form of the source identity `(14.16)`.
              dsimp [pavOwner, hpav]
              exact
                congrArg ∇
                  (proximal_average_conjugate_unitMoreau_toReal_eq_half_sum f g hf hg)
    _ = fun x : H ↦
          (1 / 2 : ℝ) • Prox[f, hf] x +
            (1 / 2 : ℝ) • Prox[g, hg] x := by
              -- Differentiate the two summands separately and reassemble the arithmetic mean.
              exact gradient_half_sum_unitMoreau_toReal_eq_half_sum_prox f g hf hg

end ProximalAverage

end ERealFunction
