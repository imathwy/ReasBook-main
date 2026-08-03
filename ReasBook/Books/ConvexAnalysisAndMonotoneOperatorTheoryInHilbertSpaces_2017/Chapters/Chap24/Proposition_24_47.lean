import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap24.Example_24_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

section RealInterval

variable {a b : ℝ}

local notation "Ω" => Set.Icc a b

/-- The interval indicator can be added to a `Γ₀(ℝ)` function without leaving `Γ₀(ℝ)`
when the effective domains meet. -/
theorem indicator_Icc_add_mem_gammaZero
    {φ : ℝ → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(ℝ))
    (h : a ≤ b) (hdom : (Ω ∩ effectiveDomain φ).Nonempty) :
    ι[Ω] + φ ∈ Γ₀(ℝ) :=
  pointwiseAdd_mem_gammaZero (ι[Ω]) φ
    (indicator_mem_gammaZero_of_nonempty_isClosed_convex
      (Set.nonempty_Icc.2 h) isClosed_Icc (convex_Icc a b))
    hφ
    (by simpa [effectiveDomain_indicator] using hdom)

-- Semantic recall note: the canonical closed-interval projection owner is `Set.projIcc`. For the
-- `Γ₀` witness of `ι_Ω + φ`, this file keeps only the thin interval-specialized bridge
-- `indicator_Icc_add_mem_gammaZero`
-- over the chapter owners
-- `indicator_mem_gammaZero_of_nonempty_isClosed_convex` and `pointwiseAdd_mem_gammaZero`
-- rather than a second interval-specific owner.

/-- Proposition 24.47: if `φ ∈ Γ₀(ℝ)` and `Ω = [a,b]` is a closed interval such that
`Ω ∩ dom φ ≠ ∅`, then `Prox_{ι_Ω + φ}` is the canonical interval projection `Set.projIcc`
applied to `Prox_φ`. -/
theorem proximityOperator_indicator_Icc_add_eq_projIcc_comp_prox
    {φ : ℝ → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(ℝ))
    (h : a ≤ b) (hdom : (Ω ∩ effectiveDomain φ).Nonempty) :
    Prox[ι[Ω] + φ, indicator_Icc_add_mem_gammaZero hφ h hdom] =
      projIccReal h ∘ Prox[φ, hφ] := by
  funext x
  let p := Prox[φ, hφ] x
  let q : ℝ := projIccReal h p
  have hp_prox : IsProxPoint φ x p := by
    simpa [p] using
      proximityOperator_isProxPoint φ (hasUniqueProxPoint_of_mem_gammaZero φ hφ) x
  have hp_min : ∀ y, proximalObjective φ x p ≤ proximalObjective φ x y := by
    rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp_prox
    exact hp_prox
  have hp_dom : p ∈ effectiveDomain φ := by
    rcases hφ.2.nonempty with ⟨r, hr_dom⟩
    by_contra hp_dom
    have hp_top : (φ p : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hp_dom))
    have hp_le := hp_min r
    have hr_top : (φ r : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hr_dom)
    have hr_bot : (φ r : EReal) ≠ ⊥ := ne_of_gt (φ r).2
    have hr_obj_ne_top : proximalObjective φ x r ≠ ⊤ := by
      rw [proximalObjective, ← EReal.coe_toReal hr_top hr_bot, ← EReal.coe_add]
      exact EReal.coe_ne_top _
    rw [proximalObjective, hp_top, EReal.top_add_coe] at hp_le
    exact hr_obj_ne_top (top_le_iff.mp hp_le)
  have hq_mem : q ∈ Ω := by
    change ((Set.projIcc a b h p : Set.Icc a b) : ℝ) ∈ Ω
    exact (Set.projIcc a b h p).2
  have hq_dom : q ∈ effectiveDomain φ := by
    rcases hdom with ⟨r, hr_mem, hr_dom⟩
    by_cases hp_left : p < a
    · have hq_eq : q = a := by
        simp [q, Set.projIcc_of_le_left, hp_left.le]
      rw [hq_eq]
      exact hφ.2.convex_effectiveDomain.ordConnected.out hp_dom hr_dom ⟨hp_left.le, hr_mem.1⟩
    · by_cases hp_mem : p ∈ Ω
      · simpa [q, Set.projIcc_of_mem h hp_mem] using hp_dom
      · have hp_right : b < p := by
          have hpa : a ≤ p := le_of_not_gt hp_left
          have hpb : ¬ p ≤ b := by
            exact fun hpb ↦ hp_mem ⟨hpa, hpb⟩
          exact lt_of_not_ge hpb
        have hq_eq : q = b := by
          simp [q, Set.projIcc_of_right_le, hp_right.le]
        rw [hq_eq]
        exact
          hφ.2.convex_effectiveDomain.ordConnected.out
            hr_dom hp_dom ⟨hr_mem.2, hp_right.le⟩
  have hquad_conv :
      _root_.ConvexOn ℝ Set.univ (fun y : ℝ ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ α β hα hβ hαβ
    have hsq :
        ‖x - (α • y + β • z)‖ ^ 2 ≤ α * ‖x - y‖ ^ 2 + β * ‖x - z‖ ^ 2 := by
      have hbase : _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ ‖t‖ ^ 2) :=
        strictConvexOn_norm_sq.convexOn
      have hrewrite :
          x - (α • y + β • z) = α • (x - y) + β • (x - z) := by
        calc
          x - (α • y + β • z) = (α + β) • x - (α • y + β • z) := by simp [hαβ]
          _ = α • x + β • x - (α • y + β • z) := by rw [add_smul]
          _ = α • (x - y) + β • (x - z) := by
                rw [smul_sub, smul_sub]
                abel_nf
      rw [hrewrite]
      exact
        hbase.2
          (by simp : x - y ∈ (Set.univ : Set ℝ))
          (by simp : x - z ∈ (Set.univ : Set ℝ))
          hα hβ hαβ
    have htarget :
        (1 / 2 : ℝ) * ‖x - (α • y + β • z)‖ ^ 2 ≤
          α * ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) + β * ((1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
      nlinarith
    simpa [smul_eq_mul] using htarget
  have hobj_conv :
      _root_.ConvexOn ℝ (effectiveDomain φ)
        (fun y : ℝ ↦ (φ y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
    refine ⟨hφ.2.convex_effectiveDomain, ?_⟩
    intro y hy z hz α β hα hβ hαβ
    have hφ_conv :=
      hφ.2.toReal_convexOn_effectiveDomain.2 hy hz hα hβ hαβ
    have hquad :=
      hquad_conv.2
        (by simp : y ∈ (Set.univ : Set ℝ))
        (by simp : z ∈ (Set.univ : Set ℝ))
        hα hβ hαβ
    have hsum := add_le_add hφ_conv hquad
    simpa [smul_eq_mul, mul_add, add_mul, add_assoc, add_left_comm, add_comm,
      left_distrib, right_distrib] using hsum
  have hq_prox : IsProxPoint (ι[Ω] + φ) x q := by
    rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff]
    intro y
    by_cases hy_mem : y ∈ Ω ∩ effectiveDomain φ
    · have hyΩ : y ∈ Ω := hy_mem.1
      have hy_dom : y ∈ effectiveDomain φ := hy_mem.2
      have hp_top : (φ p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
      have hp_bot : (φ p : EReal) ≠ ⊥ := ne_of_gt (φ p).2
      have hq_top : (φ q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq_dom)
      have hq_bot : (φ q : EReal) ≠ ⊥ := ne_of_gt (φ q).2
      have hy_top : (φ y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
      have hy_bot : (φ y : EReal) ≠ ⊥ := ne_of_gt (φ y).2
      have hp_le_real :
          (φ p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
            (φ y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
        have hp_le := hp_min y
        rw [proximalObjective, proximalObjective, ← EReal.coe_toReal hp_top hp_bot,
          ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_add, ← EReal.coe_add] at hp_le
        exact_mod_cast hp_le
      have hq_seg : q ∈ segment ℝ p y := by
        by_cases hp_left : p < a
        · have hq_eq : q = a := by
            simp [q, Set.projIcc_of_le_left, hp_left.le]
          rw [hq_eq, segment_eq_Icc (show p ≤ y by exact le_trans hp_left.le hyΩ.1)]
          exact ⟨hp_left.le, hyΩ.1⟩
        · by_cases hp_mem : p ∈ Ω
          · have hq_eq : q = p := by
              simp [q, Set.projIcc_of_mem h hp_mem]
            rw [hq_eq]
            exact left_mem_segment ℝ p y
          · have hp_right : b < p := by
              have hpa : a ≤ p := le_of_not_gt hp_left
              have hpb : ¬ p ≤ b := by
                exact fun hpb ↦ hp_mem ⟨hpa, hpb⟩
              exact lt_of_not_ge hpb
            have hq_eq : q = b := by
              simp [q, Set.projIcc_of_right_le, hp_right.le]
            have hy_le_p : y ≤ p := le_trans hyΩ.2 hp_right.le
            rw [hq_eq, segment_symm, segment_eq_Icc hy_le_p]
            exact ⟨hyΩ.2, hp_right.le⟩
      have hq_le_max :
          (φ q : EReal).toReal + (1 / 2 : ℝ) * ‖x - q‖ ^ 2 ≤
            max
              ((φ p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2)
              ((φ y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2) :=
        hobj_conv.le_on_segment hp_dom hy_dom hq_seg
      have hq_le_real :
          (φ q : EReal).toReal + (1 / 2 : ℝ) * ‖x - q‖ ^ 2 ≤
            (φ y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
        calc
          (φ q : EReal).toReal + (1 / 2 : ℝ) * ‖x - q‖ ^ 2
              ≤ max
                  ((φ p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2)
                  ((φ y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2) :=
            hq_le_max
          _ = (φ y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 :=
            max_eq_right hp_le_real
      have hq_le :
          proximalObjective (ι[Ω] + φ) x q ≤ proximalObjective (ι[Ω] + φ) x y := by
        have hcast :
            (((φ q : EReal).toReal + (1 / 2 : ℝ) * ‖x - q‖ ^ 2 : ℝ) : EReal) ≤
              (((φ y : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
          exact_mod_cast hq_le_real
        simpa [proximalObjective, indicator_apply, hq_mem, hyΩ, EReal.coe_toReal hp_top hp_bot,
          EReal.coe_toReal hq_top hq_bot, EReal.coe_toReal hy_top hy_bot, EReal.coe_add] using
          hcast
      exact hq_le
    · have hy_top : ((ι[Ω] + φ) y : EReal) = ⊤ := by
        by_cases hyΩ : y ∈ Ω
        · have hy_dom : y ∉ effectiveDomain φ := by
            exact fun hy_dom ↦ hy_mem ⟨hyΩ, hy_dom⟩
          have hφy_top : (φ y : EReal) = ⊤ := by
            exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy_dom))
          simp [indicator_apply, hyΩ, hφy_top]
        · have hφy_bot : (φ y : EReal) ≠ ⊥ := ne_of_gt (φ y).2
          simpa [indicator_apply, hyΩ] using EReal.top_add_of_ne_bot hφy_bot
      change
        ((ι[Ω] + φ) q : EReal) + ((((1 / 2 : ℝ) * ‖x - q‖ ^ 2 : ℝ) : EReal)) ≤
          ((ι[Ω] + φ) y : EReal) + ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal))
      rw [hy_top, EReal.top_add_coe]
      exact le_top
  simpa [q, p] using
    (eq_proximityOperator_of_isProxPoint
      (ι[Ω] + φ)
      (hasUniqueProxPoint_of_mem_gammaZero
        (ι[Ω] + φ)
        (indicator_Icc_add_mem_gammaZero hφ h hdom))
      hq_prox).symm

/-- Pointwise form of Proposition 24.47. -/
@[simp] theorem proximityOperator_indicator_Icc_add_apply_eq_projIccReal_prox
    {φ : ℝ → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(ℝ))
    (h : a ≤ b) (hdom : (Ω ∩ effectiveDomain φ).Nonempty) (x : ℝ) :
    Prox[ι[Ω] + φ, indicator_Icc_add_mem_gammaZero hφ h hdom] x =
      projIccReal h (Prox[φ, hφ] x) := by
  simpa [Function.comp] using
    congrFun (proximityOperator_indicator_Icc_add_eq_projIcc_comp_prox hφ h hdom) x

end RealInterval

end

end ERealFunction
