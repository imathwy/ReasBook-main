import Mathlib
import BauschkeLean.Chap12.Definition_12_20_Core
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap13.Example_13_6
import BauschkeLean.Chap15.Theorem_15_3
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 16 43: `halfSquaredNorm` is the canonical `toEReal` lift of
`x ↦ ‖x‖² / 2`. -/
private theorem halfSquaredNorm_eq_toEReal_quadratic :
    ((fun x : H ↦ ((‖x‖ ^ 2) / 2 : ℝ)).toEReal) =
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
  funext x
  simp [halfSquaredNorm, moreauQuadraticKernel, div_eq_mul_inv, mul_comm]

omit [CompleteSpace H] in
/-- Helper for Example 16 43: the quadratic owner `halfSquaredNorm` belongs to `Γ₀(H)`. -/
private theorem halfSquaredNorm_mem_gammaZero :
    (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
  rw [← halfSquaredNorm_eq_toEReal_quadratic]
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    -- Use convexity of `x ↦ ‖x‖²` and scale the resulting Jensen inequality by `1 / 2`.
    have hnorm_sq :
        _root_.ConvexOn ℝ (Set.univ : Set H) (fun x : H ↦ ‖x‖ ^ 2) :=
      (convexOn_univ_norm : _root_.ConvexOn ℝ (Set.univ : Set H) (fun x : H ↦ ‖x‖)).pow
        (fun x _ ↦ norm_nonneg x) 2
    have hconv :
        ‖a • x + (1 - a) • y‖ ^ 2 / 2 ≤
          a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) := by
      have hnorm_sq' :
          ‖a • x + (1 - a) • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 := by
        simpa [smul_eq_mul] using
          hnorm_sq.2 (by simp) (by simp) ha0 (sub_nonneg.mpr ha1) (by ring)
      nlinarith
    change (((‖a • x + (1 - a) • y‖ ^ 2) / 2 : ℝ) : EReal) ≤
        (((a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) : ℝ)) : EReal)
    exact_mod_cast hconv
  · -- Continuity of the real quadratic representative gives lower semicontinuity after coercion.
    have hcont : Continuous fun x : H ↦ ((‖x‖ ^ 2) / 2 : ℝ) := by
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_norm.pow 2).const_mul (1 / 2 : ℝ)
    have hcontE : Continuous fun x : H ↦ ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := by
      simpa using continuous_coe_real_ereal.comp hcont
    simpa using hcontE.lowerSemicontinuous

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 16 43: the quadratic owner is finite everywhere. -/
private theorem effectiveDomain_halfSquaredNorm_eq_univ :
    effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) = (Set.univ : Set H) := by
  rw [← halfSquaredNorm_eq_toEReal_quadratic]
  exact Function.effectiveDomain_toEReal (fun x : H ↦ ((‖x‖ ^ 2) / 2 : ℝ))

omit [CompleteSpace H] in
/-- Helper for Example 16 43: the quadratic subdifferential is the singleton identity operator. -/
private theorem subdifferential_halfSquaredNorm_eq_singleton_local :
    ∂ (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) =
      (fun x : H ↦ ({x} : Set H) : SetValuedOperator H H) := by
  -- Route correction: replay Example 16.12 locally so this file no longer depends on the broken
  -- import chain through `Chap01.Text_1_0_13`.
  ext x u
  rw [Set.mem_singleton_iff]
  constructor
  · intro hu
    -- Fenchel--Young equality for `halfSquaredNorm` forces the quadratic gap `‖x - u‖²` to vanish.
    have hfy := (mem_subdifferential_iff_fenchel_young_eq halfSquaredNorm x u).1 hu
    rw [fenchelConjugate_halfSquaredNorm] at hfy
    norm_num [halfSquaredNorm_apply] at hfy
    have hfy' :
        (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) = inner ℝ x u := by
      exact_mod_cast hfy
    have hnorm : ‖x - u‖ ^ (2 : ℕ) = 0 := by
      rw [norm_sub_sq_real]
      nlinarith [hfy', real_inner_comm x u]
    have hzero : ‖x - u‖ = 0 := sq_eq_zero_iff.mp hnorm
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  · intro hu
    subst u
    -- Self-conjugacy of `halfSquaredNorm` makes the Fenchel--Young inequality exact at `u = x`.
    exact (mem_subdifferential_iff_fenchel_young_eq halfSquaredNorm x x).2 <| by
      rw [fenchelConjugate_halfSquaredNorm, Function.asEReal_apply, halfSquaredNorm_apply,
        real_inner_self_eq_norm_sq]
      exact_mod_cast (by ring :
        ‖x‖ ^ (2 : ℕ) / 2 + ‖x‖ ^ (2 : ℕ) / 2 = ‖x‖ ^ (2 : ℕ))

omit [CompleteSpace H] in
/-- Helper for Example 16 43: scalar multiplication of the singleton identity operator acts
pointwise. -/
private theorem singleton_operator_real_smul_ext (γ : PosReal) :
    (γ : ℝ) • (fun x : H ↦ ({x} : Set H) : SetValuedOperator H H) =
      (fun x : H ↦ ({(γ : ℝ) • x} : Set H) : SetValuedOperator H H) := by
  -- Extensionality reduces the operator identity to the scalar action on a singleton set.
  ext x u
  constructor
  · intro hu
    rcases Set.mem_smul_set.mp hu with ⟨v, hv, rfl⟩
    rcases Set.mem_singleton_iff.mp hv with rfl
    simp
  · intro hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    exact Set.mem_smul_set.mpr ⟨x, by simp, rfl⟩

omit [CompleteSpace H] in
/-- Helper for Example 16 43: scaling `halfSquaredNorm` scales its singleton subdifferential. -/
private theorem subdifferential_scaled_halfSquaredNorm_eq_singleton_smul
    (γ : PosReal) :
    ∂ (γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) =
      (fun x : H ↦ ({(γ : ℝ) • x} : Set H) : SetValuedOperator H H) := by
  -- First apply the positive-scaling rule for subdifferentials at the quadratic owner.
  calc
    ∂ (γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) =
        (γ : ℝ) •
          (∂ (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) : SetValuedOperator H H) := by
            simpa using
              subdifferential_posReal_smul_eq_smul
                (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) γ
    _ = (γ : ℝ) • (fun x : H ↦ ({x} : Set H) : SetValuedOperator H H) := by
          rw [subdifferential_halfSquaredNorm_eq_singleton_local]
    _ = (fun x : H ↦ ({(γ : ℝ) • x} : Set H) : SetValuedOperator H H) := by
          rw [singleton_operator_real_smul_ext γ]

omit [CompleteSpace H] in
/-- Helper for Example 16 43: if the second effective domain is all of `H`, then the canonical
regularity hypothesis `0 ∈ sri (effectiveDomain f - effectiveDomain g)` holds. -/
private theorem zero_mem_sri_sub_effectiveDomain_of_dom_univ_local
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : effectiveDomain g = (Set.univ : Set H)) :
    (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) := by
  -- Rewrite the domain difference against `univ`, then identify its strong relative interior.
  rw [hdom]
  obtain ⟨x, hx⟩ : (effectiveDomain f).Nonempty := ConvexOn.nonempty hf.2
  have hsub : effectiveDomain f - (Set.univ : Set H) = (Set.univ : Set H) := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      exact Set.mem_sub.mpr ⟨x, hx, x - y, by simp, by abel⟩
  rw [hsub]
  rw [Set.mem_strongRelativeInterior_iff]
  refine ⟨by simp, ?_⟩
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    rw [Set.cone_def]
    exact ConvexCone.subset_hull (by simp)

omit [CompleteSpace H] in
/-- Helper for Example 16 43: a Fenchel--Young equality split for `f + g` separates into the two
component subgradient memberships. -/
private theorem component_subgradients_of_dual_sum_split
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    {x u w : H}
    (hsplit : ((f x : EReal) + (g x : EReal)) +
        (conjugate f.asEReal (u - w) + conjugate g.asEReal w) =
          ((inner ℝ x u : ℝ) : EReal)) :
    u - w ∈ (∂ f) x ∧ w ∈ (∂ g) x := by
  -- The conjugate terms are never `-∞` because `Γ₀(H)` functions have nonempty effective domains.
  have hc_bot : f.asEReal∗ (u - w) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty (u - w)
  have hd_bot : g.asEReal∗ w ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty w
  have hab_bot : (f x : EReal) + (g x : EReal) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g x).2⟩
  have hcd_bot : f.asEReal∗ (u - w) + g.asEReal∗ w ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2
      ⟨bot_lt_iff_ne_bot.mpr hc_bot, bot_lt_iff_ne_bot.mpr hd_bot⟩
  have hsum_top :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ (u - w) + g.asEReal∗ w) ≠ ⊤ := by
    intro htop
    exact EReal.coe_ne_top (inner ℝ x u : ℝ) (hsplit.symm.trans htop)
  have hsum_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hab_bot hcd_bot).1 hsum_top
  have hab_top : (f x : EReal) + (g x : EReal) ≠ ⊤ := hsum_top_parts.1
  have hcd_top : f.asEReal∗ (u - w) + g.asEReal∗ w ≠ ⊤ := hsum_top_parts.2
  have hab_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (f x).2) (ne_of_gt (g x).2)).1 hab_top
  have hcd_top_parts :=
    (EReal.add_ne_top_iff_ne_top₂ hc_bot hd_bot).1 hcd_top
  have ha_top : (f x : EReal) ≠ ⊤ := hab_top_parts.1
  have hb_top : (g x : EReal) ≠ ⊤ := hab_top_parts.2
  have hc_top : f.asEReal∗ (u - w) ≠ ⊤ := hcd_top_parts.1
  have hd_top : g.asEReal∗ w ≠ ⊤ := hcd_top_parts.2
  have hac_top : (f x : EReal) + f.asEReal∗ (u - w) ≠ ⊤ :=
    EReal.add_ne_top ha_top hc_top
  have hbd_top : (g x : EReal) + g.asEReal∗ w ≠ ⊤ :=
    EReal.add_ne_top hb_top hd_top
  have hac_bot : (f x : EReal) + f.asEReal∗ (u - w) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, bot_lt_iff_ne_bot.mpr hc_bot⟩
  have hbd_bot : (g x : EReal) + g.asEReal∗ w ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(g x).2, bot_lt_iff_ne_bot.mpr hd_bot⟩
  -- Fenchel--Young gives the component lower bounds.
  have hfy_f :
      ((inner ℝ x (u - w) : ℝ) : EReal) ≤
        (f x : EReal) + f.asEReal∗ (u - w) :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hf) x (u - w)
  have hfy_g :
      ((inner ℝ x w : ℝ) : EReal) ≤
        (g x : EReal) + g.asEReal∗ w :=
    fenchel_young_inequality (isProper_of_mem_gammaZero hg) x w
  have hfy_f_toReal :
      inner ℝ x (u - w) ≤
        (f x : EReal).toReal + (f.asEReal∗ (u - w)).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_f (EReal.coe_ne_bot _) hac_top
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot] at htmp
    exact htmp
  have hfy_g_toReal :
      inner ℝ x w ≤
        (g x : EReal).toReal + (g.asEReal∗ w).toReal := by
    have htmp :=
      EReal.toReal_le_toReal hfy_g (EReal.coe_ne_bot _) hbd_top
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot] at htmp
    exact htmp
  -- Convert the displayed equality to `ℝ` so linear arithmetic can isolate each equality case.
  have hsplit_toReal :
      ((f x : EReal).toReal + (g x : EReal).toReal) +
          ((f.asEReal∗ (u - w)).toReal + (g.asEReal∗ w).toReal) =
        inner ℝ x u := by
    have htmp := congrArg EReal.toReal hsplit
    rw [EReal.toReal_add hab_top hab_bot hcd_top hcd_bot,
      EReal.toReal_add ha_top (ne_of_gt (f x).2) hb_top (ne_of_gt (g x).2),
      EReal.toReal_add hc_top hc_bot hd_top hd_bot] at htmp
    exact htmp
  have hpair_real :
      inner ℝ x (u - w) + inner ℝ x w = inner ℝ x u := by
    calc
      inner ℝ x (u - w) + inner ℝ x w
          = (inner ℝ x u - inner ℝ x w) + inner ℝ x w := by
              simp [inner_sub_right]
      _ = inner ℝ x u := by ring
  have hcomp_f_toReal :
      (f x : EReal).toReal + (f.asEReal∗ (u - w)).toReal =
        inner ℝ x (u - w) := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hcomp_g_toReal :
      (g x : EReal).toReal + (g.asEReal∗ w).toReal = inner ℝ x w := by
    linarith [hfy_f_toReal, hfy_g_toReal, hsplit_toReal, hpair_real]
  have hfy_f_eq :
      (f x : EReal) + f.asEReal∗ (u - w) =
        ((inner ℝ x (u - w) : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hac_top hac_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add ha_top (ne_of_gt (f x).2) hc_top hc_bot]
    exact hcomp_f_toReal
  have hfy_g_eq :
      (g x : EReal) + g.asEReal∗ w =
        ((inner ℝ x w : ℝ) : EReal) := by
    apply (EReal.toReal_eq_toReal hbd_top hbd_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).mp
    rw [EReal.toReal_add hb_top (ne_of_gt (g x).2) hd_top hd_bot]
    exact hcomp_g_toReal
  -- Read the two exact Fenchel--Young equalities back as subgradient memberships.
  constructor
  · exact
      (mem_subdifferential_iff_fenchel_young_eq f x (u - w)).2 hfy_f_eq
  · exact
      (mem_subdifferential_iff_fenchel_young_eq g x w).2 hfy_g_eq

/-- Helper for Example 16 43: an active subgradient of `f + g` with `dom g = univ` yields an
exact dual infimal-convolution witness. -/
private theorem
    exists_exact_infimalConvolution_witness_of_mem_subdifferential_pointwiseAdd_of_dom_univ
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : effectiveDomain g = (Set.univ : Set H))
    {x u : H} (hu : u ∈ (∂ (f + g)) x) :
    ∃ w : H, (f.asEReal∗ □ g.asEReal∗) u = f.asEReal∗ (u - w) + g.asEReal∗ w := by
  -- Route correction: follow the textbook Attouch--Brézis route through the conjugate identity
  -- and exactness of `f^* □ g^*`, instead of trying to force the reverse inclusion directly.
  have hsri :
      (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) :=
    zero_mem_sri_sub_effectiveDomain_of_dom_univ_local hf hdom
  have hfg : f + g ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri
  have hconj :
      (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ :=
    conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
      f g hf hg hsri
  have hconj_gamma :
      (((f∗[hf]) □ (g∗[hg])) : H → EReal) = f.asEReal∗ □ g.asEReal∗ := by
    funext z
    simp
  have hfy :
      ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u =
        ((inner ℝ x u : ℝ) : EReal) := by
    simpa [pointwiseAdd_apply] using
      (mem_subdifferential_iff_fenchel_young_eq (f + g) x u).1 hu
  have hprimal_ne_bot : ((f x : EReal) + (g x : EReal)) ≠ ⊥ := by
    refine ne_of_gt ?_
    exact EReal.bot_lt_add_iff.2 ⟨(f x).2, (g x).2⟩
  have hdual_ne_top : (f + g).asEReal∗ u ≠ ⊤ := by
    intro hu_top
    have hsum_top :
        ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u = ⊤ := by
      rw [hu_top]
      exact EReal.add_top_of_ne_bot hprimal_ne_bot
    exact EReal.coe_ne_top _ (hfy.symm.trans hsum_top)
  have hu_dom :
      u ∈ dom (((f∗[hf]) □ (g∗[hg])) : H → EReal) := by
    rw [mem_dom_iff]
    rw [hconj_gamma, ← hconj]
    exact lt_top_iff_ne_top.mpr hdual_ne_top
  rcases
      infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
        f g hf hg hsri hu_dom with
    ⟨y, hy⟩
  -- Repackage the exact decomposition in the `u - w, w` form used by the source argument.
  refine ⟨u - y, ?_⟩
  simpa [gammaZeroConjugate_apply, sub_sub_cancel] using hy

/-- Helper for Example 16 43: under `dom g = univ`, every active subgradient of `f + g`
splits into one subgradient of `f` and one subgradient of `g`. -/
private theorem dual_split_of_mem_subdifferential_pointwiseAdd_of_dom_univ
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : effectiveDomain g = (Set.univ : Set H))
    {x u : H} (hu : u ∈ (∂ (f + g)) x) :
    ∃ v : H, v ∈ (∂ f) x ∧ u - v ∈ (∂ g) x := by
  have hsri :
      (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) :=
    zero_mem_sri_sub_effectiveDomain_of_dom_univ_local hf hdom
  have hfg : f + g ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain f g hf hg hsri
  have hconj :
      (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ :=
    conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
      f g hf hg hsri
  obtain ⟨w, hw⟩ :=
    exists_exact_infimalConvolution_witness_of_mem_subdifferential_pointwiseAdd_of_dom_univ
      hf hg hdom hu
  have hsplit :
      ((f x : EReal) + (g x : EReal)) +
          (f.asEReal∗ (u - w) + g.asEReal∗ w) =
        ((inner ℝ x u : ℝ) : EReal) := by
    -- Rewrite the active Fenchel--Young equality through the conjugate formula
    -- and the exact witness.
    have hfy := (mem_subdifferential_iff_fenchel_young_eq (f + g) x u).1 hu
    calc
      ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ (u - w) + g.asEReal∗ w)
          = ((f x : EReal) + (g x : EReal)) + (f.asEReal∗ □ g.asEReal∗) u := by
              rw [hw]
      _ = ((f x : EReal) + (g x : EReal)) + (f + g).asEReal∗ u := by
            rw [← hconj]
      _ = ((inner ℝ x u : ℝ) : EReal) := by
            simpa [pointwiseAdd_apply] using hfy
  rcases component_subgradients_of_dual_sum_split hf hg hsplit with ⟨hvf, hwg⟩
  refine ⟨u - w, hvf, ?_⟩
  simpa [sub_sub_cancel] using hwg

/-- Helper for Example 16 43: the Chapter 16 sum rule under the full-domain regularity branch. -/
private theorem subdifferential_add_eq_add_of_dom_univ_local
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : effectiveDomain g = (Set.univ : Set H)) :
    (∂ (f + g) : SetValuedOperator H H) = (∂ f) + (∂ g) := by
  ext x u
  constructor
  · intro hu
    -- Split the active subgradient using the exact Attouch--Brézis dual witness.
    obtain ⟨v, hvf, hvg⟩ :=
      dual_split_of_mem_subdifferential_pointwiseAdd_of_dom_univ hf hg hdom hu
    exact Set.mem_add.2 ⟨v, hvf, u - v, hvg, by abel⟩
  · intro hu
    -- Proposition 16.6 gives the easy inclusion after specializing the linear map to the identity.
    have hu_id :
        u ∈ (∂ f) x +
          ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g x := by
      simpa [ContinuousLinearMap.adjointImageSubdifferential] using hu
    simpa [Function.comp] using
      (subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g (ContinuousLinearMap.id ℝ H) x hu_id)

-- Proof sketch: apply the chapter sum rule for the full-domain quadratic perturbation
-- `γ • halfSquaredNorm`, then identify its subdifferential as the singleton-valued map
-- `x ↦ {γ • x}`.
/-- Example 16 43: if `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, then the subdifferential of
`f + (γ / 2) ‖·‖²` is `∂ f + γ Id`, encoded here as the set-valued map
`x ↦ (∂ f) x + {γ • x}`. -/
theorem subdifferential_add_scaledHalfSquaredNorm_eq_add_singleton_smul
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    ∂ (f + γ • halfSquaredNorm) =
      (∂ f) + fun x ↦ ({(γ : ℝ) • x} : Set H) := by
  -- Route correction: keep the textbook sum-rule route, but prove the quadratic support facts
  -- locally so the target no longer depends on the broken Chapter 14 / Example 16.12 import path.
  have hscaled : γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
    -- Chapter 12 already shows positive scaling preserves `Γ₀(H)`.
    exact smul_mem_gammaZero
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))
      halfSquaredNorm_mem_gammaZero
      γ
  have hdom :
      effectiveDomain (γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) = (Set.univ : Set H) := by
    -- Positive scaling preserves the everywhere-finite domain of the quadratic.
    ext x
    rw [mem_effectiveDomain_iff]
    simpa [posReal_smul_apply, halfSquaredNorm_apply, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using
      (EReal.coe_lt_top (((γ : ℝ) * ((‖x‖ ^ 2) / 2 : ℝ))))
  have hsum :
      ∂ (pointwiseAdd f (γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)))) =
        ((∂ f : SetValuedOperator H H) +
          ∂ (γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)))) := by
    -- The scaled quadratic term is finite everywhere, so the chapter sum rule applies directly.
    simpa using
      (subdifferential_add_eq_add_of_dom_univ_local
        (f := f)
        (g := γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)))
        hf
        hscaled
        hdom)
  -- The quadratic perturbation contributes the singleton map `x ↦ {γ • x}`.
  calc
    ∂ (f + γ • halfSquaredNorm)
        = ((∂ f : SetValuedOperator H H) +
            ∂ (γ • (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)))) := by
              simpa using hsum
    _ = (∂ f) + fun x ↦ ({(γ : ℝ) • x} : Set H) := by
          rw [subdifferential_scaled_halfSquaredNorm_eq_singleton_smul]

end

end ERealFunction
