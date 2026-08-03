import Mathlib
import BauschkeLean.Chap04.Proposition_4_4
import BauschkeLean.Chap08.Example_8_10
import BauschkeLean.Chap09.Corollary_9_4
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.Proposition_12_26

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section GammaZero

variable (f : H → Set.Ioi (⊥ : EReal))

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2_real
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2_real
attribute [local instance] ERealFunction.prod_seminormedAddCommGroup_l2_real
attribute [local instance] ERealFunction.prod_normedSpace_l2_real
attribute [local instance] ERealFunction.prod_completeSpace_l2_real
attribute [local instance] ERealFunction.prod_innerProductSpace_l2_real

/-- Helper for Proposition 12 28: the quadratic penalty `y ↦ (1 / 2) ‖x - y‖²` as an
`]-∞,+∞]`-valued function. -/
private noncomputable def quadraticPenalty (x : H) : H → Set.Ioi (⊥ : EReal) :=
  (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2).toEReal

/-- Helper for Proposition 12 28: the bundled proximal objective is the pointwise sum of `f` and
the quadratic penalty. -/
private noncomputable def proximalObjectiveIoi (x : H) : H → Set.Ioi (⊥ : EReal) :=
  f + quadraticPenalty x

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 28: coercing the quadratic penalty back to `EReal` recovers its real
formula. -/
@[simp] private theorem quadraticPenalty_apply (x y : H) :
    (quadraticPenalty (H := H) x y : EReal) = (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
  simp [quadraticPenalty]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 28: coercing the bundled proximal objective back to `EReal` gives
the canonical proximal objective from Definition 12.23. -/
@[simp] private theorem proximalObjectiveIoi_apply (x y : H) :
    (proximalObjectiveIoi (f := f) x y : EReal) = proximalObjective f x y := by
  simp [proximalObjectiveIoi, proximalObjective, quadraticPenalty]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 28: a continuous convex real-valued function on all of `H`
canonically gives a member of `Γ₀(H)` after applying `toEReal`. -/
private theorem real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : H → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · simpa [Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hreal :
        φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
    have hcast :
        (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) ≤
          (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
      exact_mod_cast hreal
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

omit [CompleteSpace H] in
/-- Helper for Proposition 12 28: the quadratic penalty belongs to `Γ₀(H)`. -/
private theorem quadraticPenalty_mem_gammaZero (x : H) :
    quadraticPenalty (H := H) x ∈ Γ₀(H) := by
  have hcont : Continuous fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    exact continuous_const.mul
      ((continuous_norm.comp (continuous_const.sub continuous_id)).pow 2)
  have hbase : _root_.ConvexOn ℝ Set.univ (fun z : H ↦ ‖z‖ ^ 2) :=
    (strictConvexOn_norm_sq (H := H)).convexOn
  have hconv : _root_.ConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    have hsq :
        ‖x - (a • y + b • z)‖ ^ 2 ≤ a * ‖x - y‖ ^ 2 + b * ‖x - z‖ ^ 2 := by
      have hrewrite :
          x - (a • y + b • z) = a • (x - y) + b • (x - z) := by
        calc
          x - (a • y + b • z) = (a + b) • x - (a • y + b • z) := by simp [hab]
          _ = a • x + b • x - (a • y + b • z) := by rw [add_smul]
          _ = a • (x - y) + b • (x - z) := by
            rw [smul_sub, smul_sub]
            abel_nf
      simpa [hrewrite] using
        hbase.2 (by simp : x - y ∈ (Set.univ : Set H)) (by simp : x - z ∈ (Set.univ : Set H))
          ha hb hab
    have htarget :
        (1 / 2 : ℝ) * ‖x - (a • y + b • z)‖ ^ 2 ≤
          a * ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) + b * ((1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
      nlinarith
    simpa [smul_eq_mul] using htarget
  simpa [quadraticPenalty, Function.toEReal_apply] using
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ (H := H)
      (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) hcont hconv

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 28: the quadratic penalty is finite everywhere. -/
private theorem effectiveDomain_quadraticPenalty_eq_univ (x : H) :
    effectiveDomain (quadraticPenalty (H := H) x) = Set.univ := by
  ext y
  simp [quadraticPenalty]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 28: the bundled proximal objective again belongs to `Γ₀(H)`. -/
private theorem proximalObjectiveIoi_mem_gammaZero_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    proximalObjectiveIoi (f := f) x ∈ Γ₀(H) := by
  have hquad : quadraticPenalty (H := H) x ∈ Γ₀(H) :=
    quadraticPenalty_mem_gammaZero (H := H) x
  rcases hf.2.nonempty with ⟨p, hp⟩
  have hdom : (effectiveDomain f ∩ effectiveDomain (quadraticPenalty (H := H) x)).Nonempty := by
    refine ⟨p, hp, ?_⟩
    simp [effectiveDomain_quadraticPenalty_eq_univ (H := H) x]
  simpa [proximalObjectiveIoi] using
    pointwiseAdd_mem_gammaZero f (quadraticPenalty (H := H) x) hf hquad hdom

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 28: a real-height epigraph point has finite base value. -/
private theorem mem_effectiveDomain_of_mem_real_epigraph_local
    {g : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph (fun y : H ↦ (g y : EReal))) :
    x ∈ effectiveDomain g := by
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hxξ) (EReal.coe_lt_top _)

/-- Helper for Proposition 12 28: the epigraph projection inequality yields an affine minorant on
the effective domain. -/
private theorem affine_minorant_on_effectiveDomain_of_projection_local
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain g) (hξ : ξ < (g x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (g y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hg) (x, ξ)) :
    let u : H := ((π - ξ)⁻¹) • (x - p)
    ∀ y ∈ effectiveDomain g,
      ((⟪y - p, u⟫_ℝ + (g p : EReal).toReal : ℝ) : EReal) ≤ (g y : EReal) := by
  have hproj_data :
      max (ξ : EReal) (g p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain g,
          ⟪y - p, x - p⟫_ℝ + ((g y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hg).mp
      hproj
  rcases hproj_data with ⟨hmax, hvar⟩
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (g y : EReal)) := by
    rw [hproj]
    exact projectionPoint_mem (epigraph (fun y : H ↦ (g y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hg) (x, ξ)
  have hp : p ∈ effectiveDomain g :=
    mem_effectiveDomain_of_mem_real_epigraph_local hp_mem_epigraph
  have hξ_le_pi : ξ ≤ π := by
    have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
      exact le_trans
        (show (ξ : EReal) ≤ max (ξ : EReal) (g p : EReal) from le_max_left _ _)
        hmax
    exact_mod_cast hξ_le_pi'
  have hgp_top : (g p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hgp_bot : (g p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (g p : EReal) > ⊥ from (g p).2)
  have hgp_le_pi : (g p : EReal).toReal ≤ π := by
    have hgp_le_pi' : (g p : EReal) ≤ (π : EReal) :=
      mem_epigraph_iff _ _ _ |>.mp hp_mem_epigraph
    have hcast :
        (((g p : EReal).toReal : ℝ) : EReal) ≤ (π : EReal) := by
      simpa [EReal.coe_toReal hgp_top hgp_bot] using hgp_le_pi'
    exact_mod_cast hcast
  have hξ_lt_pi : ξ < π := by
    by_cases hπξ : π = ξ
    · have hvarx :
          ⟪x - p, x - p⟫_ℝ + ((g x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        exact (real_inner_self_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ)
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hgp_le_xi : (g p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (g p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (g p : EReal) ≤ max (ξ : EReal) (g p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hgx_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
      have hgx_bot : (g x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (g x : EReal) > ⊥ from (g x).2)
      have hgx_le_xi : (g x : EReal).toReal ≤ ξ := by
        have hgx_le_xi' : (g x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hgp_le_xi
        have hcast :
            (((g x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hgx_top hgx_bot] using hgx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  dsimp
  intro y hy
  have hvar :
      ⟪y - p, x - p⟫_ℝ + ((g y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    hvar y hy
  have hgap_pos : 0 < π - ξ := sub_pos.mpr hξ_lt_pi
  have hinner_le :
      ⟪y - p, x - p⟫_ℝ ≤ ((g y : EReal).toReal - π) * (π - ξ) := by
    nlinarith
  have hscaled :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ ≤ (g y : EReal).toReal - π := by
    have hdiv : ⟪y - p, x - p⟫_ℝ / (π - ξ) ≤ (g y : EReal).toReal - π := by
      refine (div_le_iff₀ hgap_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
    simpa [div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hreal :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (g p : EReal).toReal ≤ (g y : EReal).toReal := by
    linarith
  have hgy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hgy_bot : (g y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (g y : EReal) > ⊥ from (g y).2)
  have hcast :
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (g p : EReal).toReal : ℝ) : EReal) ≤
        (((g y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_toReal hgy_top hgy_bot] using hcast

/-- Helper for Proposition 12 28: every `Γ₀(H)` function admits a continuous affine minorant. -/
private theorem exists_affine_minorant_of_mem_gammaZero_local
    (hf : f ∈ Γ₀(H)) :
    ∃ p ∈ effectiveDomain f, ∃ u : H, ∀ y : H,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  let ξ : ℝ := (f x : EReal).toReal - 1
  have hξ : ξ < (f x : EReal).toReal := by
    dsimp [ξ]
    linarith
  let z : H × ℝ :=
    projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  let p : H := z.1
  let π : ℝ := z.2
  have hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
    simp [p, π, z]
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    rw [hproj]
    exact projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph_local hp_mem_epigraph
  refine ⟨p, hp, ((π - ξ)⁻¹) • (x - p), ?_⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · exact affine_minorant_on_effectiveDomain_of_projection_local (g := f) hf hx hξ hproj y hy
  · rw [show (f y : EReal) = ⊤ by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))]
    exact le_top

/-- Helper for Proposition 12 28: the proximal objective is coercive because the quadratic term
dominates the affine minorant supplied above. -/
private theorem coercive_proximalObjective_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    Coercive (proximalObjective f x) := by
  rw [Coercive, EReal.tendsto_nhds_top_iff_real]
  rcases exists_affine_minorant_of_mem_gammaZero_local (f := f) hf with ⟨p, hp, u, hminorant⟩
  intro ξ
  let K : ℝ := ‖u‖ * ‖p‖ - (f p : EReal).toReal
  let R : ℝ := max (2 * ‖x‖) (max (16 * ‖u‖) (max (16 : ℝ) (|ξ| + |K| + 1)))
  have hR : ∀ᶠ y : H in Bornology.cobounded H, R ≤ ‖y‖ := by
    simpa [R] using
      (eventually_cobounded_le_norm R : ∀ᶠ y : H in Bornology.cobounded H, R ≤ ‖y‖)
  filter_upwards [hR] with y hyR
  have hyx : 2 * ‖x‖ ≤ ‖y‖ := le_trans (le_max_left _ _) hyR
  have hyu : 16 * ‖u‖ ≤ ‖y‖ := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hyR)
  have hybig : max (16 : ℝ) (|ξ| + |K| + 1) ≤ ‖y‖ := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hyR)
  have hy16 : (16 : ℝ) ≤ ‖y‖ := le_trans (le_max_left _ _) hybig
  have hyconst : |ξ| + |K| + 1 ≤ ‖y‖ := le_trans (le_max_right _ _) hybig
  have hy_le : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by congr 1; abel_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ = ‖x - y‖ + ‖x‖ := by rw [norm_sub_rev]
  have hxy : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
    linarith
  have hquad : ‖y‖ ^ 2 / 8 ≤ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith
  have hinner_abs : |⟪y - p, u⟫_ℝ| ≤ ‖y - p‖ * ‖u‖ := by
    simpa [mul_comm] using abs_real_inner_le_norm (y - p) u
  have hdist : ‖y - p‖ ≤ ‖y‖ + ‖p‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_sub_le y p
  have hinner :
      -‖u‖ * ‖y‖ - ‖u‖ * ‖p‖ ≤ ⟪y - p, u⟫_ℝ := by
    have hneg : -|⟪y - p, u⟫_ℝ| ≤ ⟪y - p, u⟫_ℝ := neg_abs_le _
    have hbound : |⟪y - p, u⟫_ℝ| ≤ ‖u‖ * ‖y‖ + ‖u‖ * ‖p‖ := by
      have hmul :
          ‖y - p‖ * ‖u‖ ≤ (‖y‖ + ‖p‖) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
      have htmp : |⟪y - p, u⟫_ℝ| ≤ (‖y‖ + ‖p‖) * ‖u‖ := le_trans hinner_abs hmul
      nlinarith
    nlinarith
  have hlinear : ‖u‖ * ‖y‖ ≤ ‖y‖ ^ 2 / 16 := by
    have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith
  have hquadratic : |ξ| + |K| + 1 ≤ ‖y‖ ^ 2 / 16 := by
    have hstep : ‖y‖ ≤ ‖y‖ ^ 2 / 16 := by
      have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
      nlinarith
    exact le_trans hyconst hstep
  have hquadratic' : ξ + K + 1 ≤ ‖y‖ ^ 2 / 16 := by
    have habs : ξ + K + 1 ≤ |ξ| + |K| + 1 := by
      nlinarith [le_abs_self ξ, le_abs_self K]
    exact le_trans habs hquadratic
  have hreal :
      ξ < ⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    dsimp [K] at hquadratic'
    linarith
  have hlower :
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) ≤
        proximalObjective f x y := by
    have hsum0 :=
      add_le_add_left (hminorant y) ((((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    calc
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal)
          =
            ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) +
              (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
                rw [EReal.coe_add]
      _ ≤ (f y : EReal) + (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := hsum0
      _ = proximalObjective f x y := by
            simp [proximalObjective]
  have hreal_cast :
      (ξ : EReal) <
        ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hreal
  exact lt_of_lt_of_le hreal_cast hlower

/-- Helper for Proposition 12 28: every `Γ₀(H)` function admits a proximal point at every base
point. -/
private theorem proximalPoints_nonempty_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    (proximalPoints f x).Nonempty := by
  have hgamma : proximalObjectiveIoi (f := f) x ∈ Γ₀(H) :=
    proximalObjectiveIoi_mem_gammaZero_of_mem_gammaZero (f := f) hf x
  have hcoercive : Coercive (proximalObjectiveIoi (f := f) x).asEReal := by
    simpa using coercive_proximalObjective_of_mem_gammaZero (f := f) hf x
  have hargmin :
      (Argmin (proximalObjectiveIoi (f := f) x).asEReal).Nonempty := by
    simpa using
      argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded
        (f := proximalObjectiveIoi (f := f) x) hgamma isClosed_univ convex_univ Set.univ_nonempty
        (Or.inl hcoercive)
  simpa [proximalPoints, proximalObjectiveIoi_apply (f := f)] using hargmin

/-- Helper for Proposition 12 28: choose one proximal point at each base point. The pairwise firm
inequality proved below shows that any such choice has the same firm-nonexpansive behavior. -/
private noncomputable def proximalSelection (hf : f ∈ Γ₀(H)) : H → H :=
  fun x ↦ Classical.choose (proximalPoints_nonempty_of_mem_gammaZero (f := f) hf x)

/-- Helper for Proposition 12 28: the selected point is indeed proximal. -/
private theorem proximalSelection_isProxPoint (hf : f ∈ Γ₀(H)) (x : H) :
    IsProxPoint f x (proximalSelection (f := f) hf x) :=
  Classical.choose_spec (proximalPoints_nonempty_of_mem_gammaZero (f := f) hf x)

local notation "Prox[" f ", " hf "]" => proximalSelection (f := f) hf

omit [CompleteSpace H] in
/-- Helper for Proposition 12 28: proximal points of a `Γ₀(H)` function lie in the effective
domain. -/
private theorem mem_effectiveDomain_of_isProxPoint
    (hf : f ∈ Γ₀(H)) {x p : H} (hp : IsProxPoint f x p) :
    p ∈ effectiveDomain f := by
  rcases hf.2.nonempty with ⟨q, hq⟩
  have hvar := (isProxPoint_iff_forall_inner_add_le f hf.2 x p).mp hp q
  by_contra hp_dom
  have hfp_top : (f p : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hp_dom))
  have hsum_top : (⟪q - p, x - p⟫_ℝ : EReal) + (f p : EReal) = ⊤ := by
    rw [hfp_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  rw [hsum_top] at hvar
  exact ne_of_lt (mem_effectiveDomain_iff.mp hq) (top_le_iff.mp hvar)

omit [CompleteSpace H] in
/-- Helper for Proposition 12 28: the proximal variational inequality becomes real-valued once
both comparison points are known to lie in the effective domain. -/
private theorem inner_add_toReal_le_toReal_of_isProxPoint
    (hf : f ∈ Γ₀(H)) {x p y : H} (hp : IsProxPoint f x p)
    (hy : y ∈ effectiveDomain f) :
    ⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f y : EReal).toReal := by
  have hp_dom : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_isProxPoint (f := f) hf hp
  have hvar := (isProxPoint_iff_forall_inner_add_le f hf.2 x p).mp hp y
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hcast :
      (((⟪y - p, x - p⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal)) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hfp_top hfp_bot, EReal.coe_toReal hfy_top hfy_bot, EReal.coe_add]
      using hvar
  exact_mod_cast hcast

omit [CompleteSpace H] in
/-- Helper for Proposition 12 28: proximal points at two base points satisfy the pairwise firm
inequality that characterizes firm nonexpansiveness. -/
private theorem prox_point_pairwise_firm_inequality
    (hf : f ∈ Γ₀(H)) {x y p q : H} (hp : IsProxPoint f x p) (hq : IsProxPoint f y q) :
    ‖p - q‖ ^ (2 : ℕ) ≤ inner ℝ (p - q) (x - y) := by
  have hp_dom : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_isProxPoint (f := f) hf hp
  have hq_dom : q ∈ effectiveDomain f :=
    mem_effectiveDomain_of_isProxPoint (f := f) hf hq
  have hpq :
      ⟪q - p, x - p⟫_ℝ + (f p : EReal).toReal ≤ (f q : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint (f := f) hf hp hq_dom
  have hqp :
      ⟪p - q, y - q⟫_ℝ + (f q : EReal).toReal ≤ (f p : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint (f := f) hf hq hp_dom
  have hsum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    linarith
  let d : H := p - q
  have hsub : y - q - (x - p) = d - (x - y) := by
    dsimp [d]
    abel_nf
  have hqpd : q - p = -d := by
    dsimp [d]
    abel_nf
  have hrewrite :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ =
        ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ
          = inner ℝ (-d) (x - p) + inner ℝ d (y - q) := by rw [hqpd]
      _ = -inner ℝ d (x - p) + inner ℝ d (y - q) := by simp
      _ = inner ℝ d (y - q) - inner ℝ d (x - p) := by ring_nf
      _ = inner ℝ d ((y - q) - (x - p)) := by
            symm
            rw [inner_sub_right]
      _ = inner ℝ d (d - (x - y)) := by rw [hsub]
      _ = inner ℝ d d - inner ℝ d (x - y) := by rw [inner_sub_right]
      _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hsum
  have hfinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (x - y) := by
    linarith
  simpa [d] using hfinal

-- Proof sketch: apply Proposition 12.26 at the proximal points of `x` and `y`, add the two
-- resulting variational inequalities, and rewrite the conclusion with the whole-space criterion
-- for firm nonexpansiveness.
/-- Proposition 12 28 (1): for `f ∈ Γ₀(H)`, the proximity operator `Prox_f` is firmly
nonexpansive. -/
theorem proximityOperator_firmlyNonexpansive_of_mem_gammaZero (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (Prox[f, hf]) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  exact prox_point_pairwise_firm_inequality (f := f) hf
    (proximalSelection_isProxPoint (f := f) hf x)
    (proximalSelection_isProxPoint (f := f) hf y)

-- Proof sketch: combine the first clause with Proposition 4.4, which identifies firm
-- nonexpansiveness of a map with firm nonexpansiveness of its residual map `Id - T`.
/-- Proposition 12.28 (2): for `f ∈ Γ₀(H)`, the residual map `Id - Prox_f` is firmly
nonexpansive. -/
theorem id_sub_proximityOperator_firmlyNonexpansive_of_mem_gammaZero (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (id - Prox[f, hf]) := by
  have hFirm :
      FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ Prox[f, hf] x) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using
      proximityOperator_firmlyNonexpansive_of_mem_gammaZero (f := f) hf
  rw [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ]
  simpa [residualMap] using
    (firmlyNonexpansiveOn_residualMap_iff
      (Set.univ : Set H) (fun x : Set.univ ↦ Prox[f, hf] x)).2 hFirm

end GammaZero

end ERealFunction
