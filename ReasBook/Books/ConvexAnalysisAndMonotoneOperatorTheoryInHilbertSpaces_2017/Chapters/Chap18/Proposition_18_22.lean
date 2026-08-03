import Mathlib.Data.List.TFAE
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap06.Proposition_6_16
import BauschkeLean.Chap06.Proposition_6_44
import BauschkeLean.Chap06.Proposition_6_47
import BauschkeLean.Chap07.Definition_7_1
import BauschkeLean.Chap07.Proposition_7_3
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open InnerProductSpace
open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.22 is the three-way equivalence between vanishing Gâteaux
  derivative of `Metric.infDist · C` at `x`, non-support-point membership, and the tangent-cone
  condition `T[C] x = univ`.
- `core/canonical`: the owner declarations are `Metric.infDist`, `spts`, `N[C] x`, `T[C] x`, and
  the Chapter 16/17 subdifferential and differentiability criteria.
- `bridge/view`: the companion theorems below connect the source-facing clauses to the canonical
  normal-cone owner `N[C] x = {0}` and then back to the project-facing tangent-cone notation.
- Semantic recall: `lean_leansearch` returned mathlib's `tangentConeAt`; this item keeps the
  project-facing tangent-cone notation `T[C] x` used by the surrounding API.
-/

/-- Companion to Proposition 18.22: at a point `x ∈ C`, not being a support point is exactly the
triviality of the normal cone `N[C] x`. -/
theorem not_mem_supportPoints_iff_normalCone_eq_singleton_zero
    {C : Set H} {x : H} (hx : x ∈ C) :
    x ∉ spts C ↔ N[C] x = ({0} : Set H) := by
  rw [supportPoints_eq_setOf_nontrivial_normalCone]
  change ¬ (N[C] x \ ({0} : Set H) ≠ ∅) ↔ N[C] x = ({0} : Set H)
  -- Rewrite support-point membership into punctured normal-cone nonemptiness.
  constructor
  · intro hx_not_support
    have hzero_mem : (0 : H) ∈ N[C] x := by
      rw [normalCone_of_mem hx]
      simp
    apply Set.eq_of_subset_of_subset
    · intro u hu
      by_cases hu0 : u = 0
      · simpa [hu0]
      · exfalso
        have hu_diff : u ∈ N[C] x \ ({0} : Set H) := by
          refine ⟨hu, ?_⟩
          simpa [Set.mem_singleton_iff, hu0]
        have hne : N[C] x \ ({0} : Set H) ≠ ∅ := by
          intro hEmpty
          have : u ∈ (∅ : Set H) := by
            simpa [hEmpty] using hu_diff
          exact this.elim
        exact hx_not_support hne
    · intro u hu
      rw [Set.mem_singleton_iff] at hu
      simpa [hu] using hzero_mem
  · intro hnormal
    intro hx_support
    apply hx_support
    ext u
    constructor
    · intro hu
      exfalso
      have hu_zero : u = 0 := by
        simpa [hnormal] using hu.1
      exact hu.2 (by simpa [Set.mem_singleton_iff, hu_zero])
    · intro hu
      exact False.elim hu

/-- Helper for Proposition 18.22: the distance-to-set map is convex on the ambient Hilbert space
for a nonempty closed convex set. -/
lemma convexOn_univ_infDist_of_nonempty_isClosed_convex_local
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    _root_.ConvexOn ℝ Set.univ (fun y : H ↦ Metric.infDist y C) := by
  let hC_cheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let P : H → H := P[C, hC_cheb]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hPx : P x ∈ C := projectionPoint_mem C hC_cheb x
  have hPy : P y ∈ C := projectionPoint_mem C hC_cheb y
  have hcombo_mem : a • P x + b • P y ∈ C := hC_convex hPx hPy ha hb hab
  have hdistx : Metric.infDist x C = ‖x - P x‖ := by
    simpa [P, dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb x).2.symm
  have hdisty : Metric.infDist y C = ‖y - P y‖ := by
    simpa [P, dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb y).2.symm
  -- Compare the distance of the convex combination with the convex combination of projections.
  calc
    Metric.infDist (a • x + b • y) C
        ≤ dist (a • x + b • y) (a • P x + b • P y) := by
            exact Metric.infDist_le_dist_of_mem hcombo_mem
    _ = ‖a • (x - P x) + b • (y - P y)‖ := by
          simp [P, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ ‖a • (x - P x)‖ + ‖b • (y - P y)‖ := norm_add_le _ _
    _ = a * ‖x - P x‖ + b * ‖y - P y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ = a * Metric.infDist x C + b * Metric.infDist y C := by
          rw [hdistx, hdisty]

/-- Helper for Proposition 18.22: the `EReal` coercion of the distance-to-set map belongs to
`Γ₀(H)` for a nonempty closed convex set. -/
lemma distanceToSet_toEReal_mem_gammaZero_of_nonempty_isClosed_convex
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (fun y : H ↦ Metric.infDist y C).toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity comes from continuity of the distance function.
    simpa [Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp (Metric.continuous_infDist_pt C)).lowerSemicontinuous
  · refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hreal :
        Metric.infDist (a • x + (1 - a) • y) C ≤
          a * Metric.infDist x C + (1 - a) * Metric.infDist y C := by
      simpa [smul_eq_mul] using
        (convexOn_univ_infDist_of_nonempty_isClosed_convex_local
          (H := H) hC_nonempty hC_closed hC_convex).2
          (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
    have hrealE :
        (((Metric.infDist (a • x + (1 - a) • y) C : ℝ) : EReal)) ≤
          (((a * Metric.infDist x C + (1 - a) * Metric.infDist y C : ℝ) : EReal)) := by
      exact_mod_cast hreal
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add, smul_eq_mul] using hrealE

/-- Helper for Proposition 18.22: subgradient membership for the distance-to-set map is exactly
the corresponding real-valued affine minorant inequality. -/
lemma distanceToSet_mem_subdifferential_iff_real_local
    {C : Set H} {x u : H} :
    u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x ↔
      ∀ y : H, inner ℝ (y - x) u + Metric.infDist x C ≤ Metric.infDist y C := by
  rw [ERealFunction.mem_subdifferential_iff]
  constructor
  · intro hu y
    -- All values of the distance function are finite, so the `EReal` inequality descends to `ℝ`.
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_add] using hu y)
  · intro hu y
    -- Conversely, package the real inequality back into the `EReal` owner surface.
    exact (EReal.coe_le_coe_iff).2 (by simpa [EReal.coe_add] using hu y)

/-- Helper for Proposition 18.22: at a point `x ∈ C`, subgradient membership for the
distance-to-set map is exactly the real-valued affine minorant inequality with zero base value. -/
lemma distanceToSet_mem_subdifferential_iff_zero_value_local
    {C : Set H} {x u : H} (hx : x ∈ C) :
    u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x ↔
      ∀ y : H, inner ℝ (y - x) u ≤ Metric.infDist y C := by
  rw [distanceToSet_mem_subdifferential_iff_real_local]
  simp [Metric.infDist_zero_of_mem hx]

/-- Helper for Proposition 18.22: normalizing a nonzero normal vector produces a point of
`N[C] x ∩ Metric.closedBall (0 : H) 1`. -/
lemma normalized_mem_normalCone_inter_closedBall_unit_of_nonzero
    {C : Set H} {x u : H} (hx : x ∈ C) (hu : u ∈ N[C] x) (hu_ne : u ≠ 0) :
    ‖u‖⁻¹ • u ∈ N[C] x ∩ Metric.closedBall (0 : H) 1 := by
  constructor
  · -- Rewrite the normal cone pointwise and scale the defining inequalities by `‖u‖⁻¹ ≥ 0`.
    rw [Set.normalCone_of_mem hx] at hu ⊢
    have hu_pointwise : ∀ y ∈ C, inner ℝ (y - x) u ≤ 0 :=
      (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := u) (p := x)).1 hu
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff
        (C := C) (u := ‖u‖⁻¹ • u) (p := x)).2 <| by
          intro y hy
          simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
            mul_nonpos_of_nonneg_of_nonpos
              (inv_nonneg.mpr (norm_nonneg u)) (hu_pointwise y hy)
  · -- The normalized vector lies on the unit sphere, hence in the closed unit ball.
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using (norm_smul_inv_norm hu_ne).le

/-- Helper for Proposition 18.22: at a point `x ∈ C`, every subgradient of the distance-to-set
map lies in `N[C] x ∩ Metric.closedBall (0 : H) 1`. -/
lemma mem_normalCone_inter_closedBall_of_mem_subdifferential_distanceToSet
    {C : Set H} {x u : H} (hx : x ∈ C)
    (hu : u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x) :
    u ∈ N[C] x ∩ Metric.closedBall (0 : H) 1 := by
  constructor
  · -- Testing the subgradient inequality on points of `C` recovers the normal-cone inequalities.
    rw [Set.normalCone_of_mem hx]
    apply (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := u) (p := x)).2
    intro y hy
    have hsubgrad :=
      (distanceToSet_mem_subdifferential_iff_zero_value_local
        (C := C) (x := x) (u := u) hx).1 hu y
    simpa [Metric.infDist_zero_of_mem hy] using hsubgrad
  · -- Evaluating the subgradient inequality at `x + u` bounds `‖u‖` by `1`.
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsubgrad :=
      (distanceToSet_mem_subdifferential_iff_zero_value_local
        (C := C) (x := x) (u := u) hx).1 hu (x + u)
    have hdist_le : Metric.infDist (x + u) C ≤ ‖u‖ := by
      have := Metric.infDist_le_dist_of_mem (x := x + u) (s := C) hx
      simpa [dist_eq_norm] using this
    have hnorm_sq_le : ‖u‖ ^ 2 ≤ ‖u‖ := by
      have hinner : inner ℝ ((x + u) - x) u = ‖u‖ ^ 2 := by
        simp [real_inner_self_eq_norm_sq]
      rw [hinner] at hsubgrad
      exact le_trans hsubgrad hdist_le
    have hnorm_le_one : ‖u‖ ≤ 1 := by
      nlinarith [norm_nonneg u, hnorm_sq_le]
    simpa using hnorm_le_one

/-- Helper for Proposition 18.22: a normal vector of norm at most `1` is a subgradient of the
distance-to-set map at the in-set point `x`. -/
lemma mem_subdifferential_distanceToSet_of_mem_normalCone_inter_closedBall
    {C : Set H} {x u : H} (hx : x ∈ C)
    (huN : u ∈ N[C] x) (huBall : u ∈ Metric.closedBall (0 : H) 1) :
    u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x := by
  rw [distanceToSet_mem_subdifferential_iff_zero_value_local (C := C) (x := x) (u := u) hx]
  have hu_pointwise : ∀ z ∈ C, inner ℝ (z - x) u ≤ 0 := by
    rw [Set.normalCone_of_mem hx] at huN
    exact (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := u) (p := x)).1 huN
  have hu_norm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using huBall
  intro y
  rw [Metric.le_infDist ⟨x, hx⟩]
  intro z hz
  calc
    inner ℝ (y - x) u = inner ℝ (y - z) u + inner ℝ (z - x) u := by
      have hsplit : y - x = (y - z) + (z - x) := by abel
      rw [hsplit, inner_add_left]
    _ ≤ inner ℝ (y - z) u := by linarith [hu_pointwise z hz]
    _ ≤ ‖y - z‖ * ‖u‖ := by exact real_inner_le_norm _ _
    _ ≤ ‖y - z‖ := by nlinarith [norm_nonneg (y - z), hu_norm]
    _ = dist y z := by rw [dist_eq_norm]

/-- Helper for Proposition 18.22: vanishing Gâteaux derivative forces every normal vector at
`x ∈ C` to be zero. -/
lemma eq_zero_of_mem_normalCone_of_distanceToSet_hasGateauxDerivativeAt_zero
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x u : H} (hx : x ∈ C)
    (hgrad :
      HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDualMap ℝ H (0 : H)) x)
    (hu : u ∈ N[C] x) :
    u = 0 := by
  by_cases hu_zero : u = 0
  · exact hu_zero
  · have hw_mem :
        ‖u‖⁻¹ • u ∈ N[C] x ∩ Metric.closedBall (0 : H) 1 :=
        normalized_mem_normalCone_inter_closedBall_unit_of_nonzero hx hu hu_zero
    have hw_sub :
        ‖u‖⁻¹ • u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x := by
      -- Reconstruct the in-set subgradient bridge directly from the source inequalities.
      exact
        mem_subdifferential_distanceToSet_of_mem_normalCone_inter_closedBall
          (C := C) hx hw_mem.1 hw_mem.2
    have hw_norm : ‖‖u‖⁻¹ • u‖ = 1 := by
      simpa using norm_smul_inv_norm hu_zero
    have hquot_tendsto :
        Filter.Tendsto
          (fun α : ℝ ↦ (Metric.infDist (x + α • (‖u‖⁻¹ • u)) C - Metric.infDist x C) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      -- The zero Gâteaux derivative forces every one-sided directional quotient to tend to `0`.
      simpa [one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        hgrad.tendsto_directionalDifferenceQuotient (‖u‖⁻¹ • u)
    have hsmall :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (Metric.infDist (x + α • (‖u‖⁻¹ • u)) C - Metric.infDist x C) / α < 1 / 2 := by
      exact hquot_tendsto (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    have hlarge :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          1 ≤ (Metric.infDist (x + α • (‖u‖⁻¹ • u)) C - Metric.infDist x C) / α := by
      filter_upwards [self_mem_nhdsWithin] with α hα
      have hα_pos : 0 < α := hα
      have hminorant :=
        (distanceToSet_mem_subdifferential_iff_zero_value_local
          (C := C) (x := x) (u := ‖u‖⁻¹ • u) hx).1 hw_sub
          (x + α • (‖u‖⁻¹ • u))
      have hα_le :
          α ≤ Metric.infDist (x + α • (‖u‖⁻¹ • u)) C := by
        have hinner :
            inner ℝ ((x + α • (‖u‖⁻¹ • u)) - x) (‖u‖⁻¹ • u) = α := by
          rw [show (x + α • (‖u‖⁻¹ • u)) - x = α • (‖u‖⁻¹ • u) by abel]
          rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hw_norm]
          ring
        rw [hinner] at hminorant
        exact hminorant
      have hquot_ge :
          1 ≤ Metric.infDist (x + α • (‖u‖⁻¹ • u)) C / α := by
        have htmp : 1 * α ≤ Metric.infDist (x + α • (‖u‖⁻¹ • u)) C := by
          simpa using hα_le
        exact (le_div_iff₀ hα_pos).2 htmp
      simpa [Metric.infDist_zero_of_mem hx] using hquot_ge
    have hcontr : ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), False := by
      filter_upwards [hsmall, hlarge] with α hlt hge
      linarith
    have hne : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioi]
      simp
    have : False := by
      exact hne.ne (Filter.eventually_false_iff_eq_bot.mp hcontr)
    exact False.elim this

/-- Helper for Proposition 18.22: if the normal cone at an in-set point is `{0}`, then the
subdifferential of the distance-to-set map also collapses to `{0}` there. -/
lemma subdifferential_distanceToSet_eq_singleton_zero_of_normalCone_eq_singleton_zero_local
    {C : Set H} {x : H} (hx : x ∈ C) (hnormal : N[C] x = ({0} : Set H)) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x = ({0} : Set H) := by
  apply Set.Subset.antisymm
  · intro u hu
    have hu_normal :
        u ∈ N[C] x :=
      (mem_normalCone_inter_closedBall_of_mem_subdifferential_distanceToSet
        (C := C) (x := x) hx hu).1
    have hu_zero : u = 0 := by
      simpa [hnormal] using hu_normal
    simpa [hu_zero]
  · intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst u
    have hzero_normal : (0 : H) ∈ N[C] x := by
      rw [normalCone_of_mem hx]
      simp
    have hzero_ball : (0 : H) ∈ Metric.closedBall (0 : H) 1 := by
      simp [Metric.mem_closedBall, dist_eq_norm]
    simpa using
      mem_subdifferential_distanceToSet_of_mem_normalCone_inter_closedBall
        (C := C) (x := x) hx hzero_normal hzero_ball

/-- Helper for Proposition 18.22: if the tangent cone at `x ∈ C` is the whole space, then every
direction can be approximated by a cone ray inside `C - {x}`, forcing the distance quotient to
vanish. -/
lemma distanceToSet_hasGateauxDerivativeAt_zero_of_tangentCone_eq_univ_local
    {C : Set H} (hC_convex : Convex ℝ C) {x : H} (hx : x ∈ C)
    (htangent : T[C] x = (univ : Set H)) :
    HasGateauxDerivativeAt
      (fun y ↦ Metric.infDist y C)
      (toDualMap ℝ H (0 : H)) x := by
  rw [hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient]
  intro y
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hy_tangent : y ∈ T[C] x := by
    simpa [htangent]
  rw [tangentCone_of_mem hx] at hy_tangent
  have htranslate_convex : Convex ℝ (C - ({x} : Set H)) := by
    simpa [sub_eq_add_neg] using hC_convex.add (convex_singleton (-x))
  rcases Metric.mem_closure_iff.1 hy_tangent ε hε with ⟨v, hv_cone, hv_close⟩
  rcases (mem_cone_iff_exists_pos_smul_mem htranslate_convex).1 hv_cone with ⟨a, ha_pos, hv_mem⟩
  rcases hv_mem with ⟨w, hw_mem, rfl⟩
  rcases hw_mem with ⟨c, hc, z, hz, rfl⟩
  have hz_eq : z = x := by
    simpa using hz
  subst z
  have hsmall :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α < min 1 a⁻¹ := by
    have hmin_pos : 0 < min 1 a⁻¹ := by
      exact lt_min (by norm_num) (inv_pos.mpr ha_pos)
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hmin_pos)
  filter_upwards [self_mem_nhdsWithin, hsmall] with α hαpos hαsmall
  have hα_pos : 0 < α := hαpos
  have hαa_nonneg : 0 ≤ α * a := by
    positivity
  have hαa_le : α * a ≤ 1 := by
    have hα_lt_inv : α < a⁻¹ := lt_of_lt_of_le hαsmall (min_le_right _ _)
    have hmul_lt : α * a < 1 := by
      have := mul_lt_mul_of_pos_right hα_lt_inv ha_pos
      simpa [inv_mul_cancel₀ ha_pos.ne'] using this
    linarith
  have hline_mem : AffineMap.lineMap x c (α * a) ∈ C := by
    simpa [AffineMap.lineMap_apply_module] using
      hC_convex hx hc (sub_nonneg.mpr hαa_le) hαa_nonneg (by ring)
  have hcone_point_mem : x + α • (a • (c - x)) ∈ C := by
    simpa [AffineMap.lineMap_apply_module', smul_smul, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hline_mem
  have hdist_le :
      Metric.infDist (x + α • y) C ≤ dist (x + α • y) (x + α • (a • (c - x))) := by
    exact Metric.infDist_le_dist_of_mem hcone_point_mem
  have hdist_eq :
      dist (x + α • y) (x + α • (a • (c - x))) = α * dist y (a • (c - x)) := by
    calc
      dist (x + α • y) (x + α • (a • (c - x))) = dist (α • y) (α • (a • (c - x))) := by
        rw [show x + α • y = α • y - (-x) by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]]
        rw [show x + α • (a • (c - x)) = α • (a • (c - x)) - (-x) by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]]
        exact dist_sub_right _ _ (-x)
      _ = ‖α • y - α • (a • (c - x))‖ := by
            rw [dist_eq_norm]
      _ = ‖α • (y - a • (c - x))‖ := by
            rw [← smul_sub]
      _ = α * ‖y - a • (c - x)‖ := by
            rw [norm_smul, Real.norm_of_nonneg hα_pos.le]
      _ = α * dist y (a • (c - x)) := by
            rw [dist_eq_norm]
  have hquot_le : Metric.infDist (x + α • y) C / α ≤ dist y (a • (c - x)) := by
    exact (div_le_iff₀ hα_pos).2 (by simpa [hdist_eq, mul_comm, mul_left_comm, mul_assoc] using hdist_le)
  have hquot_lt : Metric.infDist (x + α • y) C / α < ε := by
    exact lt_of_le_of_lt hquot_le (by simpa [dist_comm] using hv_close)
  have hquot_nonneg : 0 ≤ Metric.infDist (x + α • y) C / α := by
    exact div_nonneg (Metric.infDist_nonneg) hα_pos.le
  simpa [Metric.infDist_zero_of_mem hx, dist_eq_norm, Real.norm_eq_abs, smul_eq_mul, one_div,
    div_eq_mul_inv, abs_of_nonneg Metric.infDist_nonneg, abs_of_pos hα_pos,
    abs_of_nonneg hquot_nonneg, mul_comm, mul_left_comm, mul_assoc] using hquot_lt

/-- Companion to Proposition 18.22: for a closed convex set, the distance function has Gâteaux
derivative `0` at `x ∈ C` exactly when the normal cone `N[C] x` is trivial. -/
theorem distanceToSet_hasGateauxDerivativeAt_zero_iff_normalCone_eq_singleton_zero
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDualMap ℝ H (0 : H)) x ↔
      N[C] x = ({0} : Set H) := by
  constructor
  · intro hgrad
    apply Set.eq_of_subset_of_subset
    · intro u hu
      -- The source route closes the normal cone by ruling out every nonzero normal vector.
      simpa [Set.mem_singleton_iff] using
        eq_zero_of_mem_normalCone_of_distanceToSet_hasGateauxDerivativeAt_zero
          (H := H) hC_closed hC_convex hx hgrad hu
    · intro u hu
      rw [Set.mem_singleton_iff] at hu
      simpa [hu] using (show (0 : H) ∈ N[C] x by
        rw [normalCone_of_mem hx]
        simp)
  · intro hnormal
    -- Route correction: the source file factors `(iii) → (i)` through a differentiability
    -- owner that is unavailable in the current Lake state, so we close the same tangent-cone
    -- architecture directly by approximating each direction with cone rays from `C - {x}`.
    have htangent : T[C] x = (univ : Set H) := by
      exact (tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem hC_convex hx).2 hnormal
    exact
      distanceToSet_hasGateauxDerivativeAt_zero_of_tangentCone_eq_univ_local
        (H := H) hC_convex hx htangent

/-- Clauses (i) and (ii) of Proposition 18.22: for a closed convex set, the distance function has
Gâteaux derivative `0` at `x ∈ C` exactly when `x` is not a support point. -/
theorem distanceToSet_hasGateauxDerivativeAt_zero_iff_not_mem_supportPoints
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDualMap ℝ H (0 : H)) x ↔
      x ∉ spts C := by
  -- Compose the distance/normal-cone bridge with the support-point/normal-cone equivalence.
  calc
    HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDualMap ℝ H (0 : H)) x ↔
      N[C] x = ({0} : Set H) := by
        exact
          distanceToSet_hasGateauxDerivativeAt_zero_iff_normalCone_eq_singleton_zero
            hC_closed hC_convex hx
    _ ↔ x ∉ spts C := by
        exact (not_mem_supportPoints_iff_normalCone_eq_singleton_zero hx).symm

/-- Clauses (i) and (iii) of Proposition 18.22: for a closed convex set, the distance function has
Gâteaux derivative `0` at `x ∈ C` exactly when `T[C] x = univ`. -/
theorem distanceToSet_hasGateauxDerivativeAt_zero_iff_tangentCone_eq_univ
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDualMap ℝ H (0 : H)) x ↔
      T[C] x = (univ : Set H) := by
  -- Compose the distance/normal-cone bridge with the tangent/normal-cone equivalence.
  calc
    HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDualMap ℝ H (0 : H)) x ↔
      N[C] x = ({0} : Set H) := by
        exact
          distanceToSet_hasGateauxDerivativeAt_zero_iff_normalCone_eq_singleton_zero
            hC_closed hC_convex hx
    _ ↔ T[C] x = (univ : Set H) := by
        exact
          (tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem hC_convex hx).symm

/-- Proposition 18.22: for a closed convex subset `C` of a real Hilbert space and `x ∈ C`, the
following are equivalent: the distance function to `C` has Gâteaux derivative `0` at `x`, the
point `x` is not a support point of `C`, and the tangent cone `T[C] x` is the whole space. -/
theorem distanceToSet_zeroGateauxDerivative_tfae_not_mem_supportPoints_tangentCone_eq_univ
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    List.TFAE
      [ HasGateauxDerivativeAt
          (fun y ↦ Metric.infDist y C)
          (toDualMap ℝ H (0 : H)) x,
        x ∉ spts C,
        T[C] x = (univ : Set H) ] := by
  -- Link each source-facing clause back to the common owner condition from the previous theorems.
  tfae_have 1 ↔ 2 := by
    exact
      distanceToSet_hasGateauxDerivativeAt_zero_iff_not_mem_supportPoints
        hC_closed hC_convex hx
  tfae_have 1 ↔ 3 := by
    exact
      distanceToSet_hasGateauxDerivativeAt_zero_iff_tangentCone_eq_univ
        hC_closed hC_convex hx
  tfae_finish

end

end Set
