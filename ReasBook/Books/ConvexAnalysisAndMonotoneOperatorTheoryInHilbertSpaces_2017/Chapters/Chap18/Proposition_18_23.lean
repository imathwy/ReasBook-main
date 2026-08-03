import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap04.Proposition_4_16
import BauschkeLean.Chap06.Proposition_6_45
import BauschkeLean.Chap07.Definition_7_1
import BauschkeLean.Chap07.Proposition_7_3
import BauschkeLean.Chap16.Example_16_62
import BauschkeLean.Chap18.Proposition_18_22
import BauschkeLean.Chap17.Proposition_17_31
import BauschkeLean.Chap17.Proposition_17_41

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open SetValuedOperator
open scoped Gradient InnerProductSpace
open scoped Topology

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 18 23: the distance-to-set map is convex on the ambient Hilbert space
for a nonempty closed convex set. -/
lemma convexOn_univ_infDist_of_nonempty_isClosed_convex
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

/-- Helper for Proposition 18 23: for a nonempty closed convex set, the `EReal` coercion of the
distance-to-set function belongs to `Γ₀(H)`. -/
lemma distanceToSet_toEReal_mem_gammaZero_of_nonempty_isClosed_convex
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (fun y : H ↦ Metric.infDist y C).toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · simpa [Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp (Metric.continuous_infDist_pt C)).lowerSemicontinuous
  · refine ⟨?_, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy a ha0 ha1
      have h1ma : 0 ≤ 1 - a := sub_nonneg.mpr ha1.le
      have hsum : a + (1 - a) = 1 := by linarith
      have hreal :
          Metric.infDist (a • x + (1 - a) • y) C ≤
            a * Metric.infDist x C + (1 - a) * Metric.infDist y C := by
        simpa [smul_eq_mul] using
          (convexOn_univ_infDist_of_nonempty_isClosed_convex
            hC_nonempty hC_closed hC_convex).2
            (by simp) (by simp) ha0.le h1ma hsum
      have hrealE :
          (((Metric.infDist (a • x + (1 - a) • y) C : ℝ) : EReal)) ≤
            (((a * Metric.infDist x C + (1 - a) * Metric.infDist y C : ℝ) : EReal)) := by
        exact_mod_cast hreal
      simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add, smul_eq_mul] using hrealE

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.23 records the interior, boundary, and exterior
  differentiability behavior of `x ↦ Metric.infDist x C`.
- `core/canonical`: the owner abstractions are `Metric.infDist`, `HasGradientAt`,
  `DifferentiableAt`, `GateauxDifferentiableAt`, `spts`, and the metric projection `P_C`.
- `bridge/view`: the current file keeps only the source-facing proposition clauses, avoiding the
  unstable helper-owner layer that presently rebuilds through unrelated broken dependencies. -/

-- Proof sketch: if `x ∈ interior C`, then some open ball around `x` lies in `C`, so
-- `Metric.infDist · C` vanishes on a neighborhood of `x`. The distance function is therefore
-- locally constant at `x`, hence Fréchet differentiable there with gradient `0`.
/-- Proposition 18 23 (1): clause (i). At an interior point of `C`, the distance function to `C`
is Fréchet differentiable with gradient `0`. -/
theorem distanceToSet_hasGradientAt_zero_of_mem_interior
    {C : Set H} {x : H} (hx : x ∈ interior C) :
    HasGradientAt (fun y ↦ Metric.infDist y C) (0 : H) x := by
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨r, hr, hball⟩
  have hzero :
      (fun y : H ↦ Metric.infDist y C) =ᶠ[𝓝 x] fun _ : H ↦ (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    exact Metric.infDist_zero_of_mem (hball hy)
  simpa using (hasGradientAt_const (x := x) (c := (0 : ℝ))).congr_of_eventuallyEq hzero

section

variable {C : Set H}
variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
include hC_closed hC_convex

/-- Helper for Proposition 18 23: a point of a closed convex set that is not a support point
has vanishing Gâteaux derivative for the distance-to-set map. -/
lemma distanceToSet_hasGateauxDerivativeAt_zero_of_not_mem_supportPoints
    {x : H} (hx : x ∈ C) (hx_support : x ∉ spts C) :
    HasGateauxDerivativeAt
      (fun y ↦ Metric.infDist y C)
      (InnerProductSpace.toDualMap ℝ H (0 : H)) x := by
  -- Route correction: keep the boundary argument on the Proposition 18.22 owner theorem instead
  -- of re-unpacking the equivalence inside each contradiction proof.
  simpa using
    (distanceToSet_hasGateauxDerivativeAt_zero_iff_not_mem_supportPoints
      hC_closed hC_convex hx).2 hx_support

-- Proof sketch: Proposition 18.22 gives the Gâteaux derivative `0` at `x` from
-- `x ∉ spts C`. The source proof then combines the boundary behavior of nearby exterior
-- subgradients to show that this Gâteaux differentiability cannot upgrade to Fréchet
-- differentiability at a boundary point.
/-- Clause (ii)(a) of Proposition 18 23: at a boundary point of a closed convex set
that is not a support point, the distance function fails to be Fréchet differentiable. -/
theorem distanceToSet_not_differentiableAt_of_mem_frontier_and_not_mem_supportPoints
    {x : H} (hx : x ∈ frontier C) (hx_support : x ∉ spts C) :
    ¬ DifferentiableAt ℝ (fun y ↦ Metric.infDist y C) x := by
  intro hdiff
  let f : H → Set.Ioi (⊥ : EReal) := (fun y : H ↦ Metric.infDist y C).toEReal
  have hxC : x ∈ C := (frontier_subset_iff_isClosed.mpr hC_closed) hx
  have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
  have hf : f ∈ Γ₀(H) := by
    simpa [f] using
      distanceToSet_toEReal_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed
        hC_convex
  have hx_int_eff : x ∈ interior (effectiveDomain f) := by
    simp [f, Function.effectiveDomain_toEReal]
  have hgrad :
      HasGradientAt
        (fun y : H ↦ Metric.infDist y C)
        (∇ (fun y : H ↦ Metric.infDist y C) x) x := by
    simpa using hdiff.hasGradientAt
  have hsub_grad :
      (∂ f) x = ({∇ (fun y : H ↦ Metric.infDist y C) x} : Set H) := by
    simpa [f] using subdifferential_eq_singleton_of_hasGradientAt hf hx_int_eff hgrad
  -- Reuse the Proposition 18.22 owner theorem rather than maintaining a second local adapter.
  have hgateaux0 :
      HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (InnerProductSpace.toDualMap ℝ H (0 : H)) x :=
    distanceToSet_hasGateauxDerivativeAt_zero_of_not_mem_supportPoints
      (hC_closed := hC_closed) (hC_convex := hC_convex) hxC hx_support
  have hxeff : x ∈ effectiveDomain f := by
    simp [f, Function.effectiveDomain_toEReal]
  have hsub_zero : (∂ f) x = ({0} : Set H) := by
    simpa [f] using
      subdifferential_eq_singleton_of_hasGateauxDerivativeAt
        (f := f) (x := x) hxeff (0 : H) hgateaux0
  have hgrad_zero : ∇ (fun y : H ↦ Metric.infDist y C) x = (0 : H) := by
    apply Set.singleton_injective
    rw [← hsub_zero, hsub_grad]
  have hgrad_zero' : HasGradientAt (fun y : H ↦ Metric.infDist y C) (0 : H) x := by
    simpa [hgrad_zero] using hgrad
  rcases
      subdifferential_subset_closedBall_of_hasGradientAt hf hx_int_eff hgrad_zero'
        (1 / 2) (by norm_num) with
    ⟨δ, hδ_pos, hδball⟩
  have hx_closure_compl : x ∈ closure (Cᶜ) := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  rcases Metric.mem_closure_iff.1 hx_closure_compl δ hδ_pos with ⟨y, hy, hy_dist⟩
  have hy_ball : y ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball, dist_comm] using hy_dist
  have hv_sub :
      ((Metric.infDist y C)⁻¹ •
          (y - P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] y)) ∈
        (∂ f) y := by
    rw [subdifferential_distanceToSet_eq_singleton_normalizedResidual_of_not_mem
      (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex) hy]
    simp
  have hv_ball :
      ((Metric.infDist y C)⁻¹ •
          (y - P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] y)) ∈
        Metric.closedBall (0 : H) (1 / 2) :=
    hδball y hy_ball hv_sub
  have hv_le :
      ‖(Metric.infDist y C)⁻¹ •
          (y - P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] y)‖ ≤
        1 / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv_ball
  have hres_norm :
      ‖y - P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] y‖ =
        Metric.infDist y C := by
    exact projection_residual_norm_eq_infDist
      (C := C) hC_nonempty hC_closed hC_convex y
  have hy_dist_pos : 0 < Metric.infDist y C := by
    simpa using (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hy
  have hres_ne :
      y - P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] y ≠ 0 := by
    intro hzero
    have hnorm_zero :
        ‖y - P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] y‖ =
          0 := by
      simp [hzero]
    rw [hres_norm] at hnorm_zero
    exact hy_dist_pos.ne' hnorm_zero
  have hv_norm :
      ‖(Metric.infDist y C)⁻¹ •
          (y - P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] y)‖ =
        1 := by
    simpa [hres_norm] using norm_smul_inv_norm hres_ne
  linarith

-- Proof sketch: at a boundary support point, the distance subdifferential contains both `0`
-- and a nonzero normalized support direction, so the distance function cannot be Gâteaux
-- differentiable there.
/-- Clause (ii)(b) of Proposition 18 23: at a boundary support point of a closed convex
set, the distance function is not Gâteaux differentiable. -/
theorem distanceToSet_not_gateauxDifferentiableAt_of_mem_frontier_and_mem_supportPoints
    {x : H} (hx : x ∈ frontier C) (hx_support : x ∈ spts C) :
    ¬ _root_.GateauxDifferentiableAt (fun y ↦ Metric.infDist y C) x := by
  intro hgateaux
  rcases hgateaux with ⟨A, hA⟩
  let f : H → Set.Ioi (⊥ : EReal) := (fun y : H ↦ Metric.infDist y C).toEReal
  let u : H := (InnerProductSpace.toDual ℝ H).symm A
  have hxC : x ∈ C := (frontier_subset_iff_isClosed.mpr hC_closed) hx
  have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
  have hdist_conv : ConvexOn f (effectiveDomain f) := by
    simpa [f] using
      (distanceToSet_toEReal_mem_gammaZero_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).2
  have hxeff : x ∈ effectiveDomain f := by
    simp [f, Function.effectiveDomain_toEReal]
  have hAeq : InnerProductSpace.toDualMap ℝ H u = A := by
    change (InnerProductSpace.toDual ℝ H) u = A
    simp [u]
  have hA' :
      HasGateauxDerivativeAt
        (fun y ↦ (f y : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H u) x := by
    rw [hAeq]
    simpa [f, Function.toEReal_apply] using hA
  have hsub_single : (∂ f) x = ({u} : Set H) := by
    simpa [f, u] using
      subdifferential_eq_singleton_of_hasGateauxDerivativeAt
        (f := f) (x := x) hxeff u hA'
  have hzero_sub : (0 : H) ∈ (∂ f) x := by
    rw [subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
      hC_closed hC_convex hx]
    constructor
    · rw [normalCone_of_mem hxC]
      simp [innerSupremumOn_eq_sSup_image]
    · simp [Metric.mem_closedBall]
  have hnontrivial : N[C] x \ ({0} : Set H) ≠ ∅ := by
    rw [supportPoints_eq_setOf_nontrivial_normalCone] at hx_support
    exact hx_support
  obtain ⟨w, hw_ne, hw_inner⟩ :=
    (normalCone_diff_singleton_nonempty_iff_exists_nonzero (C := C) (x := x) hxC).1 hnontrivial
  have hw_normal : w ∈ N[C] x := by
    rw [normalCone_of_mem hxC]
    exact hw_inner
  have hw_sub : (‖w‖⁻¹ • w) ∈ (∂ f) x := by
    rw [subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
      hC_closed hC_convex hx]
    constructor
    · rw [normalCone_of_mem hxC] at hw_normal ⊢
      have hw_pointwise :
          ∀ y ∈ C, ⟪y - x, w⟫_ℝ ≤ 0 :=
        (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := w) (p := x)).1 hw_normal
      exact
        (innerSupremumOn_sub_singleton_le_zero_iff
          (C := C) (u := ‖w‖⁻¹ • w) (p := x)).2
          (fun y hy ↦ by
            simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
              mul_nonpos_of_nonneg_of_nonpos
                (inv_nonneg.mpr (norm_nonneg w)) (hw_pointwise y hy))
    · rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using (norm_smul_inv_norm hw_ne).le
  have hu_zero : u = (0 : H) := by
    have : (0 : H) ∈ ({u} : Set H) := by
      simpa [hsub_single] using hzero_sub
    simpa using this.symm
  have hw_zero : ‖w‖⁻¹ • w = (0 : H) := by
    have : ‖w‖⁻¹ • w ∈ ({u} : Set H) := by
      simpa [hsub_single] using hw_sub
    simpa [hu_zero] using this
  have hw_norm : ‖‖w‖⁻¹ • w‖ = 1 := by
    simpa using norm_smul_inv_norm hw_ne
  have : False := by
    have hnorm_zero : ‖‖w‖⁻¹ • w‖ = 0 := by
      simp [hw_zero]
    rw [hw_norm] at hnorm_zero
    exact one_ne_zero hnorm_zero
  exact this

end

section

variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" => P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]

-- Proof sketch: away from `C`, the source formula identifies the gradient of the distance
-- function with the normalized projection residual.
/-- Clause (iii) of Proposition 18 23: outside a nonempty closed convex set, the distance
function is Fréchet differentiable with gradient given by the normalized residual
`(Metric.infDist x C)⁻¹ • (x - P_C x)`. -/
theorem distanceToSet_hasGradientAt_normalized_residual_of_not_mem
    {x : H} (hx : x ∉ C) :
    HasGradientAt (fun y ↦ Metric.infDist y C) ((Metric.infDist x C)⁻¹ • (x - P x)) x := by
  let f : H → Set.Ioi (⊥ : EReal) := (fun y : H ↦ Metric.infDist y C).toEReal
  let hC_cheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let proj : H → H := P[C, hC_cheb]
  have hdist_pos : 0 < Metric.infDist x C := by
    simpa using (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
  have hf : f ∈ Γ₀(H) := by
    simpa [f] using
      distanceToSet_toEReal_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed
        hC_convex
  have hx_int_eff : x ∈ interior (effectiveDomain f) := by
    simp [f, Function.effectiveDomain_toEReal]
  have hsub :
      (∂ f) x = ({(Metric.infDist x C)⁻¹ • (x - proj x)} : Set H) := by
    simpa [f, proj] using
      subdifferential_distanceToSet_eq_singleton_normalizedResidual_of_not_mem
        (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex) hx
  classical
  let G : Selection (∂ f) := fun z ↦
    if hz : (z : H) ∉ C then
      ⟨(Metric.infDist (z : H) C)⁻¹ • ((z : H) - proj (z : H)), by
        rw [subdifferential_distanceToSet_eq_singleton_normalizedResidual_of_not_mem
          (hC_nonempty := hC_nonempty) (hC_closed := hC_closed) (hC_convex := hC_convex) hz]
        simp [proj]⟩
    else by
      let hzdom :=
        (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := (z : H))).1 z.property
      let w : H := Classical.choose hzdom
      exact ⟨w, Classical.choose_spec hzdom⟩
  have hG :
      SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ (G z : H)) x := by
    intro hxdom
    let x0 : (∂ f).dom := ⟨x, hxdom⟩
    let R : (∂ f).dom → H := fun z ↦ (Metric.infDist (z : H) C)⁻¹ • ((z : H) - proj (z : H))
    have hproj_lipschitz : LipschitzWith 1 proj := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro y z
      have hnorm_le : ‖proj y - proj z‖ ≤ ‖y - z‖ := by
        by_cases hyz : proj y = proj z
        · simp [hyz]
        · have hfirm :
              ‖proj y - proj z‖ ^ 2 ≤ ⟪proj y - proj z, y - z⟫_ℝ := by
            simpa [proj] using
              norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
                hC_nonempty hC_closed hC_convex y z
          have hmul :
              ‖proj y - proj z‖ * ‖proj y - proj z‖ ≤ ‖proj y - proj z‖ * ‖y - z‖ := by
            simpa [pow_two] using le_trans hfirm (real_inner_le_norm (proj y - proj z) (y - z))
          have hnorm_pos : 0 < ‖proj y - proj z‖ := by
            exact norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
          exact le_of_mul_le_mul_left hmul hnorm_pos
      simpa [dist_eq_norm] using hnorm_le
    have hR_cont : ContinuousAt R x0 := by
      have hdist_inv :
          ContinuousAt (fun z : (∂ f).dom ↦ (Metric.infDist (z : H) C)⁻¹) x0 := by
        apply ContinuousAt.inv₀
        · exact
            (Metric.continuous_infDist_pt C).continuousAt.comp
              continuous_subtype_val.continuousAt
        · exact hdist_pos.ne'
      have hres_cont :
          ContinuousAt (fun z : (∂ f).dom ↦ (z : H) - proj (z : H)) x0 := by
        exact continuous_subtype_val.continuousAt.sub
          (hproj_lipschitz.continuous.continuousAt.comp
            continuous_subtype_val.continuousAt)
      exact hdist_inv.smul hres_cont
    let r : ℝ := Metric.infDist x C / 2
    have hr_pos : 0 < r := by
      dsimp [r]
      exact half_pos hdist_pos
    have hGR :
        (fun z : (∂ f).dom ↦ (G z : H)) =ᶠ[𝓝 x0] R := by
      filter_upwards [Metric.ball_mem_nhds x0 hr_pos] with z hz
      have hz_out : (z : H) ∉ C := by
        intro hzC
        have hle : Metric.infDist x C ≤ dist x (z : H) := Metric.infDist_le_dist_of_mem hzC
        have hlt : dist x (z : H) < r := by
          have : dist (z : H) x < r := by
            simpa [r, Metric.mem_ball, Subtype.dist_eq] using hz
          simpa [dist_comm] using this
        have hcontra : Metric.infDist x C < Metric.infDist x C := by
          calc
            Metric.infDist x C ≤ dist x (z : H) := hle
            _ < r := hlt
            _ < Metric.infDist x C := by
              dsimp [r]
              linarith
        exact lt_irrefl _ hcontra
      simp [G, R, hz_out, proj]
    exact hR_cont.congr_of_eventuallyEq hGR
  have hdiff :
      DifferentiableAt ℝ (fun y ↦ Metric.infDist y C) x := by
    simpa [f, Function.toEReal_apply] using
      differentiableAt_of_exists_selectionContinuousAt hf hx_int_eff ⟨G, hG⟩
  have hgrad :
      HasGradientAt
        (fun y : H ↦ Metric.infDist y C)
        (∇ (fun y : H ↦ Metric.infDist y C) x) x := by
    simpa using hdiff.hasGradientAt
  have hsub_grad :
      (∂ f) x = ({∇ (fun y : H ↦ Metric.infDist y C) x} : Set H) := by
    simpa [f] using subdifferential_eq_singleton_of_hasGradientAt hf hx_int_eff hgrad
  have hgrad_eq :
      ∇ (fun y : H ↦ Metric.infDist y C) x = (Metric.infDist x C)⁻¹ • (x - proj x) := by
    apply Set.singleton_injective
    rw [← hsub, hsub_grad]
  simpa [proj, hgrad_eq] using hgrad

end

end

end Set
