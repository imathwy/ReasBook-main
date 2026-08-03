import Mathlib
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap06.Proposition_6_47
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap16.Example_16_32
import BauschkeLean.Chap16.Proposition_16_61

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Set H}

/-- Helper for Example 16 62: membership in the subdifferential of the distance-to-set function is
equivalent to the corresponding real-valued affine minorant inequality. -/
lemma distanceToSet_mem_subdifferential_iff_real {x u : H} :
    u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x ↔
      ∀ y : H, inner ℝ (y - x) u + Metric.infDist x C ≤ Metric.infDist y C := by
  rw [ERealFunction.mem_subdifferential_iff]
  constructor
  · intro hu y
    -- All values of `Metric.infDist` are finite, so the `EReal` inequality descends to `ℝ`.
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_add] using hu y)
  · intro hu y
    -- Conversely, package the real inequality back into the `EReal` owner surface.
    exact (EReal.coe_le_coe_iff).2 (by simpa [EReal.coe_add] using hu y)

/-- Helper for Example 16 62: at a point of `C`, the base value of the distance function is `0`,
so the subgradient inequality drops its constant term. -/
lemma distanceToSet_mem_subdifferential_iff_zero_value {x u : H} (hx : x ∈ C) :
    u ∈ (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x ↔
      ∀ y : H, inner ℝ (y - x) u ≤ Metric.infDist y C := by
  -- Rewrite subgradient membership through the real-valued form and use `d_C(x) = 0`.
  rw [distanceToSet_mem_subdifferential_iff_real]
  simp [Metric.infDist_zero_of_mem hx]

/-- Helper for Example 16 62: on the interior of `C`, the distance-to-set function is locally
constant with value `0`, so its subdifferential is the singleton `{0}`. -/
lemma subdifferential_distanceToSet_eq_singleton_zero_on_interior
    {x : H} (hx : x ∈ interior C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x = ({0} : Set H) := by
  have hxC : x ∈ C := interior_subset hx
  ext u
  constructor
  · intro hu
    rw [Set.mem_singleton_iff]
    by_cases hu0 : u = 0
    · exact hu0
    have hu_affine :=
      (distanceToSet_mem_subdifferential_iff_zero_value (C := C) (x := x) (u := u) hxC).1 hu
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨ε, hε_pos, hball⟩
    let t : ℝ := ε / (2 * ‖u‖)
    have ht_pos : 0 < t := by
      -- Choose a positive step small enough to stay inside the interior ball.
      dsimp [t]
      exact div_pos hε_pos (by positivity)
    have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have ht_mul_norm : t * ‖u‖ = ε / 2 := by
      -- The chosen step has size exactly `ε / 2` after multiplying by `‖u‖`.
      calc
        t * ‖u‖ = ε / (2 * ‖u‖) * ‖u‖ := by rfl
        _ = ε / 2 := by
          field_simp [hu_norm_ne]
    have hplus_dist : dist (x + t • u) x < ε := by
      -- The forward perturbation remains inside the interior ball around `x`.
      rw [dist_eq_norm]
      have hplus_shift : x + t • u - x = t • u := by abel
      rw [hplus_shift, norm_smul, Real.norm_of_nonneg ht_pos.le, ht_mul_norm]
      linarith
    have hplus_mem : x + t • u ∈ C := by
      exact hball (by simpa [Metric.mem_ball] using hplus_dist)
    have hminus_dist : dist (x - t • u) x < ε := by
      -- The backward perturbation also stays inside the same interior ball.
      rw [dist_eq_norm]
      have hminus_shift : x - t • u - x = -(t • u) := by abel
      rw [hminus_shift, norm_neg, norm_smul, Real.norm_of_nonneg ht_pos.le, ht_mul_norm]
      linarith
    have hminus_mem : x - t • u ∈ C := by
      exact hball (by simpa [Metric.mem_ball] using hminus_dist)
    have hplus_nonpos : t * ‖u‖ ^ 2 ≤ 0 := by
      -- Evaluating the subgradient inequality at `x + t • u` gives the forward sign.
      have htest := hu_affine (x + t • u)
      have hplus_shift : (x + t • u) - x = t • u := by abel
      rw [Metric.infDist_zero_of_mem hplus_mem] at htest
      rw [hplus_shift, real_inner_smul_left, real_inner_self_eq_norm_sq] at htest
      simpa using htest
    have hminus_nonpos : -(t * ‖u‖ ^ 2) ≤ 0 := by
      -- Evaluating at `x - t • u` gives the opposite sign, forcing the norm square to vanish.
      have htest := hu_affine (x - t • u)
      have hminus_shift : (x - t • u) - x = -(t • u) := by abel
      rw [Metric.infDist_zero_of_mem hminus_mem] at htest
      rw [hminus_shift, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at htest
      simpa using htest
    have hsq_zero : ‖u‖ ^ 2 = 0 := by
      nlinarith [hplus_nonpos, hminus_nonpos, ht_pos]
    have hnorm_zero : ‖u‖ = 0 := sq_eq_zero_iff.mp hsq_zero
    exact norm_eq_zero.mp hnorm_zero
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    -- The zero vector satisfies the affine minorant inequality because `Metric.infDist ≥ 0`.
    rw [distanceToSet_mem_subdifferential_iff_zero_value (C := C) (x := x) (u := (0 : H)) hxC]
    intro y
    simpa using Metric.infDist_nonneg (x := y) (s := C)

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- Classical decidability of membership in `C`, used to state the piecewise distance
subdifferential formula. -/
local instance instDecidablePredDistanceToSetSet :
    DecidablePred (fun x : H ↦ x ∈ C) := Classical.decPred _

/-- Classical decidability of membership in `frontier C`, used to state the boundary branch of the
distance subdifferential formula. -/
local instance instDecidablePredDistanceToSetFrontier :
    DecidablePred (fun x : H ↦ x ∈ frontier C) := Classical.decPred _

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P" => P[C, hC_cheb]

/-- Helper for Example 16 62: a point of `C` projects to itself. -/
lemma projectionPoint_eq_self_of_mem
    {x : H} (hx : x ∈ C) :
    P x = x := by
  -- The point `x` is itself a best approximation once `x ∈ C`.
  have hx_proj : x = P x := by
    refine eq_projectionPoint_of_isBestApproximation C hC_cheb ?_
    exact ⟨hx, by simp [Metric.infDist_zero_of_mem hx]⟩
  exact hx_proj.symm

/-- Helper for Example 16 62: the norm of the projection residual equals the distance to `C`. -/
lemma projection_residual_norm_eq_infDist
    (x : H) :
    ‖x - P x‖ = Metric.infDist x C := by
  -- The chosen projection point realizes the distance to `C`.
  simpa [dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb x).2

/-- Helper for Example 16 62: outside `C`, the residual from `x` to its metric projection on `C`
is nonzero. -/
lemma projection_residual_ne_zero_of_not_mem
    {x : H} (hx : x ∉ C) :
    x - P x ≠ 0 := by
  intro hzero
  have hpC : P x ∈ C := projectionPoint_mem C hC_cheb x
  have hx_eq : x = P x := sub_eq_zero.mp hzero
  exact hx (hx_eq ▸ hpC)

/-- Helper for Example 16 62: the raw projection residual belongs to the normal cone at the
projection point. -/
lemma projection_residual_mem_normalCone
    (x : H) :
    x - P x ∈ N[C] (P x) := by
  -- Proposition 6.47 identifies the projection equation with normal-cone membership.
  exact
    (eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex
      (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
      (hC_convex := hC_convex) (x := x) (p := P x)).mp rfl

/-- Helper for Example 16 62: outside `C`, the normalized projection residual lies in the normal
cone at the projection point. -/
lemma normalized_projection_residual_mem_normalCone_of_not_mem
    {x : H} (_hx : x ∉ C) :
    ((Metric.infDist x C)⁻¹ • (x - P x)) ∈ N[C] (P x) := by
  have hPx : P x ∈ C := projectionPoint_mem C hC_cheb x
  have hres :
      x - P x ∈ N[C] (P x) :=
    projection_residual_mem_normalCone (C := C) hC_nonempty hC_closed hC_convex x
  -- Rewrite the normal cone to the pointwise support inequality before scaling.
  rw [Set.normalCone_of_mem hPx] at hres ⊢
  have hres_pointwise : ∀ y ∈ C, ⟪y - P x, x - P x⟫_ℝ ≤ 0 :=
    (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := x - P x) (p := P x)).1 hres
  -- Scaling by the nonnegative factor `(Metric.infDist x C)⁻¹` preserves the inequalities.
  exact
    (innerSupremumOn_sub_singleton_le_zero_iff
      (C := C) (u := (Metric.infDist x C)⁻¹ • (x - P x)) (p := P x)).2 <| by
        intro y hy
        simpa [real_inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using
          mul_nonpos_of_nonneg_of_nonpos
            (inv_nonneg.mpr (Metric.infDist_nonneg (x := x) (s := C))) (hres_pointwise y hy)

section

omit [CompleteSpace H]

/-- Helper for Example 16 62: the norm function packaged as an `]-∞,+∞]`-valued function belongs
to `Γ₀(H)`. -/
lemma norm_toEReal_mem_gammaZero :
    (norm.toEReal : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
  -- Package the norm as a proper lower-semicontinuous convex function.
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha hb
    have hnorm :
        ‖a • x + (1 - a) • y‖ ≤ a * ‖x‖ + (1 - a) * ‖y‖ := by
      simpa [smul_eq_mul] using
        (convexOn_univ_norm.2 (by simp) (by simp) ha (sub_nonneg.mpr hb) (by ring) :
          ‖a • x + (1 - a) • y‖ ≤ a • ‖x‖ + (1 - a) • ‖y‖)
    change ((‖a • x + (1 - a) • y‖ : ℝ) : EReal) ≤
      ((a * ‖x‖ + (1 - a) * ‖y‖ : ℝ) : EReal)
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    exact_mod_cast hnorm
  · simpa using (continuous_coe_real_ereal.comp continuous_norm).lowerSemicontinuous

/-- Helper for Example 16 62: the indicator of a nonempty closed convex set belongs to `Γ₀(H)`. -/
lemma indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

end

section

omit [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 16 62: for a nonempty set, the coercion of `Metric.infDist` to `EReal`
agrees with the infimum of translated norms over `C`. -/
lemma distanceToSet_toEReal_eq_sInf_norm_image_of_nonempty
    (hC_nonempty : C.Nonempty) (x : H) :
    ((Metric.infDist x C : ℝ) : EReal) =
      sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
  let S : Set EReal := (fun y : H ↦ (dist x y : EReal)) '' C
  have hS_nonempty : S.Nonempty := by
    rcases hC_nonempty with ⟨y, hy⟩
    exact ⟨(dist x y : EReal), ⟨y, hy, rfl⟩⟩
  have hglb : IsGLB S ((Metric.infDist x C : ℝ) : EReal) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (EReal.coe_le_coe_iff).2 <|
        (Metric.isGLB_infDist (x := x) hC_nonempty).1 ⟨y, hy, rfl⟩
    · intro b hb
      revert hb
      refine EReal.rec ?_ ?_ ?_ b
      · intro _
        exact bot_le
      · intro r hbr
        have hreal_lb : r ∈ lowerBounds ((fun y : H ↦ dist x y) '' C) := by
          intro s hs
          rcases hs with ⟨y, hy, rfl⟩
          exact (EReal.coe_le_coe_iff).1 (by simpa using hbr ⟨y, hy, rfl⟩)
        exact_mod_cast (Metric.isGLB_infDist (x := x) hC_nonempty).2 hreal_lb
      · intro htop
        exfalso
        rcases hC_nonempty with ⟨y, hy⟩
        have : (⊤ : EReal) ≤ (dist x y : EReal) := by
          simpa using htop ⟨y, hy, rfl⟩
        simp at this
  calc
    ((Metric.infDist x C : ℝ) : EReal) = sInf S := by
      rw [(hglb.csInf_eq hS_nonempty).symm]
    _ = sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
      simp [S, dist_eq_norm]

/-- Helper for Example 16 62: evaluating the indicator-plus-norm infimal convolution at `x`
reduces to the same infimum of translated norms over `C`. -/
lemma indicator_infimalConvolution_norm_apply (x : H) :
    (ι[C] □ norm.toEReal) x =
      sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
  rw [infimalConvolution_apply]
  calc
    (⨅ y : H, (ι[C] y : EReal) + (norm.toEReal (x - y) : EReal))
      = ⨅ y : C, (‖x - (y : H)‖ : EReal) := by
          apply le_antisymm
          · refine le_iInf ?_
            intro y
            have hle :
                (⨅ z : H, (ι[C] z : EReal) + (norm.toEReal (x - z) : EReal)) ≤
                  (ι[C] (y : H) : EReal) + (norm.toEReal (x - (y : H)) : EReal) :=
              iInf_le _ (y : H)
            simpa [indicator_apply, Function.toEReal_apply, y.property] using hle
          · refine le_iInf ?_
            intro y
            by_cases hy : y ∈ C
            · have hle :
                  (⨅ z : C, (‖x - (z : H)‖ : EReal)) ≤
                    (‖x - ((⟨y, hy⟩ : C) : H)‖ : EReal) :=
                iInf_le (fun z : C ↦ (‖x - (z : H)‖ : EReal)) ⟨y, hy⟩
              simpa [indicator_apply, Function.toEReal_apply, hy] using hle
            · have hle : (⨅ z : C, (‖x - (z : H)‖ : EReal)) ≤ ⊤ := le_top
              have hle' :
                  (⨅ z : C, (‖x - (z : H)‖ : EReal)) ≤
                    (ι[C] y : EReal) + (norm.toEReal (x - y) : EReal) := by
                convert hle using 1
                simp [indicator_apply, hy]
              exact hle'
    _ = sInf ((fun y : H ↦ (‖x - y‖ : EReal)) '' C) := by
      symm
      rw [Set.image_eq_range, sInf_range]

end

section

omit [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 16 62: for a nonempty set, the real-valued distance function agrees with
the infimal convolution representation `ι[C] □ ‖·‖` after coercion to `EReal`. -/
lemma distanceToSet_toEReal_eq_indicator_infimalConvolution_norm_of_nonempty
    (hC_nonempty : C.Nonempty) :
    (fun y : H ↦ Metric.infDist y C).toEReal = ι[C] □ norm.toEReal := by
  funext y
  change ((Metric.infDist y C : ℝ) : EReal) = _
  calc
    ((Metric.infDist y C : ℝ) : EReal) =
        sInf ((fun z : H ↦ (‖y - z‖ : EReal)) '' C) := by
      simpa using distanceToSet_toEReal_eq_sInf_norm_image_of_nonempty
        (C := C) hC_nonempty y
    _ = (ι[C] □ norm.toEReal) y := by
      symm
      exact indicator_infimalConvolution_norm_apply (C := C) y

end

/-- Helper for Example 16 62: the metric projection point realizes the infimal-convolution value
for the distance function. -/
lemma distanceToSet_infimalConvolution_eq_projection_value
    (x : H) :
    (ι[C] □ norm.toEReal) x =
      (ι[C] (P x) : EReal) + (norm.toEReal (x - P x) : EReal) := by
  have hdist :=
    congrFun
      (distanceToSet_toEReal_eq_indicator_infimalConvolution_norm_of_nonempty
        (C := C) hC_nonempty) x
  have hPx : P x ∈ C := projectionPoint_mem C hC_cheb x
  -- Rewrite the distance representation at `x` and identify the residual norm with the distance.
  calc
    (ι[C] □ norm.toEReal) x = ((Metric.infDist x C : ℝ) : EReal) := by
      simpa [Function.toEReal_apply] using hdist.symm
    _ = ((‖x - P x‖ : ℝ) : EReal) := by
      rw [projection_residual_norm_eq_infDist (C := C) hC_nonempty hC_closed hC_convex x]
    _ = (ι[C] (P x) : EReal) + (norm.toEReal (x - P x) : EReal) := by
      simp [indicator_apply, Function.toEReal_apply, hPx]

section

include hC_nonempty hC_closed hC_convex

/-- Helper for Example 16 62: at a point of `C`, the distance-to-set subdifferential is the
intersection of the normal cone with the closed unit ball. -/
lemma subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem
    {x : H} (hx : x ∈ C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      N[C] x ∩ Metric.closedBall (0 : H) 1 := by
  have hindicator :
      ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
      (C := C) hC_nonempty hC_closed hC_convex
  have hPx : P x = x :=
    projectionPoint_eq_self_of_mem (C := C) hC_nonempty hC_closed hC_convex hx
  have hvalue :
      (ι[C] □ norm.toEReal) x = (ι[C] x : EReal) + (norm.toEReal (x - x) : EReal) := by
    -- Route correction: rewrite `P x = x` before invoking Proposition 16.61, so the minimizer is
    -- the source point `y := x` and no projection transport remains in the fibers.
    simpa [hPx] using
      distanceToSet_infimalConvolution_eq_projection_value
        (C := C) hC_nonempty hC_closed hC_convex x
  have hindicator_sub :
      (∂ ι[C]) x = N[C] x := by
    simpa using
      congrFun (subdifferential_setIndicator_eq_normalCone (C := C) hC_nonempty) x
  have hnorm_sub :
      (∂ norm.toEReal) (x - x) = Metric.closedBall (0 : H) 1 := by
    simpa using subdifferential_norm_eq_singleton_or_closedBall (H := H) (x - x)
  -- Apply Proposition 16.61 to `d_C = ι[C] □ ‖·‖` at the exact in-set minimizing point `x`.
  calc
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x = (∂ (ι[C] □ norm.toEReal)) x := by
      simpa using congrArg (fun f : H → EReal ↦ (∂ f) x)
        (distanceToSet_toEReal_eq_indicator_infimalConvolution_norm_of_nonempty
          (C := C) hC_nonempty)
    _ = (∂ ι[C]) x ∩ (∂ norm.toEReal) (x - x) := by
      simpa using
        subdifferential_infimalConvolution_eq_inter_of_value_eq
          (f := ι[C]) (g := norm.toEReal) (x := x) (y := x)
          hindicator norm_toEReal_mem_gammaZero hvalue
    _ = N[C] x ∩ Metric.closedBall (0 : H) 1 := by
      rw [hindicator_sub, hnorm_sub]

end

/-- Helper for Example 16 62: outside `C`, the distance-to-set subdifferential is the singleton
containing the normalized projection residual. -/
lemma subdifferential_distanceToSet_eq_singleton_normalizedProjectionResidual_of_not_mem
    {x : H} (hx : x ∉ C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
  have hindicator :
      ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
      (C := C) hC_nonempty hC_closed hC_convex
  have hres_ne :
      x - P x ≠ 0 :=
    projection_residual_ne_zero_of_not_mem (C := C) hC_nonempty hC_closed hC_convex hx
  have hindicator_sub :
      (∂ ι[C]) (P x) = N[C] (P x) := by
    simpa using
      congrFun (subdifferential_setIndicator_eq_normalCone (C := C) hC_nonempty) (P x)
  have hnorm_sub :
      (∂ norm.toEReal) (x - P x) = ({‖x - P x‖⁻¹ • (x - P x)} : Set H) := by
    simpa [hres_ne] using subdifferential_norm_eq_singleton_or_closedBall (H := H) (x - P x)
  have hsingleton :
      ({‖x - P x‖⁻¹ • (x - P x)} : Set H) =
        ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
    rw [projection_residual_norm_eq_infDist (C := C) hC_nonempty hC_closed hC_convex x]
  -- Apply Proposition 16.61 at the exterior minimizing point `P x`, then collapse the singleton
  -- intersection using normalized normal-cone membership.
  calc
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x = (∂ (ι[C] □ norm.toEReal)) x := by
      simpa using congrArg (fun f : H → EReal ↦ (∂ f) x)
        (distanceToSet_toEReal_eq_indicator_infimalConvolution_norm_of_nonempty
          (C := C) hC_nonempty)
    _ = (∂ ι[C]) (P x) ∩ (∂ norm.toEReal) (x - P x) := by
      simpa using
        subdifferential_infimalConvolution_eq_inter_of_value_eq
          (f := ι[C]) (g := norm.toEReal) (x := x) (y := P x)
          hindicator norm_toEReal_mem_gammaZero
          (distanceToSet_infimalConvolution_eq_projection_value
            (C := C) hC_nonempty hC_closed hC_convex x)
    _ = N[C] (P x) ∩ ({‖x - P x‖⁻¹ • (x - P x)} : Set H) := by
      rw [hindicator_sub, hnorm_sub]
    _ = N[C] (P x) ∩ ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
      rw [hsingleton]
    _ = ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
      ext u
      constructor
      · intro hu
        exact hu.2
      · intro hu
        rcases Set.mem_singleton_iff.mp hu with rfl
        exact ⟨normalized_projection_residual_mem_normalCone_of_not_mem
          (C := C) hC_nonempty hC_closed hC_convex hx, Set.mem_singleton _⟩

/- Source/core/bridge triage:
- `source-facing`: Example 16.62 is the piecewise subdifferential formula for the
  distance-to-set function.
- `core/canonical`: the owner declarations are `Metric.infDist`, `P[C, hC]`, `N[C]`, and `∂`.
- `bridge/view`: the boundary and exterior branch lemmas are derived views of this piecewise owner.

The refinement therefore keeps the piecewise formula as the main source-facing statement and
derives the reusable branch lemmas from it instead of maintaining parallel standalone copies. -/

-- Proof sketch: write `d_C = ι_C □ ‖·‖` using the projection formula for the distance to a closed
-- convex set, then apply the exact subdifferential formula for infimal convolution at the
-- projection point. The in-set branch becomes `N[C] x ∩ Metric.closedBall (0 : H) 1`, and the
-- interior subcase collapses to `{0}` by the already-proved local-constancy argument.
/-- Example 16 62: for a nonempty closed convex subset `C` of a real Hilbert space, the
subdifferential of the distance-to-set function is the singleton containing the normalized
projection residual outside `C`, the intersection `N[C] x ∩ Metric.closedBall (0 : H) 1` on the
boundary, and `{0}` off the boundary inside `C` (equivalently, on `interior C`). -/
theorem subdifferential_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
    (x : H) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      if x ∈ C then
        if x ∈ frontier C then
          N[C] x ∩ Metric.closedBall (0 : H) 1
        else
          ({0} : Set H)
      else
        ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
  by_cases hxC : x ∈ C
  · by_cases hxbdry : x ∈ frontier C
    · -- On the frontier, the in-set branch is the normal cone intersected with the unit ball.
      simpa [hxC, hxbdry] using
        subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem
          (C := C) hC_nonempty hC_closed hC_convex hxC
    · have hx_int : x ∈ interior C := by
        -- Inside `C`, not being on the frontier is equivalent to belonging to the interior.
        rw [mem_frontier_iff_notMem_interior hxC] at hxbdry
        exact not_not.mp hxbdry
      -- Away from the frontier but still in `C`, the interior branch collapses to `{0}`.
      simpa [hxC, hxbdry] using
        subdifferential_distanceToSet_eq_singleton_zero_on_interior
          (C := C) hx_int
  · -- Outside `C`, the exterior singleton branch is already available.
    simpa [hxC] using
      subdifferential_distanceToSet_eq_singleton_normalizedProjectionResidual_of_not_mem
        (C := C) hC_nonempty hC_closed hC_convex hxC

/-- Exterior branch of Example 16.62: away from `C`, the distance-to-set subdifferential is the
singleton containing the normalized projection residual. -/
theorem subdifferential_distanceToSet_eq_singleton_normalizedResidual_of_not_mem
    {x : H} (hx : x ∉ C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
  simpa [hx] using
    subdifferential_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex x

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}

/-- Boundary branch of Example 16.62: at a frontier point of a nonempty closed convex set, the
subdifferential of the distance-to-set function is `N[C] x ∩ Metric.closedBall (0 : H) 1`. -/
theorem subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : H} (hx : x ∈ frontier C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x =
      N[C] x ∩ Metric.closedBall (0 : H) 1 := by
  have hxC : x ∈ C := hC_closed.frontier_subset hx
  have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
  simpa [hxC, hx] using
    subdifferential_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex x

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Set H}

/-- Interior branch of Example 16.62: on `interior C`, the distance-to-set subdifferential is the
singleton `{0}`. -/
theorem subdifferential_distanceToSet_eq_singleton_zero_of_mem_interior
    {x : H} (hx : x ∈ interior C) :
    (∂ (fun y : H ↦ Metric.infDist y C).toEReal) x = ({0} : Set H) := by
  -- Reuse the file-local interior lemma rather than duplicating the local-constancy proof.
  simpa using subdifferential_distanceToSet_eq_singleton_zero_on_interior
    (C := C) hx

end

end SubdifferentialCalculus

end

end ERealFunction
