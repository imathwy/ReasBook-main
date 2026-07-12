import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Theorem_5_4_7_3
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_8_11
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_8_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PowerCone

/- Theorem 5.4.8.5 lies in the Chapter 5 self-concordant-barrier / power-cone-slice domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_constrainedEpigraph_abs_pow_iff` from
  `Definition_5_4_8_11`, the source-facing owner/view for the epigraph `Q₄`;
* `separableLogBarrierF4` and `separableLogBarrierF4_apply` from `Definition_5_4_8_12`, the
  source-facing owner/view for the barrier `F₄`;
* `powerCone` from `Definition_5_4_7_1`, the earlier chapter owner for the symmetric power
  cone;
* `power_cone_barrier` and `power_cone_barrier_is_four_self_concordant_barrier` from
  `Theorem_5_4_7_3`, the upstream Chapter 5 owner reused by the affine slice here.
* `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay`,
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`, and
  `IsSelfConcordantBarrierOnWith.add`, the chapter owner tools for the explicit endpoint
  `p = 1`, where the epigraph of `|x|` is cut out by affine slack maps.

Best owner abstraction:
* source-facing: the textbook epigraph/barrier pair `Q₄`, `F₄`;
* core/canonical: `constrainedEpigraph`, `IsSelfConcordantBarrierOnWith`, and the earlier
  power-cone barrier owner `power_cone_barrier`;
* bridge/view: the slice-identification theorems below relating the canonical specialized
  epigraph/barrier surface to that upstream power-cone owner for `p > 1`, together with the
  endpoint `p = 1` reduction to affine `-log` slack barriers.

Primitive data:
* the canonical epigraph owner specialized to `x ↦ |x| ^ p`;
* the canonical source-facing barrier owner `separableLogBarrierF4 p`.

Derived API:
* the interior-membership theorem for `Q₄`;
* the slice-identification bridge theorems;
* the endpoint `p = 1` barrier theorem obtained from affine `-log` slacks;
* the resulting `4`-self-concordant barrier theorem for `F₄` on `interior Q₄`, stated on the
  canonical `L²` product owner `Z = WithLp 2 (ℝ × ℝ)` through `z ↦ z.ofLp`.

This file therefore keeps the source-facing theorem, but removes the impression of a second
independent barrier construction by connecting `Q₄` and `F₄` directly to the earlier
power-cone owner while exposing the same canonical `WithLp 2` ambient owner used by the nearby
barrier files instead of relying on hidden raw-product inner-product data. -/

variable {p : ℝ}

local notation "Z" => WithLp 2 (ℝ × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → ℝ × ℝ)
local notation "Q₄[" p "]" =>
  constrainedEpigraph (Set.univ : Set ℝ)
    (fun y : ℝ ↦ ((|y| ^ p : ℝ) : WithTop ℝ))

local notation "F₄" => separableLogBarrierF4 p

-- Proof sketch: rewrite `powerCone (1 / p)` at the affine slice `((t, 1), x)` and use
-- `Real.le_rpow_inv_iff_of_pos` / `Real.rpow_le_rpow_iff` to convert
-- `|x| ≤ t^(1 / p)` into the epigraph inequality `t ≥ |x|^p`.
/-- On the affine slice `((t, 1), x)`, the symmetric power cone `K_{1 / p}` is exactly the
canonical epigraph `Q₄` of `x ↦ |x|^p`. -/
theorem mem_powerCone_one_div_p_unitSlice_iff {x t : ℝ} (hp0 : 0 < p) :
    ((t, 1), x) ∈ K_[(1 / p)] ↔ (x, t) ∈ Q₄[p] := by
  rw [mem_powerCone_iff, mem_constrainedEpigraph_abs_pow_iff]
  constructor
  · rintro ⟨ht, -, hx⟩
    have hx' : |x| ≤ Real.rpow t (1 / p) := by
      simpa [powerConeGeometricMean_apply] using hx
    have hpow : |x| ^ p ≤ (Real.rpow t (1 / p)) ^ p := by
      exact (Real.rpow_le_rpow_iff (abs_nonneg x) (Real.rpow_nonneg ht _) hp0).2 hx'
    have ht' : (Real.rpow t (1 / p)) ^ p = t := by
      simpa [one_div] using (Real.rpow_inv_rpow ht hp0.ne' : (t ^ p⁻¹) ^ p = t)
    rw [ht'] at hpow
    simpa [ge_iff_le] using hpow
  · intro hxt
    have hxt' : |x| ^ p ≤ t := by
      simpa [ge_iff_le] using hxt
    have hxt_nonneg : 0 ≤ |x| ^ p := Real.rpow_nonneg (abs_nonneg x) _
    have ht : 0 ≤ t := le_trans hxt_nonneg hxt'
    have hx : |x| ≤ Real.rpow t (1 / p) := by
      simpa [one_div] using (Real.le_rpow_inv_iff_of_pos (abs_nonneg x) ht hp0).2 hxt'
    refine ⟨ht, by norm_num, ?_⟩
    simpa [powerConeGeometricMean_apply] using hx

-- Proof sketch: for `t ≥ 0`, evaluate both sides using `separableLogBarrierF4_apply` and
-- `power_cone_barrier_apply`, then simplify the fixed slice coordinate `1`.
/-- On the affine slice `((t, 1), x)`, the source-facing barrier `F₄` is exactly the Chapter 5
power-cone barrier with parameter `α = 1 / p`. -/
theorem separableLogBarrierF4_eq_power_cone_barrier_unitSlice
    (p x t : ℝ) (ht : 0 ≤ t) :
    separableLogBarrierF4 p (x, t) = power_cone_barrier (1 / p) ((t, 1), x) := by
  rw [separableLogBarrierF4_apply, power_cone_barrier_apply (1 / p) t 1 x ht (by norm_num)]
  simp [div_eq_mul_inv, sub_eq_add_neg, add_comm, mul_comm]

-- Proof sketch: for `p > 0`, the function `x ↦ |x| ^ p` is continuous, so the interior of its
-- closed epigraph is obtained by replacing `t ≥ |x| ^ p` with the strict inequality
-- `t > |x| ^ p`.
/-- A pair `(x, t)` lies in the canonical epigraph interior for Definition 5.4.8.11 exactly when
`t > |x| ^ p`. -/
theorem mem_interior_constrainedEpigraph_abs_pow_iff {x t : ℝ} (hp0 : 0 < p) :
    (x, t) ∈ interior Q₄[p] ↔ t > |x| ^ p := sorry

-- Proof sketch: at the endpoint `p = 1`, the domain `t > |x|` is exactly the intersection of the
-- three affine slack regions `t > 0`, `t - x > 0`, and `t + x > 0`. Pull back the scalar owner
-- `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` along those affine maps, sum the three
-- resulting barriers using `IsSelfConcordantBarrierOnWith.add`, and compare with the source-facing
-- formula `F₄(x, t) = -log t - log (t^2 - x^2)` on the same open domain.
/-- Endpoint case `p = 1`: the barrier
`F₄(x, t) = -\log t - \log (t^2 - x^2)` is a `3`-self-concordant barrier for the epigraph of
`|x|`, viewed on the canonical `L²` product owner `Z = WithLp 2 (ℝ × ℝ)` through
`z ↦ z.ofLp`. -/
theorem separableLogBarrierF4_one_is_three_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior Q₄[(1 : ℝ)])
      (3 : NNReal)
      (separableLogBarrierF4 1 ∘ ofZ) := sorry

-- Proof sketch: split into the endpoint `p = 1` and the genuine power-cone range `p > 1`. In
-- the endpoint case, use `separableLogBarrierF4_one_is_three_selfConcordantBarrier` and enlarge
-- the barrier parameter from `3` to `4`. For `p > 1`, identify the interior of the canonical
-- closed epigraph from Definition 5.4.8.11 with the affine slice of `interior (powerCone
-- (1 / p))`, rewrite the barrier through `separableLogBarrierF4_eq_power_cone_barrier_unitSlice`,
-- and apply `power_cone_barrier_is_four_self_concordant_barrier`.
/-- Theorem 5.4.8.5: for `p ≥ 1`, the function
`F₄(x, t) = -\log t - \log (t^(2 / p) - x^2)` is a `4`-self-concordant barrier for the canonical
epigraph of `x ↦ |x|^p`, viewed on the canonical `L²` product owner `Z = WithLp 2 (ℝ × ℝ)`
through `z ↦ z.ofLp`. -/
theorem separableLogBarrierF4_is_four_selfConcordantBarrier
    (hp : 1 ≤ p) :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior Q₄[p])
      (4 : NNReal)
      (F₄ ∘ ofZ) := by
  rcases lt_or_eq_of_le hp with hp1 | rfl
  · have hp0 : 0 < p := lt_trans zero_lt_one hp1
    sorry
  · let h3 := separableLogBarrierF4_one_is_three_selfConcordantBarrier
    refine
      { toIsStandardSelfConcordantOn := h3.toIsStandardSelfConcordantOn
        barrier_parameter_bound := ?_ }
    intro x hx u
    exact le_trans (h3.barrier_parameter_bound hx u) (by norm_num)
