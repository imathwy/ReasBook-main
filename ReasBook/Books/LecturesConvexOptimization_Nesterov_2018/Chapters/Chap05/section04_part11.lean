import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_4_8_5 (from Chap05) -/
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

/-! ### Theorem_5_4_8_6 (from Chap05) -/
noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerConePlus

variable (p : ℝ)

/- Theorem 5.4.8.6 lies in the Chapter 5 self-concordant-barrier / power-cone-slice domain.

Sampled owner declarations:
* `Q₅` and `mem_Q₅_iff` from `Definition_5_4_8_13`, the source-facing owner/view for `Q₅`;
* `separableLogBarrierF5` and `separableLogBarrierF5_apply` from `Definition_5_4_8_14`, the
  source-facing owner/view for `F₅`;
* `power_cone_plus`, `power_cone_plus_barrier`, and
  `power_cone_plus_barrier_is_three_self_concordant_barrier` from `Theorem_5_4_7_4`, the
  upstream owner theorem on the one-sided power cone;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  affine-pullback theorem for barrier owners.

Best owner abstraction:
* source-facing: the textbook set `Q₅` and barrier `F₅`;
* core/canonical: `K_[p]⁺`, `power_cone_plus_barrier p`, and
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: the affine slice `((t, 1), x)` identifying `Q₅` and `F₅` with those upstream
  power-cone owners.

Primitive data:
* the source-facing owner `Q₅ p`;
* the canonical slice owner `F₅ = power_cone_plus_barrier p ∘ ((t, 1), x)`.

Derived API:
* the interior-membership theorem for `Q₅`;
* the interior slice-domain bridge to `K_[p]⁺`;
* the resulting source-facing barrier theorem.

Source/core/bridge triage:
* source-facing: Theorem 5.4.8.6 itself;
* core/canonical: the one-sided power-cone barrier theorem from `Theorem_5_4_7_4`;
* bridge/view: the interior unit-slice theorem below.

The previous proof sketch used the wrong slice `((1, t), x)`, which corresponds to
`x ≤ t^(1 - p)` rather than `x ≤ t^p`. The correct source-faithful bridge is the affine slice
`((t, 1), x)`. -/

local notation "Q₅" => Q₅ p

local notation "F₅" => separableLogBarrierF5 p

-- Proof sketch: use that for `p > 0` the map `t ↦ t^p` is continuous on `(0, ∞)`, so the
-- interior of the canonical closed constrained sublevel set `Q₅` is obtained by replacing the
-- boundary conditions `t ≥ 0` and `x ≤ t^p` with the strict inequalities `t > 0` and `x < t^p`.
/-- A pair `(x, t)` lies in the interior of the canonical constrained sublevel set for
Definition 5.4.8.13 exactly when `t > 0` and `x < t^p`. -/
theorem mem_interior_constrainedSublevelSet_sub_rpow_iff
    {x t : ℝ} (hp0 : 0 < p) :
    (x, t) ∈ interior Q₅ ↔ 0 < t ∧ x < Real.rpow t p := sorry

-- Proof sketch: the slice point `((t, 1), x)` belongs to `interior (K_[p]⁺)` exactly when the
-- first coordinate stays positive and the power-cone slack
-- `x₁^p x₂^(1 - p) - z` stays positive. On the unit slice `x₂ = 1`, that strict slack is
-- `t^p - x`, which is the same strict condition that describes `interior Q₅`.
/-- On the affine slice `((t, 1), x)`, membership in `interior (K_[p]⁺)` is exactly membership
in `interior Q₅`. -/
theorem mem_interior_power_cone_plus_unitSlice_iff {x t : ℝ} (hp0 : 0 < p) :
    ((t, 1), x) ∈ interior (K_[p]⁺) ↔ (x, t) ∈ interior Q₅ := by
  rw [mem_interior_constrainedSublevelSet_sub_rpow_iff p hp0]
  constructor
  · intro h
    have hK : ((t, 1), x) ∈ K_[p]⁺ := interior_subset h
    rw [mem_power_cone_plus_iff, powerConeGeometricMean_apply] at hK
    rcases hK with ⟨ht, -, hx_raw⟩
    have hx : x ≤ Real.rpow t p := by
      simpa using hx_raw
    have ht_strict : 0 < t := by
      by_contra ht_nonpos
      have ht_zero : t = 0 := le_antisymm (le_of_not_gt ht_nonpos) ht
      let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((s, 1), x)
      have hγ : Continuous γ := by
        fun_prop
      have hpre :
          γ ⁻¹' interior (K_[p]⁺) ∈ nhds t := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hneg : -ε / 2 ∈ Metric.ball t ε := by
        have hhalf_neg : -ε / 2 < 0 := by
          linarith
        have habs : |(-ε / 2 : ℝ) - 0| = ε / 2 := by
          rw [sub_zero, abs_of_neg hhalf_neg]
          ring
        rw [ht_zero, Metric.mem_ball, Real.dist_eq, habs]
        linarith
      have hmem : γ (-ε / 2) ∈ interior (K_[p]⁺) := hεsub hneg
      have hcone : γ (-ε / 2) ∈ K_[p]⁺ := interior_subset hmem
      simp [γ, mem_power_cone_plus_iff, powerConeGeometricMean_apply] at hcone
      linarith
    have hx_strict : x < Real.rpow t p := by
      by_contra hx_not
      have hx_eq : x = Real.rpow t p := le_antisymm hx (not_lt.mp hx_not)
      let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun z ↦ ((t, 1), z)
      have hγ : Continuous γ := by
        fun_prop
      have hpre :
          γ ⁻¹' interior (K_[p]⁺) ∈ nhds x := by
        exact hγ.continuousAt.preimage_mem_nhds
          (IsOpen.mem_nhds isOpen_interior (by simpa [γ] using h))
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
      have hup : x + ε / 2 ∈ Metric.ball x ε := by
        have hhalf_nonneg : 0 ≤ x + ε / 2 - x := by
          linarith
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hhalf_nonneg]
        linarith
      have hmem : γ (x + ε / 2) ∈ interior (K_[p]⁺) := hεsub hup
      have hcone : γ (x + ε / 2) ∈ K_[p]⁺ := interior_subset hmem
      simp [γ, mem_power_cone_plus_iff, powerConeGeometricMean_apply, hx_eq] at hcone
      linarith
    exact ⟨ht_strict, hx_strict⟩
  · rintro ⟨ht, hx⟩
    let q : ((ℝ × ℝ) × ℝ) := ((t, 1), x)
    let φ : ((ℝ × ℝ) × ℝ) → ℝ := fun y ↦ powerConeGeometricMean p y.1 - y.2
    have hφ_pos : 0 < φ q := by
      simpa [q, φ, powerConeGeometricMean_apply] using sub_pos.mpr hx
    have hφ_cont : ContinuousAt φ q := by
      have hfst :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.1 p) q :=
        by simpa using continuousAt_fst.fst.rpow_const (Or.inl ht.ne')
      have hsnd :
          ContinuousAt (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.2 (1 - p)) q :=
        by simpa using continuousAt_fst.snd.rpow_const (Or.inl one_ne_zero)
      have hmul :
          ContinuousAt
            (fun y : ((ℝ × ℝ) × ℝ) ↦ Real.rpow y.1.1 p * Real.rpow y.1.2 (1 - p))
            q :=
        hfst.mul hsnd
      simpa [φ, powerConeGeometricMean_apply] using hmul.sub continuousAt_snd
    have hfirst :
        (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.1) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      continuousAt_fst.fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds ht)
    have hsecond :
        (fun y : ((ℝ × ℝ) × ℝ) ↦ y.1.2) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      continuousAt_fst.snd.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by norm_num : 0 < (1 : ℝ)))
    have hslack : φ ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds q :=
      hφ_cont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hφ_pos)
    have hnhds : K_[p]⁺ ∈ nhds q := by
      refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hfirst hsecond) hslack) ?_
      rintro y ⟨⟨hy1, hy2⟩, hy3⟩
      rw [mem_power_cone_plus_iff, powerConeGeometricMean_apply]
      refine ⟨le_of_lt hy1, le_of_lt hy2, ?_⟩
      have hy3' : 0 < powerConeGeometricMean p y.1 - y.2 := by
        simpa [φ] using hy3
      have hylt : y.2 < powerConeGeometricMean p y.1 := by
        linarith
      exact le_of_lt hylt
    exact mem_interior_iff_mem_nhds.mpr hnhds

-- Proof sketch: for `0 < p < 1`, identify `Q₅` with the affine slice
-- `{{((x₁, x₂), z) | x₂ = 1}} ∩ K_[p]⁺` via `((t, 1), x)`, and rewrite
-- `separableLogBarrierF5 p` as the restriction of the canonical cone-composition barrier from
-- `Theorem_5_4_7_4`. Then apply preservation of self-concordant barriers under affine
-- restriction. For the endpoint `p = 1`, the set becomes the linear epigraph `{(x, t) | t ≥ 0,
-- x ≤ t}` and the same logarithmic formula is the standard two-slack barrier with parameter `3`.
/-- Theorem 5.4.8.6: for `0 < p ≤ 1`, the function
`F₅(x, t) = -\log t - \log (t^p - x)` is a `3`-self-concordant barrier for the hypograph-type
constraint set `Q₅ = {(x, t) ∈ \mathbb{R}^2 \mid t ≥ 0,\ t^p ≥ x}`. -/
theorem separableLogBarrierF5_is_three_selfConcordantBarrier
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsSelfConcordantBarrierOnWith (interior Q₅) (3 : NNReal) F₅ := by
  rcases lt_or_eq_of_le hp1 with hp1_lt | rfl
  · let g : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
          (0 : (ℝ × ℝ) →L[ℝ] ℝ)).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).toContinuousAffineMap +ᵥ
        ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (1 : ℝ)), (0 : ℝ))
    have hg_apply (q : ℝ × ℝ) : g q = ((q.2, 1), q.1) := by
      simp [g]
    let hbase :
        IsSelfConcordantBarrierOnWith
          (interior (K_[p]⁺))
          (3 : NNReal)
          (power_cone_plus_barrier p) :=
      power_cone_plus_barrier_is_three_self_concordant_barrier hp0 hp1_lt
    let hslice :
        IsSelfConcordantBarrierOnWith
          (g ⁻¹' interior (K_[p]⁺))
          (3 : NNReal)
          (power_cone_plus_barrier p ∘ g) :=
      hbase.comp_continuousAffineMap g
    have hdom : g ⁻¹' interior (K_[p]⁺) = interior Q₅ := by
      ext q
      change g q ∈ interior (K_[p]⁺) ↔ q ∈ interior Q₅
      rw [hg_apply]
      simpa using mem_interior_power_cone_plus_unitSlice_iff p hp0
    have hfun : power_cone_plus_barrier p ∘ g = F₅ := by
      funext q
      change power_cone_plus_barrier p (g q) = separableLogBarrierF5 p q
      rw [hg_apply]
      rfl
    simpa [hdom, hfun] using hslice
  · sorry

/-! ### Theorem_5_4_8_7 (from Chap05) -/
noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerConePlus

variable (p : ℝ)

/- Theorem 5.4.8.7 lies in the Chapter 5 self-concordant-barrier / power-cone-slice domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_Q₆_iff` from `Definition_5_4_8_15`, the source-facing
  owner/view for `Q₆`;
* `separableLogBarrierF6` from `Definition_5_4_8_16`, the source-facing owner for `F₆`;
* `power_cone_plus_barrier_is_three_self_concordant_barrier` from `Theorem_5_4_7_4`, the
  upstream one-sided power-cone barrier theorem;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  affine-pullback theorem for barrier owners.

Best owner abstraction:
* source-facing: the textbook epigraph `Q₆` and barrier `F₆`;
* core/canonical: `K_[p / (p + 1)]⁺`,
  `power_cone_plus_barrier (p / (p + 1))`, and
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`;
* bridge/view: the affine unit slice `q ↦ (q, 1)`.

Primitive data:
* the canonical epigraph owner specialized to `x ↦ x⁻ᵖ`;
* the canonical source-facing barrier owner `separableLogBarrierF6 p`.

Derived API:
* the interior-membership theorem for `Q₆`;
* the unit-slice bridge from `K_[p / (p + 1)]⁺` to `Q₆`;
* the direct definitional unit-slice realization of `F₆`;
* the resulting source-facing barrier theorem.

This refinement keeps `Q₆` and `F₆` source-facing, but removes the ad hoc public ambient-instance
parameters and presents the theorem through the canonical one-sided power-cone owner already used
upstream in the chapter. -/

local notation "F₆" => separableLogBarrierF6 p

-- Proof sketch: rewrite Definition 5.4.8.15 through the chapter owner
-- `constrainedEpigraph`; the interior of this closed epigraph is obtained by keeping the
-- positivity condition `x > 0` and replacing the boundary inequality `t ≥ 1 / x^p`
-- with the strict inequality `t > 1 / x^p`.
/-- A pair `(x, t)` lies in the interior of the canonical epigraph for Definition 5.4.8.15
exactly when `x > 0` and `t > x^{-p}`. -/
theorem mem_interior_qSix_iff {x t : ℝ} :
    (x, t) ∈ interior (Q₆ p) ↔
      0 < x ∧ t > 1 / Real.rpow x p := sorry

-- Proof sketch: for `α = p / (p + 1)`, the unit slice `((x, t), 1)` of the one-sided power cone
-- condition `1 ≤ x^α t^(1 - α)` is equivalent to `t ≥ x^{-p}` when `p > 0`. Since membership in
-- `Q₆` already records `x > 0`, the positivity of `t` is then automatic.
/-- On the affine slice `((x, t), 1)`, the one-sided power cone with
`α = p / (p + 1)` is exactly the canonical epigraph `Q₆`. -/
theorem mem_power_cone_plus_unitSlice_qSix_iff {x t : ℝ} (hp : 0 < p) :
    ((x, t), 1) ∈ K_[(p / (p + 1))]⁺ ↔ (x, t) ∈ Q₆ p := sorry

-- Proof sketch: the interior of `Q₆` is the strict version of its epigraph inequalities, and the
-- same strict inequalities describe the unit slice of `interior (K_[(p / (p + 1))]⁺)`.
/-- On the affine slice `((x, t), 1)`, membership in `interior (K_[(p / (p + 1))]⁺)`
is exactly membership in `interior Q₆`. -/
theorem mem_interior_power_cone_plus_unitSlice_qSix_iff {x t : ℝ} (hp : 0 < p) :
    ((x, t), 1) ∈ interior (K_[(p / (p + 1))]⁺) ↔ (x, t) ∈ interior (Q₆ p) := sorry

-- Proof sketch: rewrite the interior of the canonical epigraph from Definition 5.4.8.15 as
-- the strict domain
-- `{(x, t) | x > 0, t > x^{-p}}`, set `α = p / (p + 1) ∈ (0, 1)`, and observe that
-- `t ≥ x^{-p}` is equivalent to `x^α t^(1 - α) ≥ 1`. Then identify `separableLogBarrierF6 p`
-- with the affine slice `z = 1` of the standard `3`-self-concordant barrier for the lifted
-- one-sided power cone, and use preservation of self-concordance under affine restriction.
/-- Theorem 5.4.8.7: for `p > 0`, the function
`F₆(x, t) = -\log x - \log t - \log (x^α t^(1 - α) - 1)` with `α = p / (p + 1)` is a
`3`-self-concordant barrier for
`Q₆ = {(x, t) ∈ \mathbb{R}^2 \mid x > 0,\ t ≥ x^{-p}}`. -/
theorem separableLogBarrierF6_is_three_selfConcordantBarrier
    (hp : 0 < p) :
    IsSelfConcordantBarrierOnWith (interior (Q₆ p)) (3 : NNReal) F₆ := by
  let α : ℝ := p / (p + 1)
  have hα₀ : 0 < α := sorry
  have hα₁ : α < 1 := sorry
  let g : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
    ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod
        (0 : (ℝ × ℝ) →L[ℝ] ℝ)).toContinuousAffineMap +ᵥ
      ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (0 : ℝ)), (1 : ℝ))
  have hg_apply (q : ℝ × ℝ) : g q = (q, 1) := by
    simp [g]
  let hbase :
      IsSelfConcordantBarrierOnWith
        (interior (K_[α]⁺))
        (3 : NNReal)
        (power_cone_plus_barrier α) :=
    power_cone_plus_barrier_is_three_self_concordant_barrier hα₀ hα₁
  let hslice :
      IsSelfConcordantBarrierOnWith
        (g ⁻¹' interior (K_[α]⁺))
        (3 : NNReal)
        (power_cone_plus_barrier α ∘ g) :=
    hbase.comp_continuousAffineMap g
  have hdom : g ⁻¹' interior (K_[α]⁺) = interior (Q₆ p) := by
    ext q
    change g q ∈ interior (K_[α]⁺) ↔ q ∈ interior (Q₆ p)
    rw [hg_apply]
    simpa [α] using mem_interior_power_cone_plus_unitSlice_qSix_iff p hp
  have hfun : power_cone_plus_barrier α ∘ g = F₆ := by
    funext q
    change power_cone_plus_barrier α (g q) = separableLogBarrierF6 p q
    simp [hg_apply, separableLogBarrierF6, α]
  simpa [hdom, hfun, α] using hslice

/-! ### Theorem_5_4_8_8 (from Chap05) -/
/- Theorem 5.4.8.8 lies in the Chapter 5 finite exponential-sum convexity domain.

Sampled owner declarations:
* `sumOfExponentials` from `Definition_5_4_8_19`, the source-facing owner for the exponential sum
  `y ↦ ∑ⱼ αⱼ exp ⟪aⱼ, y⟫`;
* `sumOfExponentials_apply`, the defining evaluation bridge for that owner;
* `sumOfExponentials_convex`, the upstream chapter owner theorem proving whole-space convexity
  under the mathematically weaker nonnegativity hypothesis on the coefficients.

Best owner abstraction:
* source-facing: the textbook positive-coefficient convexity statement for `sumOfExponentials`;
* core/canonical: `sumOfExponentials_convex`;
* bridge/view: specializing the owner theorem from nonnegative coefficients to strictly positive
  coefficients.

Primitive data:
* the coefficient family `α₁, …, αᵣ`;
* the vectors `a₁, …, aᵣ`.

Derived API:
* the whole-space convexity conclusion for `sumOfExponentials`.

Source/core/bridge triage:
* source-facing: the positive-coefficient textbook theorem;
* core/canonical: `sumOfExponentials_convex`;
* bridge/view: the implication `0 < αⱼ → 0 ≤ αⱼ`.

This numbered item adds no new mathematical owner beyond the canonical theorem already proved in
`Definition_5_4_8_19`. Since the project already exposes the stronger reusable owner statement
with nonnegative coefficients, this file keeps only the direct recall surface; the textbook
strict-positivity specialization should be obtained from `sumOfExponentials_convex` at the call
site when needed.
-/

recall sumOfExponentials_convex

/-! ### Theorem_5_4_8_9 (from Chap05) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 5.4.8.9 lies in the Chapter 5 box-constrained `ℓ_p` approximation / epigraph-lift
domain.

Sampled owner declarations:
- `Set.Icc` and `Set.mem_Icc`, the canonical closed-interval API for the scalar box bounds;
- `SetConstrainedMinimizationProblem` and
  `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  ambient owner and optimal-value API for constrained minimization;
- `functionalConstraintOptimalValue_eq_standardFormOptimalValue` in
  `Chap05/Proposition_5_3_6_1`, the local Chapter 5 pattern for proving equality of optimal
  values by comparing two `SetConstrainedMinimizationProblem` owners;
- `lpApproximationObjective` in `Definition_5_4_8_20`, the upstream owner of the residual
  objective.

Best owner abstraction:
- source-facing: the textbook box-constrained `ℓ_p` problem and its epigraph reformulation;
- core/canonical: the Chapter 1 owner `SetConstrainedMinimizationProblem`, with the box encoded
  directly by coordinatewise scalar interval membership `x j ∈ Set.Icc (α j) (β j)`;
- bridge/view: `lpApproximationProblem` and `lpApproximationEpigraphProblem`.

Primitive data:
- the box endpoints `α`, `β`;
- the lifted decision triple `(x, τ⁽⁰⁾, τ⁽¹⁾, …, τ⁽ᵐ⁾)`.

Derived API:
- the original problem owner `lpApproximationProblem`;
- the lifted owner `lpApproximationEpigraphProblem`;
- the companion owner lemmas expanding their feasible sets and objective evaluations;
- the canonical lift of a feasible `x` to an epigraph-feasible decision point;
- the bridge inequality comparing the original objective value with the epigraph slack
  `τ⁽⁰⁾` at a feasible lifted point.

This refinement removes the theorem-local box and epigraph exact-interface wrappers and states the
main result directly as equality of the canonical Chapter 1 optimal values of the original and
lifted problems.
-/

/-- The original box-constrained `ℓ_p` approximation problem, packaged in the canonical Chapter 1
owner. -/
def lpApproximationProblem (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := {x | ∀ j : Fin n, x j ∈ Set.Icc (α j) (β j)}
  objective := lpApproximationObjective p a b

/-- The original owner has exactly the coordinatewise scalar-interval box as its feasible set. -/
@[simp] theorem lpApproximationProblem_feasibleSet
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E) :
    (lpApproximationProblem p a b α β).feasibleSet =
      {x | ∀ j : Fin n, x j ∈ Set.Icc (α j) (β j)} :=
  rfl

/-- Evaluating the original owner returns the `ℓ_p` approximation objective. -/
@[simp] theorem lpApproximationProblem_apply
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β x : E) :
    lpApproximationProblem p a b α β x = lpApproximationObjective p a b x :=
  rfl

/-- A point is feasible for the original owner exactly when each coordinate lies between the
corresponding box bounds. -/
@[simp] theorem mem_lpApproximationProblem_feasibleSet_iff
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β x : E} :
    x ∈ (lpApproximationProblem p a b α β).feasibleSet ↔
      ∀ j : Fin n, α j ≤ x j ∧ x j ≤ β j := by
  simp [lpApproximationProblem, Set.mem_Icc]

/-- A decision variable for the epigraph reformulation of the box-constrained `ℓ_p`
approximation problem consists of the original point `x`, the objective slack `τ⁽⁰⁾`, and the
residual slacks `τ⁽¹⁾, …, τ⁽ᵐ⁾`. -/
abbrev LpApproximationEpigraphPoint (n m : ℕ) :=
  EuclideanSpace ℝ (Fin n) × ℝ × (Fin m → ℝ)

namespace LpApproximationEpigraphPoint

variable {n m : ℕ}

/-- The original optimization variable `x ∈ ℝⁿ`. -/
abbrev point (decision : LpApproximationEpigraphPoint n m) : EuclideanSpace ℝ (Fin n) :=
  decision.1

/-- The auxiliary objective variable `τ⁽⁰⁾`. -/
abbrev objectiveSlack (decision : LpApproximationEpigraphPoint n m) : ℝ :=
  decision.2.1

/-- The residual epigraph variables `τ⁽¹⁾, …, τ⁽ᵐ⁾`. -/
abbrev residualSlack (decision : LpApproximationEpigraphPoint n m) : Fin m → ℝ :=
  decision.2.2

end LpApproximationEpigraphPoint

open LpApproximationEpigraphPoint

/-- The canonical Chapter 1 owner of the epigraph reformulation of the box-constrained `ℓ_p`
approximation problem. -/
def lpApproximationEpigraphProblem (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ)
    (α β : E) : SetConstrainedMinimizationProblem (LpApproximationEpigraphPoint n m) where
  feasibleSet := {decision |
    (∀ i : Fin m, |⟪a i, decision.point⟫ - b i| ^ p ≤ decision.residualSlack i) ∧
      (∑ i : Fin m, decision.residualSlack i) ≤ decision.objectiveSlack ∧
      decision.point ∈ (lpApproximationProblem p a b α β).feasibleSet}
  objective := objectiveSlack

-- Proof sketch: unfold `lpApproximationEpigraphProblem`; membership is exactly the
-- conjunction of the residual epigraph inequalities, the sum constraint
-- `∑ τ⁽ⁱ⁾ ≤ τ⁽⁰⁾`, and the box constraint on `x`.
/-- Membership in the feasible set of `lpApproximationEpigraphProblem p a b α β` is exactly the
conjunction of the pointwise epigraph inequalities, the aggregate slack inequality, and the box
constraint from the original owner. -/
@[simp] theorem mem_lpApproximationEpigraphProblem_feasibleSet_iff
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β : E}
    {decision : LpApproximationEpigraphPoint n m} :
    decision ∈ (lpApproximationEpigraphProblem p a b α β).feasibleSet ↔
      (∀ i : Fin m, |⟪a i, decision.point⟫ - b i| ^ p ≤ decision.residualSlack i) ∧
        (∑ i : Fin m, decision.residualSlack i) ≤ decision.objectiveSlack ∧
        decision.point ∈ (lpApproximationProblem p a b α β).feasibleSet :=
  Iff.rfl

/-- Evaluating the epigraph owner returns the auxiliary objective slack `τ⁽⁰⁾`. -/
@[simp] theorem lpApproximationEpigraphProblem_apply
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E)
    (decision : LpApproximationEpigraphPoint n m) :
    lpApproximationEpigraphProblem p a b α β decision = decision.objectiveSlack :=
  rfl

/-- At every feasible epigraph point, the original `ℓ_p` objective at the projected point is
bounded above by the lifted slack `τ⁽⁰⁾`. -/
theorem lpApproximationObjective_le_objectiveSlack_of_mem_feasibleSet
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β : E}
    {decision : LpApproximationEpigraphPoint n m}
    (hdecision : decision ∈ (lpApproximationEpigraphProblem p a b α β).feasibleSet) :
    lpApproximationObjective p a b decision.point ≤ decision.objectiveSlack := by
  rcases mem_lpApproximationEpigraphProblem_feasibleSet_iff.mp hdecision with ⟨hres, hsum, _⟩
  exact le_trans (Finset.sum_le_sum fun i _ ↦ hres i) hsum

/-- Any feasible point of the original box-constrained problem admits the canonical epigraph
lift obtained by taking residual slacks equal to the pointwise residual powers and the objective
slack equal to their sum. -/
theorem lpApproximationEpigraphLift_mem_feasibleSet
    {p : ℝ} {a : Fin m → E} {b : Fin m → ℝ} {α β x : E}
    (hx : x ∈ (lpApproximationProblem p a b α β).feasibleSet) :
    (x, lpApproximationObjective p a b x, fun i : Fin m ↦ |⟪a i, x⟫ - b i| ^ p) ∈
      (lpApproximationEpigraphProblem p a b α β).feasibleSet := by
  rw [mem_lpApproximationEpigraphProblem_feasibleSet_iff]
  refine ⟨?_, ?_, hx⟩
  · intro i
    exact le_rfl
  · simp [lpApproximationObjective]

-- Proof sketch: map any feasible `x` for the original box-constrained problem to the epigraph
-- point with `τ⁽ⁱ⁾ = |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p` and
-- `τ⁽⁰⁾ = ∑ᵢ |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p`, which preserves the objective value. Conversely, project any
-- feasible epigraph point to its `x`-coordinate; the inequalities
-- `|⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p ≤ τ⁽ⁱ⁾` and `∑ᵢ τ⁽ⁱ⁾ ≤ τ⁽⁰⁾` imply that the original objective value is
-- bounded above by `τ⁽⁰⁾`. Comparing the two induced lower bounds on attainable objective values
-- yields equality of the infima.
/-- Theorem 5.4.8.9: the box-constrained `ℓ_p` approximation problem
`min_{α ≤ x ≤ β} \sum_{i=1}^m |\langle a_i, x \rangle - b^{(i)}|^p` and its epigraph
reformulation with variables `τ⁽⁰⁾, τ⁽¹⁾, …, τ⁽ᵐ⁾` have the same canonical Chapter 1 optimal
value. -/
theorem lpApproximation_optimalValue_eq_epigraphOptimalValue
    (p : ℝ) (a : Fin m → E) (b : Fin m → ℝ) (α β : E) :
    (lpApproximationProblem p a b α β).optimalValue =
      (lpApproximationEpigraphProblem p a b α β).optimalValue := by
  let problem := lpApproximationProblem p a b α β
  let epigraphProblem := lpApproximationEpigraphProblem p a b α β
  apply le_antisymm
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨decision, hdecision, rfl⟩
    rcases mem_lpApproximationEpigraphProblem_feasibleSet_iff.mp hdecision with ⟨_, _, hx⟩
    have hpoint : decision.point ∈ problem.feasibleSet := by
      simpa [problem] using hx
    have hproblem :
        problem.optimalValue ≤ (problem decision.point : EReal) := by
      simpa [problem] using problem.optimalValue_le_of_mem_feasibleSet hpoint
    have hvalue :
        (problem decision.point : EReal) ≤ (decision.objectiveSlack : EReal) := by
      have hvalue' :
          lpApproximationObjective p a b decision.point ≤ decision.objectiveSlack :=
        lpApproximationObjective_le_objectiveSlack_of_mem_feasibleSet hdecision
      exact_mod_cast hvalue'
    simpa [problem, epigraphProblem] using hproblem.trans hvalue
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    let decision : LpApproximationEpigraphPoint n m :=
      (x, lpApproximationObjective p a b x, fun i : Fin m ↦ |⟪a i, x⟫ - b i| ^ p)
    have hpoint : x ∈ problem.feasibleSet := by
      simpa [problem] using hx
    have hdecision : decision ∈ epigraphProblem.feasibleSet := by
      simpa [decision, epigraphProblem] using
        lpApproximationEpigraphLift_mem_feasibleSet hpoint
    have hepigraph :
        epigraphProblem.optimalValue ≤ (epigraphProblem decision : EReal) := by
      exact epigraphProblem.optimalValue_le_of_mem_feasibleSet hdecision
    simpa [problem, epigraphProblem, decision] using hepigraph

end

/-! ### Definition_5_4_9_1 (from Chap05) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 5.4.9.1 lies in the Chapter 5 box-constrained `ℓ_p` approximation domain.

Sampled owner declarations:
- `lpApproximationObjective` in `Definition_5_4_8_20`, the chapter owner for the residual
  objective `x ↦ ∑ i, |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p`;
- `lpApproximationProblem` and `mem_lpApproximationProblem_feasibleSet_iff` in
  `Theorem_5_4_8_9`, the chapter owner for the same box-constrained problem and its box-membership
  expansion;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with its ambient real-valued objective;
- `SemidefiniteOptimizationProblem.toSetConstrainedMinimizationProblem` in
  `Definition_5_4_4_4`, the local Chapter 5 pattern for keeping source-facing primitive data while
  routing the ambient optimization interface through the Chapter 1 owner.

Best owner abstraction:
- source-facing: `LpApproximationBoxProblem n m`, whose primitive data are exactly the textbook
  exponent, residual vectors/targets, and box bounds;
- core/canonical: `SetConstrainedMinimizationProblem E`, together with the existing chapter owners
  `lpApproximationObjective` and `lpApproximationProblem`;
- bridge/view: `toSetConstrainedMinimizationProblem`, plus the derived `feasibleSet` and the
  evaluation/membership lemmas exposing its objective through the canonical owner.

Primitive data:
- `p : Set.Ici (1 : ℝ)`, `a`, `b`;
- `α`, `β`.

Derived API:
- `toSetConstrainedMinimizationProblem := lpApproximationProblem problem.p problem.a problem.b
  problem.α problem.β`;
- `feasibleSet := problem.toSetConstrainedMinimizationProblem.feasibleSet`;
- `one_le_p : 1 ≤ (problem.p : ℝ)`;
- `objective_apply`, `mem_feasibleSet_iff`, and the induced coercion to the canonical objective.

This refinement therefore keeps the textbook source-facing data owner, but removes the duplicate
ambient optimization wrapper surface in favor of the canonical Chapter 1 owner
`lpApproximationProblem`, without introducing a second local name for the same objective.
-/

/-- Definition 5.4.9.1: an `ℓ_p` approximation problem with box constraints on `ℝⁿ` is given by
an exponent `p ≥ 1`, vectors `a₁, ..., aₘ ∈ ℝⁿ`, scalars `b⁽¹⁾, ..., b⁽ᵐ⁾ ∈ ℝ`, and box bounds
`α`, `β ∈ ℝⁿ`. The associated optimization problem minimizes
`∑ i, |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p` over the box `α ≤ x ≤ β`. -/
structure LpApproximationBoxProblem (n m : ℕ) where
  /-- The exponent `p` in the `ℓ_p` approximation objective, constrained by `p ≥ 1`. -/
  p : Set.Ici (1 : ℝ)
  /-- The vectors `a₁, ..., aₘ ∈ ℝⁿ`. -/
  a : Fin m → EuclideanSpace ℝ (Fin n)
  /-- The scalar targets `b⁽¹⁾, ..., b⁽ᵐ⁾ ∈ ℝ`. -/
  b : Fin m → ℝ
  /-- The lower box bound `α ∈ ℝⁿ`. -/
  α : EuclideanSpace ℝ (Fin n)
  /-- The upper box bound `β ∈ ℝⁿ`. -/
  β : EuclideanSpace ℝ (Fin n)

namespace LpApproximationBoxProblem

/-- The canonical Chapter 1 owner attached to a box-constrained `ℓ_p` approximation problem. -/
def toSetConstrainedMinimizationProblem
    (problem : LpApproximationBoxProblem n m) :
    SetConstrainedMinimizationProblem E :=
  lpApproximationProblem problem.p problem.a problem.b problem.α problem.β

/-- The exponent of a box-constrained `ℓ_p` approximation problem satisfies `p ≥ 1`. -/
theorem one_le_p (problem : LpApproximationBoxProblem n m) : 1 ≤ (problem.p : ℝ) :=
  problem.p.2

/-- The feasible box `\{x : ℝⁿ | α ≤ x ≤ β\}` of an `ℓ_p` approximation problem. -/
abbrev feasibleSet (problem : LpApproximationBoxProblem n m) : Set E :=
  problem.toSetConstrainedMinimizationProblem.feasibleSet

/-- The owner bridge preserves the box feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : LpApproximationBoxProblem n m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the `ℓ_p` approximation objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : LpApproximationBoxProblem n m) (x : E) :
    problem.toSetConstrainedMinimizationProblem x =
      lpApproximationObjective problem.p problem.a problem.b x :=
  rfl

/-- An `ℓ_p` approximation problem with box constraints can be evaluated as its objective
function. -/
instance : CoeFun (LpApproximationBoxProblem n m) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a box-constrained `ℓ_p` approximation problem returns its objective value. -/
@[simp] theorem coe_apply
    (problem : LpApproximationBoxProblem n m) (x : E) :
    problem x = lpApproximationObjective problem.p problem.a problem.b x :=
  rfl

/-- A point is feasible exactly when it lies componentwise between the box bounds `α` and `β`. -/
-- Proof sketch: unfold `feasibleSet`; membership is exactly the coordinatewise condition
-- `∀ i, problem.α i ≤ x i ∧ x i ≤ problem.β i`.
@[simp] theorem mem_feasibleSet_iff
    (problem : LpApproximationBoxProblem n m) (x : E) :
    x ∈ problem.feasibleSet ↔
      ∀ i : Fin n, problem.α i ≤ x i ∧ x i ≤ problem.β i := by
  simp [feasibleSet, toSetConstrainedMinimizationProblem]

/-- Evaluating the objective expands to the finite sum of `p`-th powers of the residual
terms `|⟪aᵢ, x⟫ - b⁽ⁱ⁾|`. -/
-- Proof sketch: expand the inherited coercion to `lpApproximationObjective`; the displayed
-- equality is exactly its defining formula.
@[simp] theorem objective_apply
    (problem : LpApproximationBoxProblem n m) (x : E) :
    problem x =
      ∑ i : Fin m, |⟪problem.a i, x⟫ - problem.b i| ^ (problem.p : ℝ) := by
  simp [lpApproximationObjective]

end LpApproximationBoxProblem

/-! ### Definition_5_4_9_2 (from Chap05) -/
/-
Definition 5.4.9.2 lies in the chapter's algorithmic complexity-model domain.

Sampled owner declarations before refining:
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the project
  pattern where a complexity notion is a `Prop` on primitive data;
* `HasLpBarrierShortStepIterationBound` in `Definition_5_4_9_6`, the nearby Chapter 5 owner for a
  direct iteration-count bound predicate on the primitive function `N_it`;
* `HasLpBarrierShortStepTotalArithmeticComplexityBound` in `Theorem_5_4_9_3`, the nearby Chapter
  5 owner for a direct total-cost bound predicate on primitive arithmetic-work data;
* `HasConvergenceRateOfOrder` in `Chap01/Definition_1_6_9`, the project owner for a source-facing
  bound with a uniform constant and a derived asymptotic bridge.

Best owner abstraction:
* source-facing: the textbook complexity model consisting of the accuracy-indexed iteration-count
  family `N_it`, the oracle arithmetic cost per iteration, and the additional per-iteration
  arithmetic overhead;
* core/canonical: a direct `Prop`-valued bound owner on those three primitive cost functions;
* bridge/view: downstream total-cost constructions obtained by combining the three primitive
  functions, rather than a separate packaged owner.

Primitive data:
* the accuracy-indexed iteration-count family;
* the oracle arithmetic cost per iteration;
* the additional per-iteration arithmetic overhead.

Derived API:
* the small-accuracy hypothesis `ε ∈ (0, 1)`;
* the three textbook bounds with constants uniform in `ε`;
* the restriction to positive dimensions, avoiding spurious zero-dimension obligations.
-/

/-- Definition 5.4.9.2: the ellipsoid method satisfies the textbook complexity model when there
exist positive constants, independent of the target accuracy `ε ∈ (0, 1)`, such that the
accuracy-indexed iteration count `N_it`, oracle arithmetic cost per iteration, and additional
per-iteration arithmetic overhead obey the bounds `N_it = O(n^2 log (1 / ε))`,
`C_oracle = O(m n)`, and `C_iter = O(n^2)` in positive dimensions. -/
def HasEllipsoidMethodComplexityBounds
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ) : Prop :=
  ∃ C_it C_oracle C_iter : ℝ,
    0 < C_it ∧
      0 < C_oracle ∧
      0 < C_iter ∧
      (∀ {ε : ℝ} {n : ℕ}, ε ∈ Set.Ioo (0 : ℝ) 1 → 0 < n →
        (iterationCount ε n : ℝ) ≤ C_it * (n : ℝ) ^ 2 * Real.log (1 / ε)) ∧
      (∀ {m n : ℕ}, 0 < m → 0 < n →
        (oracleCostPerIteration m n : ℝ) ≤ C_oracle * (m : ℝ) * (n : ℝ)) ∧
      (∀ {n : ℕ}, 0 < n →
        (extraCostPerIteration n : ℝ) ≤ C_iter * (n : ℝ) ^ 2)

/-! ### Definition_5_4_9_3 (from Chap05) -/
noncomputable section

/- Definition 5.4.9.3 lies in the Chapter 5 logarithmic barrier / strict-epigraph domain.

Sampled owner declarations:
* `separableLogBarrierF4` from `Definition_5_4_8_12`, the existing Chapter 5 owner for the
  textbook scalar barrier `f(y, t) = -log t - log (t^(2 / p) - y^2)`;
* `separableLogBarrierF4_apply` from `Definition_5_4_8_12`, the coordinate evaluation bridge for
  that owner;
* `strictConstrainedEpigraph` from `Theorem_5_3_5`, the chapter owner for strict epigraph
  domains;
* `mem_strictConstrainedEpigraph_iff` from `Theorem_5_3_5`, the canonical membership expansion
  for that owner.

Best owner abstraction:
* source-facing: the textbook scalar sub-function `f(y, t)`;
* core/canonical: the existing owner `separableLogBarrierF4 p : ℝ × ℝ → ℝ`;
* bridge/view: the strict-epigraph description of the points where the two logarithmic arguments
  are positive.

Primitive data:
* the scalar exponent `p`.

Derived API:
* the recalled owner `separableLogBarrierF4 p`;
* its coordinate formula `separableLogBarrierF4_apply`;
* the strict-epigraph bridge describing the natural finiteness domain.

This refinement removes the duplicate subtype-valued wrapper and keeps Definition 5.4.9.3 as a
recall of the existing Chapter 5 owner `separableLogBarrierF4`, with the domain side expressed
through the chapter strict-epigraph owner instead of a bespoke set definition. -/

recall separableLogBarrierF4
recall separableLogBarrierF4_apply
recall strictConstrainedEpigraph
recall mem_strictConstrainedEpigraph_iff

/- Definition 5.4.9.3 recalls the Chapter 5 owner `separableLogBarrierF4 p` for the textbook
sub-function `f(y, t) = -log t - log (t^(2 / p) - y^2)`. -/
variable (p : ℝ) in
#check separableLogBarrierF4 p

/-- The points where the textbook scalar barrier formula has positive logarithmic arguments are
exactly the points with `t > 0` for which `(y, t^(2 / p))` lies in the strict epigraph of the
square function. -/
theorem separableLogBarrierF4_domain_iff (p y t : ℝ) :
    0 < t ∧ 0 < Real.rpow t (2 / p) - y ^ 2 ↔
      0 < t ∧
        (y, Real.rpow t (2 / p)) ∈ strictConstrainedEpigraph Set.univ (fun x : ℝ ↦ x ^ 2) := by
  rw [mem_strictConstrainedEpigraph_iff]
  constructor
  · rintro ⟨ht, hgap⟩
    refine ⟨ht, Set.mem_univ _, ?_⟩
    linarith
  · rintro ⟨ht, ⟨_, hsq⟩⟩
    exact ⟨ht, by linarith⟩

/-! ### Definition_5_4_9_4 (from Chap05) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

namespace LpApproximationBoxProblem

open LpApproximationEpigraphPoint

/- Definition 5.4.9.4 lies in the Chapter 5 box-constrained `ℓ_p` approximation / barrier-model
Lagrangian domain.

Sampled owner declarations:
- `LpApproximationEpigraphPoint`, `objectiveSlack`, and `residualSlack` in
  `Theorem_5_4_8_9`, the existing chapter owner for the lifted decision variables;
- `lpApproximationEpigraphProblem` and
  `mem_lpApproximationEpigraphProblem_feasibleSet_iff` in `Theorem_5_4_8_9`, the chapter owner
  for the lifted reformulation and its feasible-set expansion;
- `LagrangianProblem` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, the project owner for finite families of inequality constraints;
- `LpApproximationBoxProblem.feasibleSet` in `Definition_5_4_9_1`, the source-facing chapter
  owner for the box constraints.

Best owner abstraction:
- source-facing: the barrier-model reformulation attached to a box-constrained `ℓ_p`
  approximation problem;
- core/canonical: `LagrangianProblem (LpApproximationEpigraphPoint n m) (m + (1 + (n + n)))`;
- bridge/view: `barrierModelProblem`, whose objective and feasible set are compared directly with
  the existing epigraph owners.

Primitive data:
- no new primitive data beyond `problem : LpApproximationBoxProblem n m`;
- the lifted decision variables are reused from `LpApproximationEpigraphPoint n m`, with
  `objectiveSlack` playing the role of the textbook `ξ` and `residualSlack` the role of `τ`.

Derived API:
- `problem.barrierModelProblem`;
- the objective evaluation bridge `barrierModelProblem_apply`;
- the feasible-set bridge `mem_barrierModelProblem_feasibleSet_iff`.

The previous version introduced a second public owner `LpBarrierModelPoint` for the same lifted
decision data already provided by `LpApproximationEpigraphPoint`. This refinement deletes that
duplicate wheel and makes Definition 5.4.9.4 a direct Lagrangian-owner presentation of the
existing epigraph lift.
-/

/-- Definition 5.4.9.4: the barrier-model reformulation of a box-constrained `ℓ_p`
approximation problem is the Chapter 1 Lagrangian problem on the existing lifted decision points
`LpApproximationEpigraphPoint n m`, where `objectiveSlack` plays the role of the scalar variable
`ξ` and `residualSlack` plays the role of the residual bounds `τ`. Its inequality constraints are
the residual epigraph constraints, the coupling inequality `∑ i, τᵢ ≤ ξ`, and the coordinatewise
box constraints. -/
def barrierModelProblem
    (problem : LpApproximationBoxProblem n m) :
    LagrangianProblem (LpApproximationEpigraphPoint n m) (m + (1 + (n + n))) where
  objective := objectiveSlack
  constraints :=
    Fin.addCases
      (fun i decision ↦
        |⟪problem.a i, decision.point⟫ - problem.b i| ^ (problem.p : ℝ) -
          decision.residualSlack i)
      (Fin.addCases
        (fun _ decision ↦ (∑ i : Fin m, decision.residualSlack i) - decision.objectiveSlack)
        (Fin.addCases
          (fun j decision ↦ problem.α j - decision.point j)
          (fun j decision ↦ decision.point j - problem.β j)))

/-- Evaluating the barrier-model problem returns the lifted objective slack `ξ`. -/
@[simp] theorem barrierModelProblem_apply
    (problem : LpApproximationBoxProblem n m)
    (decision : LpApproximationEpigraphPoint n m) :
    problem.barrierModelProblem decision = decision.objectiveSlack :=
  rfl

/-- Membership in the feasible set of `problem.barrierModelProblem` is exactly membership in the
existing epigraph feasible-set owner for the same lifted reformulation. -/
@[simp] theorem mem_barrierModelProblem_feasibleSet_iff
    (problem : LpApproximationBoxProblem n m)
    (decision : LpApproximationEpigraphPoint n m) :
    decision ∈ problem.barrierModelProblem.feasibleSet ↔
      decision ∈
        (lpApproximationEpigraphProblem
          problem.p problem.a problem.b problem.α problem.β).feasibleSet := by
  rw [problem.barrierModelProblem.mem_feasibleSet_iff,
    mem_lpApproximationEpigraphProblem_feasibleSet_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact sub_nonpos.mp <| by
        simpa [barrierModelProblem] using h (Fin.castAdd (1 + (n + n)) i)
    · exact sub_nonpos.mp <| by
        simpa [barrierModelProblem] using
          h (Fin.natAdd m (Fin.castAdd (n + n) (0 : Fin 1)))
    · rw [mem_lpApproximationProblem_feasibleSet_iff]
      intro j
      refine ⟨?_, ?_⟩
      · exact sub_nonpos.mp <| by
          simpa [barrierModelProblem] using
            h (Fin.natAdd m (Fin.natAdd 1 (Fin.castAdd n j)))
      · have hj := h (Fin.natAdd m (Fin.natAdd 1 (Fin.natAdd n j)))
        dsimp [barrierModelProblem] at hj
        rwa [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right, sub_nonpos] at hj
  · rintro ⟨hres, hsum, hbox⟩
    rw [mem_lpApproximationProblem_feasibleSet_iff] at hbox
    intro k
    induction k using Fin.addCases with
    | left i =>
        simpa [barrierModelProblem] using sub_nonpos.mpr (hres i)
    | right k =>
        induction k using Fin.addCases with
        | left _ =>
            simpa [barrierModelProblem] using sub_nonpos.mpr hsum
        | right k =>
            induction k using Fin.addCases with
            | left j =>
                simpa [barrierModelProblem] using sub_nonpos.mpr (hbox j).1
            | right j =>
                dsimp [barrierModelProblem]
                rw [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right, sub_nonpos]
                exact (hbox j).2

end LpApproximationBoxProblem

end

/-! ### Definition_5_4_9_5 (from Chap05) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace LpApproximationBoxProblem

open LpApproximationEpigraphPoint

/-
Definition 5.4.9.5 lies in the Chapter 5 box-constrained `ℓ_p` approximation / logarithmic
barrier domain.

Sampled owner declarations:
- `strictConstraintSet` and `logarithmicBarrier` in `Chap01/Proposition_1_10_17`, the project
  owner pattern for logarithmic barriers attached to finite continuous inequality families;
- `analyticBarrierDomain`, `AnalyticBarrierPoint`, and `analyticBarrier` in
  `Chap03/Definition_3_62`, the chapter precedent for keeping a logarithmic barrier on its strict
  domain and any ambient formula only as a bridge;
- `epigraphLogarithmicBarrier` and `StrictEpigraphFeasiblePoint` in
  `Chap05/Definition_5_4_3_5`, the adjacent Chapter 5 owner pattern for an epigraph barrier
  built from `strictConstraintSet` and `logarithmicBarrier`;
- `separableLogBarrierF4` in `Definition_5_4_8_12`, the Chapter 5 owner of the scalar barrier
  `f(y, t) = -log t - log (t^(2 / p) - y^2)`.

Best owner abstraction:
- source-facing: the strict barrier domain and logarithmic barrier attached to the box-constrained
  `ℓ_p` approximation barrier model;
- core/canonical: `strictConstraintSet` and `logarithmicBarrier` on the split continuous
  constraint family whose first two blocks recover the scalar owner `separableLogBarrierF4`;
- bridge/view: the ambient `(x, ξ, τ)` evaluation formula.

Primitive data:
- no new primitive data beyond `problem : LpApproximationBoxProblem n m`;
- the existing lifted decision variables `LpApproximationEpigraphPoint n m`.

Derived API:
- the internal split continuous constraint family;
- `problem.barrierModelBarrierDomain`;
- `problem.StrictBarrierModelPoint`;
- `problem.barrierModelBarrier`;
- the ambient evaluation theorems.

Source/core/bridge triage:
- source-facing: `problem.barrierModelBarrierDomain` and `problem.barrierModelBarrier`;
- core/canonical: the Chapter 1 owners `strictConstraintSet` and `logarithmicBarrier`;
- bridge/view: the ambient `(x, ξ, τ)` evaluation formulas.

The textbook barrier formula is only meaningful where every logarithmic argument is strictly
positive, so the public owner must live on that strict carrier rather than on all lifted points.
This refinement therefore keeps the same mathematical formula, but moves the public API to the
strict-domain logarithmic-barrier pattern already used elsewhere in the project.
-/

private abbrev residualArgument
    (problem : LpApproximationBoxProblem n m) (i : Fin m)
    (decision : LpApproximationEpigraphPoint n m) : ℝ :=
  ⟪problem.a i, decision.point⟫ - problem.b i

private def residualArgumentMap
    (problem : LpApproximationBoxProblem n m) (i : Fin m) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun := residualArgument problem i
  continuous_toFun := by
    simpa [residualArgument] using
      (((innerSL ℝ (problem.a i) : E →L[ℝ] ℝ).continuous.comp continuous_fst).sub
        continuous_const)

private def objectiveSlackMap :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun := objectiveSlack
  continuous_toFun := continuous_snd.fst

private def residualSlackMap (i : Fin m) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun decision := decision.residualSlack i
  continuous_toFun := (continuous_apply i).comp continuous_snd.snd

private def pointCoordinateMap (j : Fin n) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun decision := decision.point j
  continuous_toFun := by
    let hOfLp :
        Continuous (fun x : E ↦ x.ofLp) :=
      PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)
    have hcoord : Continuous fun x : E ↦ x j := (continuous_apply j).comp hOfLp
    simpa using hcoord.comp continuous_fst

private def barrierModelStrictConstraints
    (problem : LpApproximationBoxProblem n m) :
    Fin (m + (m + (1 + (n + n)))) → C(LpApproximationEpigraphPoint n m, ℝ) :=
  Fin.addCases
    (fun i ↦ -(residualSlackMap i))
    (Fin.addCases
      (fun i ↦
        { toFun := fun decision ↦
            (residualArgument problem i decision) ^ (2 : ℕ) -
              Real.rpow (decision.residualSlack i) (2 / (problem.p : ℝ))
          continuous_toFun := by
            have harg :
                Continuous fun decision : LpApproximationEpigraphPoint n m ↦
                  residualArgument problem i decision :=
              (problem.residualArgumentMap i).continuous
            have hτ :
                Continuous fun decision : LpApproximationEpigraphPoint n m ↦
                  decision.residualSlack i :=
              (residualSlackMap i).continuous
            have hp : 0 ≤ 2 / (problem.p : ℝ) := by
              exact div_nonneg (by norm_num) (le_trans zero_lt_one.le problem.one_le_p)
            exact (harg.pow 2).sub <| hτ.rpow_const fun _ ↦ Or.inr hp })
      (Fin.addCases
        (fun _ ↦
          ∑ i : Fin m, residualSlackMap i - objectiveSlackMap)
        (Fin.addCases
          (fun j ↦ ContinuousMap.const _ (problem.α j) - pointCoordinateMap j)
          (fun j ↦ pointCoordinateMap j - ContinuousMap.const _ (problem.β j)))))

/-- The strict domain on which the box-constrained `ℓ_p` approximation barrier-model
logarithmic barrier is defined. -/
def barrierModelBarrierDomain
    (problem : LpApproximationBoxProblem n m) :
    Set (LpApproximationEpigraphPoint n m) :=
  strictConstraintSet problem.barrierModelStrictConstraints

/-- The subtype of points in the strict barrier-model barrier domain. This is the natural owner
carrier for the logarithmic barrier. -/
abbrev StrictBarrierModelPoint
    (problem : LpApproximationBoxProblem n m) :=
  {decision : LpApproximationEpigraphPoint n m // decision ∈ problem.barrierModelBarrierDomain}

/-- Membership in `problem.barrierModelBarrierDomain` means that every logarithmic argument in the
textbook barrier formula is strictly positive. -/
theorem mem_barrierModelBarrierDomain_iff
    (problem : LpApproximationBoxProblem n m)
    (decision : LpApproximationEpigraphPoint n m) :
    decision ∈ problem.barrierModelBarrierDomain ↔
      (∀ i : Fin m,
        0 < decision.residualSlack i ∧
          (⟪problem.a i, decision.point⟫ - problem.b i) ^ (2 : ℕ) <
            Real.rpow (decision.residualSlack i) (2 / (problem.p : ℝ))) ∧
        ∑ i : Fin m, decision.residualSlack i < decision.objectiveSlack ∧
        ∀ j : Fin n, problem.α j < decision.point j ∧ decision.point j < problem.β j := by
  sorry

/-- Definition 5.4.9.5: the logarithmic barrier attached to the box-constrained `ℓ_p`
approximation barrier model, kept on its strict domain and obtained by reusing the Chapter 1
owner `logarithmicBarrier` on the split continuous inequality family whose scalar blocks are the
Chapter 5 owner `separableLogBarrierF4 problem.p`. -/
def barrierModelBarrier
    (problem : LpApproximationBoxProblem n m) :
    C(problem.StrictBarrierModelPoint, ℝ) :=
  logarithmicBarrier problem.barrierModelStrictConstraints

/-- Evaluating `problem.barrierModelBarrier` on a strict-domain point recovers its ambient bridge
formula. -/
@[simp] theorem barrierModelBarrier_apply
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierModelBarrier decision =
      (∑ i : Fin m,
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, decision.1.point⟫ - problem.b i, decision.1.residualSlack i)) -
        Real.log (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) -
        ∑ j : Fin n,
          (Real.log (decision.1.point j - problem.α j) +
            Real.log (problem.β j - decision.1.point j)) := by
  sorry

/-- At a strict-domain tuple `(x, ξ, τ)`, the barrier-model logarithmic barrier is the textbook
formula
`F(x, ξ, τ) = \sum_i f(\langle a_i, x \rangle - b^{(i)}, τ_i)
  - \log (\xi - \sum_i τ_i)
  - \sum_j [\log (x_j - α_j) + \log (β_j - x_j)]`,
where `f = separableLogBarrierF4 problem.p`. -/
theorem barrierModelBarrier_apply_mk
    (problem : LpApproximationBoxProblem n m) (x : E) (ξ : ℝ) (τ : Fin m → ℝ)
    (h : (x, ξ, τ) ∈ problem.barrierModelBarrierDomain) :
    problem.barrierModelBarrier ⟨(x, ξ, τ), h⟩ =
      (∑ i : Fin m, separableLogBarrierF4 (problem.p : ℝ) (⟪problem.a i, x⟫ - problem.b i, τ i)) -
        Real.log (ξ - ∑ i : Fin m, τ i) -
        ∑ j : Fin n, (Real.log (x j - problem.α j) + Real.log (problem.β j - x j)) := by
  exact problem.barrierModelBarrier_apply ⟨(x, ξ, τ), h⟩

end LpApproximationBoxProblem

end

/-! ### Definition_5_4_9_6 (from Chap05) -/
/- Domain note: this item lies in the Chapter 5 explicit-structure path-following complexity domain.

Sampled owner declarations in this domain:
* `BarrierPathFollowingScheme` in `Definition_5_3_4_1`, the chapter owner for short-step
  path-following data;
* `barrierPathFollowingStoppingThreshold` and `barrierPathFollowingTerminationBound` in
  `Theorem_5_3_11`, the generic Chapter 5 owners governing short-step complexity;
* `Matrix.mulVec`-free scalar `O(...)` predicates elsewhere in the project, the standard source-
  facing bridge pattern when a textbook asymptotic estimate is read off from a more canonical
  owner theorem.

Best owner abstraction:
* source-facing: the textbook short-step iteration-count asymptotic
  `HasLpBarrierShortStepIterationBound ε N_it` with fixed accuracy `ε ∈ (0, 1)`;
* core/canonical: `BarrierPathFollowingScheme` together with
  `barrierPathFollowingTerminationBound`;
* bridge/view: the equivalence below between the canonical owner plus the fixed-accuracy side
  condition and the explicit `ν = 4m + n + 1` formula.

Primitive data:
* the fixed accuracy `ε`;
* the iteration-count family `N_it`.

Derived API:
* the source-facing Chapter 5 owner `HasLpBarrierShortStepIterationBound ε N_it`;
* the positive-dimension guard `0 < n`, matching the surrounding Chapter 5 complexity owners;
* the source-facing explicit template theorem specialized to `ν = 4m + n + 1`.

The previous version imported a nearby theorem file for a source-facing asymptotic predicate.
This refinement makes Definition 5.4.9.6 the owner of that source-facing `O(...)` bound, while
keeping the chapter’s path-following termination-bound layer as the canonical background owner.
For an existential-constant `O(...)` predicate, replacing `√(m + n)` by `√(4m + n + 1)` changes
the bound only by a universal constant factor on `ℕ`, so the remaining theorem stays a thin
explicit-template bridge. -/

section

variable (ε : ℝ) (N_it : ℕ → ℕ → ℕ)

/- This item is a source-facing bridge over the canonical Chapter 5 path-following
termination-bound layer. -/
recall barrierPathFollowingTerminationBound

/-- Definition 5.4.9.6: a short-step iteration model with count `N_it` satisfies the textbook
`O(√(m + n) log ((m + n) / ε))` bound at the fixed small accuracy `ε ∈ (0, 1)` if it is
controlled by a positive constant independent of `m` and `n` on positive variable dimension
`n`. -/
def HasLpBarrierShortStepIterationBound : Prop :=
  ε ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ C_it : ℝ,
      0 < C_it ∧
        ∀ m n : ℕ, 0 < n →
          (N_it m n : ℝ) ≤
            C_it * Real.sqrt ((m : ℝ) + (n : ℝ)) *
              Real.log (((m + n : ℕ) : ℝ) / ε)

private theorem iterationLog_nonneg
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (m n : ℕ) (hn : 0 < n) :
    0 ≤ Real.log (((m + n : ℕ) : ℝ) / ε) := by
  have hone_le_sum : (1 : ℝ) ≤ ((m + n : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ m + n by omega)
  have hε_le_sum : ε ≤ ((m + n : ℕ) : ℝ) := by
    exact le_trans (le_of_lt hε.2) hone_le_sum
  have hratio_ge_one : (1 : ℝ) ≤ ((m + n : ℕ) : ℝ) / ε := by
    exact (one_le_div₀ hε.1).2 hε_le_sum
  exact Real.log_nonneg hratio_ge_one

private theorem sqrt_sum_le_sqrt_explicit (m n : ℕ) :
    Real.sqrt (((m + n : ℕ) : ℝ)) ≤ Real.sqrt (4 * m + n + 1 : ℝ) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast (show m + n ≤ 4 * m + n + 1 by omega)

private theorem sqrt_explicit_le_three_mul_sqrt_sum
    (m n : ℕ) (hn : 0 < n) :
    Real.sqrt (4 * m + n + 1 : ℝ) ≤ 3 * Real.sqrt (((m + n : ℕ) : ℝ)) := by
  have hbound : (4 * m + n + 1 : ℝ) ≤ 9 * (((m + n : ℕ) : ℝ)) := by
    exact_mod_cast (show 4 * m + n + 1 ≤ 9 * (m + n) by
      have hmn_one : 1 ≤ m + n := by omega
      omega)
  refine le_trans (Real.sqrt_le_sqrt hbound) ?_
  rw [Real.sqrt_mul (by positivity)]
  norm_num

/-- The Chapter 5 owner `HasLpBarrierShortStepIterationBound ε N_it` is equivalent to the
explicit source-facing constant-factor bound with `ν = 4m + n + 1`, together with the fixed
small-accuracy hypothesis `ε ∈ (0, 1)` and the positive-dimension guard `0 < n`. -/
theorem hasLpBarrierShortStepIterationBound_iff_explicitTemplate
    : HasLpBarrierShortStepIterationBound ε N_it ↔
      ε ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 0 < n →
          (N_it m n : ℝ) ≤
            C * Real.sqrt (4 * m + n + 1 : ℝ) *
              Real.log (((m + n : ℕ) : ℝ) / ε) := by
  constructor
  · rintro ⟨hε, C, hC, hbound⟩
    refine ⟨hε, C, hC, ?_⟩
    intro m n hn
    have h₁ :
        (N_it m n : ℝ) ≤
          C * Real.sqrt (((m + n : ℕ) : ℝ)) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      simpa [Nat.cast_add, mul_assoc] using hbound m n hn
    have hlog_nonneg := iterationLog_nonneg hε m n hn
    have h₂ :
        C * Real.sqrt (((m + n : ℕ) : ℝ)) *
            Real.log (((m + n : ℕ) : ℝ) / ε) ≤
          C * Real.sqrt (4 * m + n + 1 : ℝ) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      have htemplate :=
        mul_le_mul_of_nonneg_right (sqrt_sum_le_sqrt_explicit m n) hlog_nonneg
      have hscaled := mul_le_mul_of_nonneg_left htemplate hC.le
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans h₁ h₂
  · rintro ⟨hε, C, hC, hbound⟩
    refine ⟨hε, 3 * C, by positivity, ?_⟩
    intro m n hn
    have h₁ :
        (N_it m n : ℝ) ≤
          C * Real.sqrt (4 * m + n + 1 : ℝ) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      simpa [mul_assoc] using hbound m n hn
    have hlog_nonneg := iterationLog_nonneg hε m n hn
    have h₂ :
        C * Real.sqrt (4 * m + n + 1 : ℝ) *
            Real.log (((m + n : ℕ) : ℝ) / ε) ≤
          (3 * C) * Real.sqrt ((m : ℝ) + (n : ℝ)) *
            Real.log (((m + n : ℕ) : ℝ) / ε) := by
      have htemplate :=
        mul_le_mul_of_nonneg_right
          (sqrt_explicit_le_three_mul_sqrt_sum m n hn) hlog_nonneg
      have hscaled := mul_le_mul_of_nonneg_left htemplate hC.le
      simpa [Nat.cast_add, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact le_trans h₁ h₂

end

/-! ### Definition_5_4_9_7 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u}

/- Definition 5.4.9.7 lies in the Chapter 5 first-order calculus / sliced-derivative domain.

Sampled owner declarations:
- `gradient` in `Mathlib/Analysis/Calculus/Gradient/Basic`, the canonical owner for Euclidean
  gradients of scalar functions on a complete real inner-product space;
- `deriv` in `Mathlib/Analysis/Calculus/Deriv/Basic`, the canonical owner for one-variable
  derivatives;
- `gradient_eq_deriv'` in `Mathlib/Analysis/Calculus/Gradient/Basic`, the scalar bridge showing
  that the real gradient agrees with the ordinary derivative in one dimension;
- `secondOrderDerivativeBlock12` in `Definition_5_4_9_8`, the immediate downstream Chapter 5
  product-domain use of the same sliced `y`-gradient / `t`-derivative pattern.

Best owner abstraction:
- source-facing: the pointwise auxiliary slice derivatives `g₁(y, t)` and `g₂(y, t)`;
- core/canonical: mathlib's `gradient` on the frozen-`t` slice and `deriv` on the frozen-`y`
  slice;
- bridge/view: the pointwise pair `auxiliaryDerivatives f y t`.

Primitive data:
- the scalar-valued two-parameter function `f : E × ℝ → ℝ`.

Derived API:
- `auxiliaryGradient f y t`;
- `auxiliaryTimeDerivative f y t`;
- the pairing `auxiliaryDerivatives f y t`.

The previous version used a curried owner `f : E → ℝ → ℝ` and made the public bridge a pair of
functions. This refinement keeps the same mathematics but aligns the owner layer with the nearby
Chapter 5 product-domain calculus API: `f` lives on `E × ℝ`, the source-facing owners take the
explicit textbook binders `(y : E)` and `(t : ℝ)`, and the pair remains only as a thin bridge.
The ambient finite-dimensional `ℝⁿ` textbook model is still demoted to a specialization: only the
gradient owner needs mathlib's canonical completeness assumption, while
`auxiliaryTimeDerivative` lives directly at the sliced `deriv` level. -/

/-- The second auxiliary derivative `g₂(y,t)`, namely the derivative of the frozen-`y` slice of
`f`. -/
abbrev auxiliaryTimeDerivative (f : E × ℝ → ℝ) (y : E) (t : ℝ) : ℝ :=
  deriv (fun t' : ℝ ↦ f (y, t')) t

section Gradient

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The first auxiliary derivative `g₁(y,t)`, namely the gradient of the frozen-`t` slice of
`f`. -/
abbrev auxiliaryGradient (f : E × ℝ → ℝ) (y : E) (t : ℝ) : E :=
  ∇ (fun y' : E ↦ f (y', t)) y

/-- Definition 5.4.9.7: the auxiliary derivatives of `f(y,t)` are the pair whose first component
is the `y`-gradient and whose second component is the `t`-derivative. -/
abbrev auxiliaryDerivatives (f : E × ℝ → ℝ) (y : E) (t : ℝ) : E × ℝ :=
  (auxiliaryGradient f y t, auxiliaryTimeDerivative f y t)

/-- Expanding `auxiliaryDerivatives f y t` recovers the pair consisting of the frozen-`t`
gradient and the frozen-`y` time derivative. -/
theorem auxiliaryDerivatives_def (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    auxiliaryDerivatives f y t = (auxiliaryGradient f y t, auxiliaryTimeDerivative f y t) :=
  rfl

/-- The first component of `auxiliaryDerivatives f` is `auxiliaryGradient f`. -/
@[simp] theorem auxiliaryDerivatives_fst (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    (auxiliaryDerivatives f y t).1 = auxiliaryGradient f y t :=
  rfl

/-- The second component of `auxiliaryDerivatives f` is `auxiliaryTimeDerivative f`. -/
@[simp] theorem auxiliaryDerivatives_snd (f : E × ℝ → ℝ) (y : E) (t : ℝ) :
    (auxiliaryDerivatives f y t).2 = auxiliaryTimeDerivative f y t :=
  rfl

end Gradient
