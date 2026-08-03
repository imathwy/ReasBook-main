import BauschkeLean.Chap26.Problem_26_28
import BauschkeLean.Chap26.Proposition_26_32
import BauschkeLean.Chap26.Proposition_26_33
import BauschkeLean.Chap26.Theorem_26_17
import BauschkeLean.Chap20.Example_20_15
import BauschkeLean.Chap20.Example_20_16

open Filter
open scoped InnerProductSpace Pointwise SetValuedOperator Topology
open ERealFunction
open SetValuedOperator
open ContinuousLinearMap

universe u v

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

noncomputable section

namespace SetValuedOperator

-- Semantic recall/local owner choice:
-- `lean_leansearch` surfaced only generic product-filter convergence lemmas, so this file uses
-- the verified Chapter 26 owners `composite_kuhn_tucker_operator`,
-- `resolvent_composite_kuhn_tucker_operator_eq`, `composite_kuhn_tucker_points`, and the
-- product-space skew owner `skewCouplingMap`.
--
-- Source/core/bridge triage:
-- - `source-facing`: Theorem 26.34 is the composite forward-backward-forward recursion `(26.98)`
--   and its residual/weak-convergence consequences.
-- - `core/canonical`: the product-space Tseng data are the operator
--   `composite_kuhn_tucker_operator z A r B`, the skew map `skewCouplingMap L`, the Chapter 23
--   resolvent surface `J[...]`, and the Kuhn--Tucker set
--   `composite_kuhn_tucker_points z A r B L`.
-- - `bridge/view`: the source coordinates `x_n`, `v_n`, `y_{1,n}`, `y_{2,n}`, `p_{1,n}`,
--   `p_{2,n}`, `q_{1,n}`, and `q_{2,n}` are derived from the recursive product-space orbit, using
--   an explicit single-valued realizer `JγM : H × K → H × K` of
--   `J[((γ : ℝ) • composite_kuhn_tucker_operator z A r B)]`, rather than stored as primitive
--   compatibility data.

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

section CompositeForwardBackwardForwardAlgorithm

/-- The product-space forward-backward-forward orbit from `(26.98)`, started at `(x₀, v₀)` and
updated with the product-space skew map `skewCouplingMap L` and the canonical resolvent map of
`composite_kuhn_tucker_operator z A r B`. -/
def compositeForwardBackwardForwardIteration
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H × K
  | 0 => (x0, v0)
  | n + 1 =>
      let w := compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n
      let y := w - (γ : ℝ) • skewCouplingMap L w
      let p := JγM y
      let q := p - (γ : ℝ) • skewCouplingMap L p
      w - y + q

/-- The predictor sequence `(y_{1,n}, y_{2,n})` attached to the composite forward-backward-
forward orbit. -/
def compositeForwardBackwardForwardPredictorSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H × K :=
  fun n ↦
    let w := compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n
    w - (γ : ℝ) • skewCouplingMap L w

/-- The resolvent sequence `(p_{1,n}, p_{2,n})` attached to `(26.98)`, realized by the canonical
resolvent map of `composite_kuhn_tucker_operator z A r B`. -/
def compositeForwardBackwardForwardResolventSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H × K :=
  fun n ↦
    JγM (compositeForwardBackwardForwardPredictorSequence z A r B L γ JγM x0 v0 n)

/-- The correction sequence `(q_{1,n}, q_{2,n})` attached to `(26.98)`. -/
def compositeForwardBackwardForwardCorrectionSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H × K :=
  fun n ↦
    let p := compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n
    p - (γ : ℝ) • skewCouplingMap L p

/-- The primal orbit `xₙ` from `(26.98)`. -/
def compositeForwardBackwardForwardPrimalIteration
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H :=
  fun n ↦ (compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n).1

/-- The dual orbit `vₙ` from `(26.98)`. -/
def compositeForwardBackwardForwardDualIteration
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → K :=
  fun n ↦ (compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n).2

/-- The primal predictor sequence `y_{1,n}` from `(26.98)`. -/
def compositeForwardBackwardForwardPrimalPredictorSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H :=
  fun n ↦ (compositeForwardBackwardForwardPredictorSequence z A r B L γ JγM x0 v0 n).1

/-- The dual predictor sequence `y_{2,n}` from `(26.98)`. -/
def compositeForwardBackwardForwardDualPredictorSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → K :=
  fun n ↦ (compositeForwardBackwardForwardPredictorSequence z A r B L γ JγM x0 v0 n).2

/-- The primal resolvent sequence `p_{1,n}` from `(26.98)`. -/
def compositeForwardBackwardForwardPrimalResolventSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H :=
  fun n ↦ (compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n).1

/-- The dual resolvent sequence `p_{2,n}` from `(26.98)`. -/
def compositeForwardBackwardForwardDualResolventSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → K :=
  fun n ↦ (compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n).2

/-- The primal correction sequence `q_{1,n}` from `(26.98)`. -/
def compositeForwardBackwardForwardPrimalCorrectionSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → H :=
  fun n ↦ (compositeForwardBackwardForwardCorrectionSequence z A r B L γ JγM x0 v0 n).1

/-- The dual correction sequence `q_{2,n}` from `(26.98)`. -/
def compositeForwardBackwardForwardDualCorrectionSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) : ℕ → K :=
  fun n ↦ (compositeForwardBackwardForwardCorrectionSequence z A r B L γ JγM x0 v0 n).2

@[simp] theorem compositeForwardBackwardForwardIteration_zero
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) :
    compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 0 = (x0, v0) := rfl

@[simp] theorem compositeForwardBackwardForwardIteration_succ
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) (n : ℕ) :
    compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 (n + 1) =
      let w := compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n
      let y := w - (γ : ℝ) • skewCouplingMap L w
      let p := JγM y
      let q := p - (γ : ℝ) • skewCouplingMap L p
      w - y + q := rfl

@[simp] theorem compositeForwardBackwardForwardPredictorSequence_apply
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) (n : ℕ) :
    compositeForwardBackwardForwardPredictorSequence z A r B L γ JγM x0 v0 n =
      let w := compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n
      w - (γ : ℝ) • skewCouplingMap L w := rfl

@[simp] theorem compositeForwardBackwardForwardResolventSequence_apply
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) (n : ℕ) :
    compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n =
      JγM (compositeForwardBackwardForwardPredictorSequence z A r B L γ JγM x0 v0 n) := rfl

@[simp] theorem compositeForwardBackwardForwardCorrectionSequence_apply
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) (n : ℕ) :
    compositeForwardBackwardForwardCorrectionSequence z A r B L γ JγM x0 v0 n =
      let p := compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n
      p - (γ : ℝ) • skewCouplingMap L p := rfl

end CompositeForwardBackwardForwardAlgorithm

/-- Helper for Theorem 26.34: the ambient product space `H × K` is Chebyshev over `Set.univ`, so
the unconstrained product-space Tseng recursion can be expressed through the canonical projector
surface. -/
private theorem isChebyshev_univ_product :
    IsChebyshev (Set.univ : Set (H × K)) :=
  isChebyshev_of_nonempty_isClosed_convex ⟨(0, 0), Set.mem_univ _⟩ isClosed_univ convex_univ

/-- Helper for Theorem 26.34: the metric projector onto the whole product space is the identity.
-/
private theorem projectionPoint_univ_eq_self_product (x : H × K) :
    P[Set.univ, isChebyshev_univ_product] x = x := by
  symm
  refine
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      ⟨(0, 0), Set.mem_univ _⟩ isClosed_univ convex_univ).2 ?_
  refine ⟨by simp, ?_⟩
  intro y hy
  simp

/-- Helper for Theorem 26.34: the recursive product-space orbit `(26.98)` is the unconstrained
Tseng orbit for the product operator `composite_kuhn_tucker_operator z A r B` and the skew map
`skewCouplingMap L`. -/
theorem compositeForwardBackwardForwardIteration_eq_projectedForwardBackwardForwardIteration
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) :
    compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 =
      projectedForwardBackwardForwardIteration
        JγM (skewCouplingMap L) (Set.univ : Set (H × K)) isChebyshev_univ_product γ
        ⟨(x0, v0), Set.mem_univ _⟩ := by
  funext n
  induction n with
  | zero =>
      simp [compositeForwardBackwardForwardIteration, projectedForwardBackwardForwardIteration]
  | succ n ihn =>
      simp [compositeForwardBackwardForwardIteration_succ, projectedForwardBackwardForwardIteration,
        ihn, projectionPoint_univ_eq_self_product, sub_eq_add_neg]

/-- Helper for Theorem 26.34: the product-space resolvent sequence from `(26.98)` is the
unconstrained product-space Tseng resolvent sequence. -/
theorem
    compositeForwardBackwardForwardResolventSequence_eq_projectedForwardBackwardForwardResolventSequence
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (γ : PosReal) (JγM : H × K → H × K) (x0 : H) (v0 : K) :
    compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 =
      projectedForwardBackwardForwardResolventSequence
        JγM (skewCouplingMap L) (Set.univ : Set (H × K)) isChebyshev_univ_product γ
        ⟨(x0, v0), Set.mem_univ _⟩ := by
  funext n
  simp [compositeForwardBackwardForwardResolventSequence,
    projectedForwardBackwardForwardResolventSequence,
    compositeForwardBackwardForwardPredictorSequence,
    projectedForwardBackwardForwardPredictorSequence,
    compositeForwardBackwardForwardIteration_eq_projectedForwardBackwardForwardIteration]

/-- Helper for Theorem 26.34: the first-coordinate map is continuous from the weak topology on
`H × K` to the weak topology on `H`. -/
theorem weakSpace_continuous_fst_product :
    Continuous fun z : WeakSpace ℝ (H × K) ↦
      toWeakSpace ℝ H (((toWeakSpace ℝ (H × K)).symm z).1) := by
  rw [continuous_iff_forall_weakDual_apply]
  intro l
  let lfst : StrongDual ℝ (H × K) := l ∘L ContinuousLinearMap.fst ℝ H K
  have hcont_id : Continuous (fun z : WeakSpace ℝ (H × K) ↦ z) := continuous_id
  have hlfst :
      Continuous fun z : WeakSpace ℝ (H × K) ↦
        StrongDual.toWeakDual lfst ((toWeakSpace ℝ (H × K)).symm z) :=
    (continuous_iff_forall_weakDual_apply).1 hcont_id (StrongDual.toWeakDual lfst)
  refine hlfst.congr ?_
  intro z
  rfl

/-- Helper for Theorem 26.34: the second-coordinate map is continuous from the weak topology on
`H × K` to the weak topology on `K`. -/
theorem weakSpace_continuous_snd_product :
    Continuous fun z : WeakSpace ℝ (H × K) ↦
      toWeakSpace ℝ K (((toWeakSpace ℝ (H × K)).symm z).2) := by
  rw [continuous_iff_forall_weakDual_apply]
  intro l
  let lsnd : StrongDual ℝ (H × K) := l ∘L ContinuousLinearMap.snd ℝ H K
  have hcont_id : Continuous (fun z : WeakSpace ℝ (H × K) ↦ z) := continuous_id
  have hlsnd :
      Continuous fun z : WeakSpace ℝ (H × K) ↦
        StrongDual.toWeakDual lsnd ((toWeakSpace ℝ (H × K)).symm z) :=
    (continuous_iff_forall_weakDual_apply).1 hcont_id (StrongDual.toWeakDual lsnd)
  refine hlsnd.congr ?_
  intro z
  rfl

/-- Helper for Theorem 26.34: weak convergence in the product space implies weak convergence of
the first coordinate. -/
theorem tendsto_toWeakSpace_fst_of_tendsto_toWeakSpace_product
    {u : ℕ → H × K} {p : H × K}
    (hu :
      Tendsto (fun n ↦ toWeakSpace ℝ (H × K) (u n)) atTop
        (𝓝 (toWeakSpace ℝ (H × K) p))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (u n).1) atTop (𝓝 (toWeakSpace ℝ H p.1)) := by
  simpa using
    (weakSpace_continuous_fst_product.tendsto (toWeakSpace ℝ (H × K) p)).comp hu

/-- Helper for Theorem 26.34: weak convergence in the product space implies weak convergence of
the second coordinate. -/
theorem tendsto_toWeakSpace_snd_of_tendsto_toWeakSpace_product
    {u : ℕ → H × K} {p : H × K}
    (hu :
      Tendsto (fun n ↦ toWeakSpace ℝ (H × K) (u n)) atTop
        (𝓝 (toWeakSpace ℝ (H × K) p))) :
    Tendsto (fun n ↦ toWeakSpace ℝ K (u n).2) atTop (𝓝 (toWeakSpace ℝ K p.2)) := by
  simpa using
    (weakSpace_continuous_snd_product.tendsto (toWeakSpace ℝ (H × K) p)).comp hu

/-- Helper for Theorem 26.34: the generic unconstrained Tseng residual theorem specializes to
the canonical product-space orbit `(26.98)`. -/
private theorem compositeForwardBackwardForward_productResidual_tendsto_zero
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K)
    (hA_max : Maximal IsMonotone A) (hB_max : Maximal IsMonotone B)
    (hz : z ∈ SetValuedOperator.range (A + L.adjointImage (B.translate r)))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (1 : ℝ) / ‖L‖)
    (JγM : H × K → H × K)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r B)])
    (x0 : H) (v0 : K) :
    Tendsto
      (fun n ↦
        compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n -
          compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n)
      atTop (𝓝 (0 : H × K)) := by
  let M : SetValuedOperator (H × K) (H × K) := composite_kuhn_tucker_operator z A r B
  let S : SetValuedOperator (H × K) (H × K) := (skewCouplingMap L).toSetValuedOperator
  have hnorm_ne : ‖L‖ ≠ 0 := by
    intro hL
    have hγ_pos : 0 < (γ : ℝ) := γ.2
    have : ¬ (γ : ℝ) < 0 := not_lt_of_ge hγ_pos.le
    exact this (by simpa [hL] using hγ_lt)
  have hnorm_pos : 0 < ‖L‖ := lt_of_le_of_ne (norm_nonneg _) hnorm_ne.symm
  let β : PosReal := ⟨‖L‖⁻¹, inv_pos.mpr hnorm_pos⟩
  have hM_max : Maximal IsMonotone M := by
    simpa [M] using composite_kuhn_tucker_operator_maximal z A r B hA_max hB_max
  have hM_dom : M.dom ⊆ (Set.univ : Set (H × K)) := by
    intro x hx
    simp
  have hS_mono : S.IsMonotone := by
    have hlin_mono : (skewCouplingMap L).toLinearMap.IsMonotone := by
      exact isMonotone_of_adjoint_eq_neg (skewCouplingMap L) (skewCouplingMap_adjoint_eq_neg L)
    exact (LinearMap.toSetValuedOperator_isMonotone_iff (skewCouplingMap L).toLinearMap).2
      hlin_mono
  have hS_eq :
      ∀ x ∈ (Set.univ : Set (H × K)),
        S x = Function.toSetValuedOperatorOn (skewCouplingMap L) Set.univ x := by
    intro x hx
    simp [S, Function.toSetValuedOperatorOn]
  have hP_nonempty : (composite_primal_inclusion_solution_set z A r B L).Nonempty := by
    rcases (mem_range_iff (A + L.adjointImage (B.translate r)) z).1 hz with ⟨x, hx⟩
    exact ⟨x, by simpa [composite_primal_inclusion_solution_set] using hx⟩
  have hK_nonempty : (composite_kuhn_tucker_points z A r B L).Nonempty := by
    rcases hP_nonempty with ⟨x, hx⟩
    exact
      ((composite_primal_nonempty_iff_composite_kuhn_tucker_points_nonempty z A r B L).mp
        ⟨x, hx⟩)
  have hT_max : Maximal IsMonotone (M + S) := by
    simpa [M, S] using
      composite_kuhn_tucker_operator_add_skewCouplingMap_maximal z A r B L hA_max hB_max
  have hT_zero_nonempty :
      ((Set.univ : Set (H × K)) ∩ (M + S).zeros).Nonempty := by
    rcases hK_nonempty with ⟨p, hp⟩
    exact ⟨p, ⟨Set.mem_univ _, by simpa [M, S, composite_kuhn_tucker_points] using hp⟩⟩
  have hS_lipschitz :
      @LipschitzOnWith (H × K) (H × K)
        (@EMetricSpace.toPseudoEMetricSpace (H × K)
          (@MetricSpace.toEMetricSpace (H × K) prod_normedAddCommGroup_l2.toMetricSpace))
        (@EMetricSpace.toPseudoEMetricSpace (H × K)
          (@MetricSpace.toEMetricSpace (H × K) prod_normedAddCommGroup_l2.toMetricSpace))
        (Real.toNNReal ((β : ℝ)⁻¹)) (skewCouplingMap L) ((Set.univ : Set (H × K)) ∪ M.dom) := by
    exact LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
      simpa [β, dist_eq_norm, map_sub, Real.toNNReal_of_nonneg (norm_nonneg _)] using
        calc
          ‖skewCouplingMap L (x - y)‖ ≤ ‖skewCouplingMap L‖ * ‖x - y‖ := by
            exact (skewCouplingMap L).le_opNorm (x - y)
          _ = ‖L‖ * ‖x - y‖ := by rw [norm_skewCouplingMap]
  have hγ_ltβ : (γ : ℝ) < (β : ℝ) := by
    simpa [β, one_div] using hγ_lt
  have htseng :
      Tendsto
        (fun n ↦
          projectedForwardBackwardForwardIteration
              JγM (skewCouplingMap L) (Set.univ : Set (H × K)) isChebyshev_univ_product γ
              ⟨(x0, v0), Set.mem_univ _⟩ n -
            projectedForwardBackwardForwardResolventSequence
              JγM (skewCouplingMap L) (Set.univ : Set (H × K)) isChebyshev_univ_product γ
              ⟨(x0, v0), Set.mem_univ _⟩ n)
        atTop (𝓝 (0 : H × K)) :=
    tsengAlgorithm_sub_tendsto_zero hM_max hM_dom hS_mono hS_eq β hT_max isClosed_univ
      convex_univ (by intro x hx; exact hx) hT_zero_nonempty hS_lipschitz γ hγ_ltβ JγM hJγM
      ⟨(x0, v0), Set.mem_univ _⟩
  simpa [compositeForwardBackwardForwardIteration_eq_projectedForwardBackwardForwardIteration,
    compositeForwardBackwardForwardResolventSequence_eq_projectedForwardBackwardForwardResolventSequence
  ]
    using htseng

/-- Helper for Theorem 26.34: the generic unconstrained Tseng weak-convergence theorem
specializes to the canonical product-space orbit `(26.98)`. -/
private theorem compositeForwardBackwardForward_tendsto_weakly_to_kuhnTuckerPoint
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K)
    (hA_max : Maximal IsMonotone A) (hB_max : Maximal IsMonotone B)
    (hz : z ∈ SetValuedOperator.range (A + L.adjointImage (B.translate r)))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (1 : ℝ) / ‖L‖)
    (JγM : H × K → H × K)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r B)])
    (x0 : H) (v0 : K) :
    ∃ p ∈ composite_kuhn_tucker_points z A r B L,
      Tendsto
        (fun n ↦
          toWeakSpace ℝ (H × K)
            (compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n))
        atTop (𝓝 (toWeakSpace ℝ (H × K) p)) := by
  let M : SetValuedOperator (H × K) (H × K) := composite_kuhn_tucker_operator z A r B
  let S : SetValuedOperator (H × K) (H × K) := (skewCouplingMap L).toSetValuedOperator
  have hnorm_ne : ‖L‖ ≠ 0 := by
    intro hL
    have hγ_pos : 0 < (γ : ℝ) := γ.2
    have : ¬ (γ : ℝ) < 0 := not_lt_of_ge hγ_pos.le
    exact this (by simpa [hL] using hγ_lt)
  have hnorm_pos : 0 < ‖L‖ := lt_of_le_of_ne (norm_nonneg _) hnorm_ne.symm
  let β : PosReal := ⟨‖L‖⁻¹, inv_pos.mpr hnorm_pos⟩
  have hM_max : Maximal IsMonotone M := by
    simpa [M] using composite_kuhn_tucker_operator_maximal z A r B hA_max hB_max
  have hM_dom : M.dom ⊆ (Set.univ : Set (H × K)) := by
    intro x hx
    simp
  have hS_mono : S.IsMonotone := by
    have hlin_mono : (skewCouplingMap L).toLinearMap.IsMonotone := by
      exact isMonotone_of_adjoint_eq_neg (skewCouplingMap L) (skewCouplingMap_adjoint_eq_neg L)
    exact (LinearMap.toSetValuedOperator_isMonotone_iff (skewCouplingMap L).toLinearMap).2
      hlin_mono
  have hS_eq :
      ∀ x ∈ (Set.univ : Set (H × K)),
        S x = Function.toSetValuedOperatorOn (skewCouplingMap L) Set.univ x := by
    intro x hx
    simp [S, Function.toSetValuedOperatorOn]
  have hP_nonempty : (composite_primal_inclusion_solution_set z A r B L).Nonempty := by
    rcases (mem_range_iff (A + L.adjointImage (B.translate r)) z).1 hz with ⟨x, hx⟩
    exact ⟨x, by simpa [composite_primal_inclusion_solution_set] using hx⟩
  have hK_nonempty : (composite_kuhn_tucker_points z A r B L).Nonempty := by
    rcases hP_nonempty with ⟨x, hx⟩
    exact
      ((composite_primal_nonempty_iff_composite_kuhn_tucker_points_nonempty z A r B L).mp
        ⟨x, hx⟩)
  have hT_max : Maximal IsMonotone (M + S) := by
    simpa [M, S] using
      composite_kuhn_tucker_operator_add_skewCouplingMap_maximal z A r B L hA_max hB_max
  have hT_zero_nonempty :
      ((Set.univ : Set (H × K)) ∩ (M + S).zeros).Nonempty := by
    rcases hK_nonempty with ⟨p, hp⟩
    exact ⟨p, ⟨Set.mem_univ _, by simpa [M, S, composite_kuhn_tucker_points] using hp⟩⟩
  have hS_lipschitz :
      @LipschitzOnWith (H × K) (H × K)
        (@EMetricSpace.toPseudoEMetricSpace (H × K)
          (@MetricSpace.toEMetricSpace (H × K) prod_normedAddCommGroup_l2.toMetricSpace))
        (@EMetricSpace.toPseudoEMetricSpace (H × K)
          (@MetricSpace.toEMetricSpace (H × K) prod_normedAddCommGroup_l2.toMetricSpace))
        (Real.toNNReal ((β : ℝ)⁻¹)) (skewCouplingMap L) ((Set.univ : Set (H × K)) ∪ M.dom) := by
    exact LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
      simpa [β, dist_eq_norm, map_sub, Real.toNNReal_of_nonneg (norm_nonneg _)] using
        calc
          ‖skewCouplingMap L (x - y)‖ ≤ ‖skewCouplingMap L‖ * ‖x - y‖ := by
            exact (skewCouplingMap L).le_opNorm (x - y)
          _ = ‖L‖ * ‖x - y‖ := by rw [norm_skewCouplingMap]
  have hγ_ltβ : (γ : ℝ) < (β : ℝ) := by
    simpa [β, one_div] using hγ_lt
  have htseng :
      ∃ p ∈ (Set.univ : Set (H × K)) ∩ (M + S).zeros,
        Tendsto
          (fun n ↦
            toWeakSpace ℝ (H × K)
              (projectedForwardBackwardForwardIteration
                JγM (skewCouplingMap L) (Set.univ : Set (H × K))
                isChebyshev_univ_product γ ⟨(x0, v0), Set.mem_univ _⟩ n))
          atTop (𝓝 (toWeakSpace ℝ (H × K) p)) ∧
          Tendsto
            (fun n ↦
              toWeakSpace ℝ (H × K)
              (projectedForwardBackwardForwardResolventSequence
                  JγM (skewCouplingMap L) (Set.univ : Set (H × K))
                  isChebyshev_univ_product γ ⟨(x0, v0), Set.mem_univ _⟩ n))
            atTop (𝓝 (toWeakSpace ℝ (H × K) p)) := by
    exact
      tsengAlgorithm_tendsto_weakly hM_max hM_dom hS_mono hS_eq β hT_max isClosed_univ
        convex_univ (by intro x hx; exact hx) hT_zero_nonempty hS_lipschitz γ hγ_ltβ JγM
        hJγM ⟨(x0, v0), Set.mem_univ _⟩
  rcases htseng
    with ⟨p, hp, hpweak, _⟩
  refine ⟨p, ?_, ?_⟩
  · simpa [M, S, composite_kuhn_tucker_points] using hp.2
  · simpa [compositeForwardBackwardForwardIteration_eq_projectedForwardBackwardForwardIteration]
      using hpweak

/-- Theorem 26.34 (1): under the composite inclusion assumptions and the recursion `(26.98)`,
the primal residuals `x_n - p_{1,n}` converge strongly to `0`. -/
theorem compositeForwardBackwardForward_primalResidual_tendsto_zero
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K)
    (hA_max : Maximal IsMonotone A) (hB_max : Maximal IsMonotone B)
    (hz : z ∈ SetValuedOperator.range (A + L.adjointImage (B.translate r)))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (1 : ℝ) / ‖L‖)
    (JγM : H × K → H × K)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r B)])
    (x0 : H) (v0 : K) :
    Tendsto
      (fun n ↦
        compositeForwardBackwardForwardPrimalIteration z A r B L γ JγM x0 v0 n -
          compositeForwardBackwardForwardPrimalResolventSequence z A r B L γ JγM x0 v0 n)
      atTop (𝓝 (0 : H)) := by
  have hprod :=
    compositeForwardBackwardForward_productResidual_tendsto_zero
      z A r B L hA_max hB_max hz γ hγ_lt JγM hJγM x0 v0
  have hfst :
      Tendsto
        (fun n ↦
          (compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n -
            compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n).1)
        atTop (𝓝 (0 : H)) := by
    simpa using (continuous_fst.tendsto (0 : H × K)).comp hprod
  simpa [compositeForwardBackwardForwardPrimalIteration,
    compositeForwardBackwardForwardPrimalResolventSequence] using hfst

/-- Theorem 26.34 (2): under the composite inclusion assumptions and the recursion `(26.98)`,
the dual residuals `v_n - p_{2,n}` converge strongly to `0`. -/
theorem compositeForwardBackwardForward_dualResidual_tendsto_zero
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K)
    (hA_max : Maximal IsMonotone A) (hB_max : Maximal IsMonotone B)
    (hz : z ∈ SetValuedOperator.range (A + L.adjointImage (B.translate r)))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (1 : ℝ) / ‖L‖)
    (JγM : H × K → H × K)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r B)])
    (x0 : H) (v0 : K) :
    Tendsto
      (fun n ↦
        compositeForwardBackwardForwardDualIteration z A r B L γ JγM x0 v0 n -
          compositeForwardBackwardForwardDualResolventSequence z A r B L γ JγM x0 v0 n)
      atTop (𝓝 (0 : K)) := by
  have hprod :=
    compositeForwardBackwardForward_productResidual_tendsto_zero
      z A r B L hA_max hB_max hz γ hγ_lt JγM hJγM x0 v0
  have hsnd :
      Tendsto
        (fun n ↦
          (compositeForwardBackwardForwardIteration z A r B L γ JγM x0 v0 n -
            compositeForwardBackwardForwardResolventSequence z A r B L γ JγM x0 v0 n).2)
        atTop (𝓝 (0 : K)) := by
    simpa using (continuous_snd.tendsto (0 : H × K)).comp hprod
  simpa [compositeForwardBackwardForwardDualIteration,
    compositeForwardBackwardForwardDualResolventSequence] using hsnd

/-- Theorem 26.34 (3): under the assumptions of `(26.97)` and the recursion `(26.98)`, there is
a Kuhn--Tucker pair `(x̄, v̄) ∈ composite_kuhn_tucker_points z A r B L`, and the source iterates
`x_n` and `v_n` converge weakly to `x̄` and `v̄`. -/
theorem compositeForwardBackwardForward_tendsto_weakly_to_kuhnTuckerPair
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K)
    (hA_max : Maximal IsMonotone A) (hB_max : Maximal IsMonotone B)
    (hz : z ∈ SetValuedOperator.range (A + L.adjointImage (B.translate r)))
    (γ : PosReal) (hγ_lt : (γ : ℝ) < (1 : ℝ) / ‖L‖)
    (JγM : H × K → H × K)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r B)])
    (x0 : H) (v0 : K) :
    ∃ xbar : H, ∃ vbar : K,
      (xbar, vbar) ∈ composite_kuhn_tucker_points z A r B L ∧
        Tendsto
          (fun n ↦
            toWeakSpace ℝ H
              (compositeForwardBackwardForwardPrimalIteration z A r B L γ JγM x0 v0 n))
          atTop (𝓝 (toWeakSpace ℝ H xbar)) ∧
        Tendsto
          (fun n ↦
            toWeakSpace ℝ K
              (compositeForwardBackwardForwardDualIteration z A r B L γ JγM x0 v0 n))
          atTop (𝓝 (toWeakSpace ℝ K vbar)) := by
  rcases
      compositeForwardBackwardForward_tendsto_weakly_to_kuhnTuckerPoint
        z A r B L hA_max hB_max hz γ hγ_lt JγM hJγM x0 v0
    with ⟨p, hp, hpweak⟩
  refine ⟨p.1, p.2, hp, ?_, ?_⟩
  · simpa [compositeForwardBackwardForwardPrimalIteration] using
      tendsto_toWeakSpace_fst_of_tendsto_toWeakSpace_product hpweak
  · simpa [compositeForwardBackwardForwardDualIteration] using
      tendsto_toWeakSpace_snd_of_tendsto_toWeakSpace_product hpweak

end SetValuedOperator
