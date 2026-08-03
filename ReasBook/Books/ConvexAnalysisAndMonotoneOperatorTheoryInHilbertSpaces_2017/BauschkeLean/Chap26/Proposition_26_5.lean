import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap20.Proposition_20_23
import BauschkeLean.Chap20.Example_20_34
import BauschkeLean.Chap20.Proposition_20_38
import BauschkeLean.Chap25.Corollary_25_5
import BauschkeLean.Chap26.Problem_26_28
import BauschkeLean.Chap26.Problem_26_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u v

namespace SetValuedOperator

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-
Source/core/bridge triage:
- `source-facing`: Proposition 26.5 is the weak graph-limit statement for the coupled composite
  primal-dual system.
- `core/canonical`: the chapter's owner abstraction for the limit pair is
  `composite_kuhn_tucker_points (0 : H) A (0 : K) B L` from Problem 26.30.
- `bridge/view`: the graph conclusions in `gra A` and `gra B`, and the primal/dual solution-set
  memberships from Problem 26.28, are derived consequences of that coupled owner.

Primitive data: graph membership of the sequence terms, weak convergence of `xSeq` and `vSeq`,
strong convergence of the primal residual `L (xSeq n) - ySeq n`, and strong convergence of the
dual residual `uSeq n + L.adjoint (vSeq n)`.
Derived API: the coupled Kuhn--Tucker point membership, then its graph and solution-set
consequences.
-/

-- Semantic recall note: the domain-style sampling pass for this file inspected the Chapter 26
-- owners `composite_primal_inclusion_solution_set` from Problem 26.28 and
-- `composite_kuhn_tucker_points`, `mem_composite_kuhn_tucker_points_iff` from Problem 26.30,
-- together with the later Chapter 26 projection theorem surface in Proposition 26.33. Those
-- declarations make `composite_kuhn_tucker_points` the canonical owner for the coupled limit pair.

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

section

variable {A : SetValuedOperator H H} {B : SetValuedOperator K K}
variable (L : H →L[ℝ] K)
variable {xSeq uSeq : ℕ → H} {ySeq vSeq : ℕ → K} {x : H} {v : K}

local notation "𝓚" => composite_kuhn_tucker_points (0 : H) A (0 : K) B L

/-- Helper for Proposition 26.5: coordinatewise weak convergence in `H` and `K` induces weak
convergence in the canonical `ℓ²` product space on `H × K`. -/
private theorem tendsto_toWeakSpace_product_of_coordinatewise
    {xSeq : ℕ → H} {vSeq : ℕ → K} {x : H} {v : K}
    (hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv :
      Tendsto (fun n ↦ toWeakSpace ℝ K (vSeq n)) atTop (𝓝 (toWeakSpace ℝ K v))) :
    Tendsto (fun n ↦ toWeakSpace ℝ (H × K) (xSeq n, vSeq n)) atTop
      (𝓝 (toWeakSpace ℝ (H × K) (x, v))) := by
  let pairToWeak : WeakSpace ℝ H × WeakSpace ℝ K → WeakSpace ℝ (H × K) :=
    fun z ↦
      toWeakSpace ℝ (H × K)
        (((toWeakSpace ℝ H).symm z.1, (toWeakSpace ℝ K).symm z.2))
  have hpairToWeak : Continuous pairToWeak := by
    rw [continuous_iff_forall_weakDual_apply]
    intro l
    let lfst : StrongDual ℝ H := l ∘L ContinuousLinearMap.inl ℝ H K
    let lsnd : StrongDual ℝ K := l ∘L ContinuousLinearMap.inr ℝ H K
    have hfstEval :
        Continuous fun z : WeakSpace ℝ H × WeakSpace ℝ K ↦
          StrongDual.toWeakDual lfst ((toWeakSpace ℝ H).symm z.1) := by
      have hweakEval :
          Continuous fun z : WeakSpace ℝ H ↦
            StrongDual.toWeakDual lfst ((toWeakSpace ℝ H).symm z) :=
        (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ H ↦ z)).1
          continuous_id (StrongDual.toWeakDual lfst)
      exact hweakEval.comp continuous_fst
    have hsndEval :
        Continuous fun z : WeakSpace ℝ H × WeakSpace ℝ K ↦
          StrongDual.toWeakDual lsnd ((toWeakSpace ℝ K).symm z.2) := by
      have hweakEval :
          Continuous fun z : WeakSpace ℝ K ↦
            StrongDual.toWeakDual lsnd ((toWeakSpace ℝ K).symm z) :=
        (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ K ↦ z)).1
          continuous_id (StrongDual.toWeakDual lsnd)
      exact hweakEval.comp continuous_snd
    -- Split every product functional into its two coordinate evaluations.
    refine (hfstEval.add hsndEval).congr ?_
    intro z
    simpa [pairToWeak, lfst, lsnd, StrongDual.toWeakDual_apply] using
      l.comp_inl_add_comp_inr (((toWeakSpace ℝ H).symm z.1), ((toWeakSpace ℝ K).symm z.2))
  have hprod :
      Tendsto (fun n ↦ (toWeakSpace ℝ H (xSeq n), toWeakSpace ℝ K (vSeq n))) atTop
        (𝓝 (toWeakSpace ℝ H x, toWeakSpace ℝ K v)) :=
    hx.prodMk_nhds hv
  -- Compose the coordinatewise weak limit with the continuous product weak-space bridge.
  simpa [pairToWeak] using
    (hpairToWeak.tendsto (toWeakSpace ℝ H x, toWeakSpace ℝ K v)).comp hprod

/-- Helper for Proposition 26.5: the zero-parameter product operator plus the skew coupling map
is maximally monotone on `H × K`. -/
private theorem compositeKuhnTuckerSumZeroMaximal
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Maximal IsMonotone
      (composite_kuhn_tucker_operator (0 : H) A (0 : K) B +
        (ContinuousLinearMap.skewCouplingMap L).toSetValuedOperator) := by
  let M : SetValuedOperator (H × K) (H × K) := fun p ↦ A p.1 ×ˢ B⁻¹ p.2
  have hprod :
      Maximal IsMonotone (composite_kuhn_tucker_operator (0 : H) A (0 : K) B) := by
    -- At zero parameters, the composite operator is exactly the product `x ↦ A x × B⁻¹ x`.
    have hM : composite_kuhn_tucker_operator (0 : H) A (0 : K) B = M := by
      funext p
      simp [M, composite_kuhn_tucker_operator]
    simpa [hM, M] using
      (SetValuedOperator.Maximal.prod hA (SetValuedOperator.Maximal.inverse hB))
  have hskewMono : (ContinuousLinearMap.skewCouplingMap L).toLinearMap.IsMonotone := by
    intro p
    rcases p with ⟨x, u⟩
    change 0 ≤ ⟪(ContinuousLinearMap.skewCouplingMap L) (x, u), (x, u)⟫_ℝ
    -- The skew quadratic form vanishes by adjoint cancellation.
    have hquad :
        ⟪(ContinuousLinearMap.skewCouplingMap L) (x, u), (x, u)⟫_ℝ = 0 := by
      rw [ContinuousLinearMap.skewCouplingMap_apply]
      calc
        ⟪((L.adjoint) u, -L x), (x, u)⟫_ℝ
            = ⟪(L.adjoint) u, x⟫_ℝ + ⟪-L x, u⟫_ℝ := by
              rfl
        _ = ⟪u, L x⟫_ℝ + -⟪L x, u⟫_ℝ := by
          rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, inner_neg_left]
        _ = 0 := by
          rw [real_inner_comm]
          ring
    rw [hquad]
  have hskew :
      Maximal IsMonotone ((ContinuousLinearMap.skewCouplingMap L).toSetValuedOperator) := by
    -- Example 20.34 upgrades the monotone bounded linear map to a maximally monotone operator.
    exact ContinuousLinearMap.toSetValuedOperator_isMaximallyMonotone_of_isMonotone
      (ContinuousLinearMap.skewCouplingMap L) hskewMono
  have hskewDom :
      ((ContinuousLinearMap.skewCouplingMap L).toSetValuedOperator).dom =
        (Set.univ : Set (H × K)) := by
    -- Singleton-valued operators are defined everywhere.
    ext p
    simp [SetValuedOperator.dom, Function.toSetValuedOperator_apply]
  -- Corollary 25.5 applies through the full-domain branch for the skew linear part.
  exact SetValuedOperator.Maximal.add_of_sumRegularity hprod hskew (Or.inl hskewDom)

/-- Proposition 26.5, canonical owner form: if graph points `(xₙ, uₙ) ∈ gra A` and
`(yₙ, vₙ) ∈ gra B` satisfy `xₙ ⇀ x`, `vₙ ⇀ v`, `L xₙ - yₙ → 0`, and
`uₙ + L^* vₙ → 0`, then the limit pair `(x, v)` is a composite Kuhn--Tucker point. -/
theorem mem_composite_kuhn_tucker_points_of_weak_primal_dual_residual_zero
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A) (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ K (vSeq n)) atTop (𝓝 (toWeakSpace ℝ K v)))
    (hLy : Tendsto (fun n ↦ L (xSeq n) - ySeq n) atTop (𝓝 0))
    (huLv : Tendsto (fun n ↦ uSeq n + L.adjoint (vSeq n)) atTop (𝓝 0)) :
    (x, v) ∈ 𝓚 := by
  let p : ℕ → H × K := fun n ↦ (xSeq n, vSeq n)
  let w : ℕ → H × K := fun n ↦ (uSeq n + L.adjoint (vSeq n), ySeq n - L (xSeq n))
  let T : SetValuedOperator (H × K) (H × K) :=
    composite_kuhn_tucker_operator (0 : H) A (0 : K) B +
      (ContinuousLinearMap.skewCouplingMap L).toSetValuedOperator
  have hTmax : Maximal IsMonotone T := by
    -- Package the operator-side maximality once before using graph closedness.
    simpa [T] using compositeKuhnTuckerSumZeroMaximal (A := A) (B := B) (L := L) hA hB
  have hpweak :
      Tendsto (fun n ↦ toWeakSpace ℝ (H × K) (p n)) atTop
        (𝓝 (toWeakSpace ℝ (H × K) (x, v))) := by
    -- Assemble the coordinatewise weak limits into the product weak limit.
    simpa [p] using
      tendsto_toWeakSpace_product_of_coordinatewise
        (H := H) (K := K) (xSeq := xSeq) (vSeq := vSeq) (x := x) (v := v) hx hv
  have hsecondResidual :
      Tendsto (fun n ↦ ySeq n - L (xSeq n)) atTop (𝓝 (0 : K)) := by
    -- Negating the primal residual puts it in the graph-closure orientation.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hLy.neg
  have hwstrong :
      Tendsto (fun n ↦ w n) atTop (𝓝 (0 : H × K)) := by
    -- Combine the dual and primal residual limits into a product strong limit.
    simpa [w] using huLv.prodMk_nhds hsecondResidual
  have hgraphSeq : ∀ n, (p n, w n) ∈ gra T := by
    intro n
    rw [SetValuedOperator.mem_graph]
    -- Split the graph point into the product-operator component and the skew linear component.
    refine Set.mem_add.2 ?_
    have hprodMem :
        (uSeq n, ySeq n) ∈ composite_kuhn_tucker_operator (0 : H) A (0 : K) B (p n) := by
      simpa [p, composite_kuhn_tucker_operator, SetValuedOperator.mem_graph,
        SetValuedOperator.mem_inverse_iff] using
        (show uSeq n ∈ A (xSeq n) ∧ ySeq n ∈ B⁻¹ (vSeq n) from
          ⟨by simpa [SetValuedOperator.mem_graph] using hxu n,
            by simpa [SetValuedOperator.mem_graph, SetValuedOperator.mem_inverse_iff] using hyv n⟩)
    have hskewMem :
        (L.adjoint (vSeq n), -L (xSeq n)) ∈
          (ContinuousLinearMap.skewCouplingMap L).toSetValuedOperator (p n) := by
      simp [ContinuousLinearMap.toSetValuedOperator, Function.toSetValuedOperator_apply,
        p, ContinuousLinearMap.skewCouplingMap_apply]
    refine ⟨(uSeq n, ySeq n), hprodMem, (L.adjoint (vSeq n), -L (xSeq n)), hskewMem, ?_⟩
    ext <;> simp [w, sub_eq_add_neg]
  have himageSeq :
      ∀ n,
        (toWeakSpace ℝ (H × K) (p n), w n) ∈
          (Prod.map (toWeakSpace ℝ (H × K)) id '' gra T) := by
    intro n
    refine ⟨(p n, w n), hgraphSeq n, rfl⟩
  have himageLimit :
      (toWeakSpace ℝ (H × K) (x, v), (0 : H × K)) ∈
        (Prod.map (toWeakSpace ℝ (H × K)) id '' gra T) := by
    -- Proposition 20.38 closes the limit point in the mixed weak-strong graph topology.
    exact (SetValuedOperator.Maximal.graph_isSeqClosed_weakStrong hTmax)
      himageSeq (hpweak.prodMk_nhds hwstrong)
  rcases himageLimit with ⟨q, hqgraph, hqeq⟩
  have hqfst : q.1 = (x, v) := by
    apply (toWeakSpace ℝ (H × K)).injective
    simpa using congrArg Prod.fst hqeq
  have hqsnd : q.2 = (0 : H × K) := by
    simpa using congrArg Prod.snd hqeq
  have hzeroGraph : ((x, v), (0 : H × K)) ∈ gra T := by
    rw [← hqfst, ← hqsnd]
    exact hqgraph
  have hzero : (0 : H × K) ∈ T (x, v) := by
    simpa [SetValuedOperator.mem_graph] using hzeroGraph
  -- Rewrite the zero membership back to the canonical Kuhn--Tucker owner.
  simpa [T, composite_kuhn_tucker_points, SetValuedOperator.mem_zeros_iff] using hzero

/-- Helper for Proposition 26.5: the canonical Kuhn--Tucker owner theorem rewrites to the
coordinate relations `-L.adjoint v ∈ A x` and `L x ∈ B⁻¹ v`. -/
private theorem weakPrimalDualResidualZero_relations
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A) (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ K (vSeq n)) atTop (𝓝 (toWeakSpace ℝ K v)))
    (hLy : Tendsto (fun n ↦ L (xSeq n) - ySeq n) atTop (𝓝 0))
    (huLv : Tendsto (fun n ↦ uSeq n + L.adjoint (vSeq n)) atTop (𝓝 0)) :
    -L.adjoint v ∈ A x ∧ L x ∈ B⁻¹ v := by
  -- Unpack the canonical owner theorem into the two coordinate relations used downstream.
  simpa using
    (mem_composite_kuhn_tucker_points_iff (0 : H) A (0 : K) B L x v).1
      (mem_composite_kuhn_tucker_points_of_weak_primal_dual_residual_zero
        (L := L) hA hB hxu hyv hx hv hLy huLv)

/-- Helper for Proposition 26.5: under the full coupled hypotheses, the `A`-graph coordinate of
the limit pair belongs to `gra A`. -/
theorem mem_graph_A_of_weak_primal_dual_residual_zero
    (hA : Maximal IsMonotone A)
    (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ K (vSeq n)) atTop (𝓝 (toWeakSpace ℝ K v)))
    (hLy : Tendsto (fun n ↦ L (xSeq n) - ySeq n) atTop (𝓝 0))
    (huLv : Tendsto (fun n ↦ uSeq n + L.adjoint (vSeq n)) atTop (𝓝 0)) :
    (x, -L.adjoint v) ∈ gra A := by
  -- Route correction: derive the graph point from the canonical coupled owner theorem instead of
  -- from a nonexistent standalone weak-product graph-closure statement.
  rw [SetValuedOperator.mem_graph]
  -- Keep only the `A`-coordinate relation from the coupled Kuhn--Tucker limit pair.
  exact
    (weakPrimalDualResidualZero_relations (A := A) (B := B) (L := L)
      hA hB hxu hyv hx hv hLy huLv).1

/-- Helper for Proposition 26.5: under the full coupled hypotheses, the `B`-graph coordinate of
the limit pair belongs to `gra B`. -/
theorem mem_graph_B_of_weak_primal_dual_residual_zero
    (hA : Maximal IsMonotone A)
    (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ K (vSeq n)) atTop (𝓝 (toWeakSpace ℝ K v)))
    (hLy : Tendsto (fun n ↦ L (xSeq n) - ySeq n) atTop (𝓝 0))
    (huLv : Tendsto (fun n ↦ uSeq n + L.adjoint (vSeq n)) atTop (𝓝 0)) :
    (L x, v) ∈ gra B := by
  have hBinv : L x ∈ B⁻¹ v := by
    -- Route correction: reuse the coupled owner theorem and extract the `B⁻¹` coordinate.
    exact
      (weakPrimalDualResidualZero_relations (A := A) (B := B) (L := L)
        hA hB hxu hyv hx hv hLy huLv).2
  -- Convert the inverse-graph relation back to ordinary graph membership.
  simpa [SetValuedOperator.mem_graph] using
    (SetValuedOperator.mem_inverse_iff B v (L x)).1 hBinv

/-- Proposition 26.5 (3): under the coupled hypotheses, the primal limit belongs to the
source-facing composite primal inclusion solution set from Problem 26.28. -/
theorem mem_composite_primal_inclusion_solution_set_of_weak_primal_dual_residual_zero
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A) (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ K (vSeq n)) atTop (𝓝 (toWeakSpace ℝ K v)))
    (hLy : Tendsto (fun n ↦ L (xSeq n) - ySeq n) atTop (𝓝 0))
    (huLv : Tendsto (fun n ↦ uSeq n + L.adjoint (vSeq n)) atTop (𝓝 0)) :
    x ∈ composite_primal_inclusion_solution_set (0 : H) A (0 : K) B L := by
  have hkt :
      -L.adjoint v ∈ A x ∧ L x ∈ B⁻¹ v := by
    -- First recover the coupled Kuhn--Tucker relations from the main owner theorem.
    simpa using
      (mem_composite_kuhn_tucker_points_iff (0 : H) A (0 : K) B L x v).1
        (mem_composite_kuhn_tucker_points_of_weak_primal_dual_residual_zero
          (L := L) hA hB hxu hyv hx hv hLy huLv)
  have hBmem : v ∈ B (L x) := by
    exact (SetValuedOperator.mem_inverse_iff B v (L x)).1 hkt.2
  have hprimal : (0 : H) ∈ A x + L.adjoint '' B (L x) := by
    -- Use the limit dual variable as the explicit witness in the primal inclusion sum.
    refine Set.mem_add.2 ?_
    refine ⟨-L.adjoint v, hkt.1, L.adjoint v, ?_, ?_⟩
    · exact ⟨v, hBmem, rfl⟩
    · abel
  rw [mem_composite_primal_inclusion_solution_set]
  -- Use the limit dual variable as the explicit witness in the primal inclusion sum.
  simpa using hprimal

/-- Proposition 26.5 (4): under the coupled hypotheses, the dual limit belongs to the
source-facing composite dual inclusion solution set from Problem 26.28. -/
theorem mem_composite_dual_inclusion_solution_set_of_weak_primal_dual_residual_zero
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A) (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ K (vSeq n)) atTop (𝓝 (toWeakSpace ℝ K v)))
    (hLy : Tendsto (fun n ↦ L (xSeq n) - ySeq n) atTop (𝓝 0))
    (huLv : Tendsto (fun n ↦ uSeq n + L.adjoint (vSeq n)) atTop (𝓝 0)) :
    v ∈ composite_dual_inclusion_solution_set (0 : H) A (0 : K) B L := by
  have hkt :
      -L.adjoint v ∈ A x ∧ L x ∈ B⁻¹ v := by
    -- First recover the coupled Kuhn--Tucker relations from the main owner theorem.
    simpa using
      (mem_composite_kuhn_tucker_points_iff (0 : H) A (0 : K) B L x v).1
        (mem_composite_kuhn_tucker_points_of_weak_primal_dual_residual_zero
          (L := L) hA hB hxu hyv hx hv hLy huLv)
  have hAinv : x ∈ A⁻¹ (-L.adjoint v) := by
    exact (SetValuedOperator.mem_inverse_iff A (-L.adjoint v) x).2 hkt.1
  have hdual : (0 : K) ∈ ((-L) '' (A⁻¹ (-L.adjoint v))) + (B⁻¹ v) := by
    -- Use the limit primal point as the explicit witness in the dual inclusion sum.
    refine Set.mem_add.2 ?_
    refine ⟨-L x, ?_, L x, hkt.2, ?_⟩
    · refine ⟨x, hAinv, rfl⟩
    · abel
  rw [mem_composite_dual_inclusion_solution_set]
  -- Use the limit primal point as the explicit witness in the dual inclusion sum.
  simpa using hdual

end

end SetValuedOperator
