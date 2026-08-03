import BauschkeLean.Chap26.Proposition_26_5
import BauschkeLean.Chap26.Text_26_0_1

-- Semantic recall note: the domain-style sampling pass for this corollary inspected the Chapter
-- 26 owners `composite_kuhn_tucker_points`, `composite_primal_inclusion_solution_set`,
-- `composite_dual_inclusion_solution_set`, and Proposition 26.5. The owner abstraction is the
-- coupled composite statement from Proposition 26.5; this file keeps only the source-facing
-- `L = Id` specialization.

open Filter
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section

variable {A B : SetValuedOperator H H}
variable {xSeq uSeq ySeq vSeq : ℕ → H} {x u : H}

/-- Corollary 26.6 (1): if `A` and `B` are maximally monotone, `(xₙ, uₙ) ∈ gra A`,
`(yₙ, vₙ) ∈ gra B`, `xₙ ⇀ x`, `vₙ ⇀ u`, `xₙ - yₙ → 0`, and `uₙ + vₙ → 0`, then
`x ∈ zer (A + B)`, formalized as `x ∈ primal_inclusion_solution_set A B`. -/
theorem mem_primal_inclusion_solution_set_of_weak_graph_residual_zero
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A) (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ H (vSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hxy : Tendsto (fun n ↦ xSeq n - ySeq n) atTop (𝓝 (0 : H)))
    (huv : Tendsto (fun n ↦ uSeq n + vSeq n) atTop (𝓝 (0 : H))) :
    x ∈ primal_inclusion_solution_set A B := by
  have huv' :
      Tendsto
        (fun n ↦ uSeq n + (ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ H)) (vSeq n))
        atTop (𝓝 (0 : H)) := by
    simpa [ContinuousLinearMap.adjoint_id] using huv
  simpa [primal_inclusion_solution_set, composite_primal_inclusion_solution_set,
    ContinuousLinearMap.adjointImage, ContinuousLinearMap.adjoint_id] using
    mem_composite_primal_inclusion_solution_set_of_weak_primal_dual_residual_zero
      (ContinuousLinearMap.id ℝ H) hA hB hxu hyv hx hv hxy huv'

/-- Corollary 26.6 (2): under the hypotheses of Corollary 26.6, the weak limit `u` belongs to
`zer (-A⁻¹ ∘ (-Id) + B⁻¹)`, formalized as `u ∈ dual_inclusion_solution_set A B`. -/
theorem mem_dual_inclusion_solution_set_of_weak_graph_residual_zero
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A) (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ H (vSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hxy : Tendsto (fun n ↦ xSeq n - ySeq n) atTop (𝓝 (0 : H)))
    (huv : Tendsto (fun n ↦ uSeq n + vSeq n) atTop (𝓝 (0 : H))) :
    u ∈ dual_inclusion_solution_set A B := by
  have huv' :
      Tendsto
        (fun n ↦ uSeq n + (ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ H)) (vSeq n))
        atTop (𝓝 (0 : H)) := by
    simpa [ContinuousLinearMap.adjoint_id] using huv
  simpa [dual_inclusion_solution_set, composite_dual_inclusion_solution_set,
    ContinuousLinearMap.adjoint_id] using
    mem_composite_dual_inclusion_solution_set_of_weak_primal_dual_residual_zero
      (ContinuousLinearMap.id ℝ H) hA hB hxu hyv hx hv hxy huv'

/-- Corollary 26.6 (3): under the hypotheses of Corollary 26.6, the weak limit pair
`(x, -u)` belongs to `gra A`. -/
theorem mem_graph_A_of_weak_graph_residual_zero
    (hA : Maximal IsMonotone A)
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ H (vSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (huv : Tendsto (fun n ↦ uSeq n + vSeq n) atTop (𝓝 (0 : H))) :
    (x, -u) ∈ gra A := by
  have huv' :
      Tendsto
        (fun n ↦ uSeq n + (ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ H)) (vSeq n))
        atTop (𝓝 (0 : H)) := by
    simpa [ContinuousLinearMap.adjoint_id] using huv
  simpa [ContinuousLinearMap.adjoint_id] using
    mem_graph_A_of_weak_primal_dual_residual_zero
      (ContinuousLinearMap.id ℝ H) hA hxu hx hv huv'

/-- Corollary 26.6 (4): under the hypotheses of Corollary 26.6, the weak limit pair
`(x, u)` belongs to `gra B`. -/
theorem mem_graph_B_of_weak_graph_residual_zero
    (hB : Maximal IsMonotone B)
    (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv : Tendsto (fun n ↦ toWeakSpace ℝ H (vSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hxy : Tendsto (fun n ↦ xSeq n - ySeq n) atTop (𝓝 (0 : H))) :
    (x, u) ∈ gra B := by
  simpa using
    mem_graph_B_of_weak_primal_dual_residual_zero
      (ContinuousLinearMap.id ℝ H) hB hyv hx hv hxy

end

end SetValuedOperator
