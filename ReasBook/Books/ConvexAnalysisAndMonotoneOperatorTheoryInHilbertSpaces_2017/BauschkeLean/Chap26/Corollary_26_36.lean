import BauschkeLean.Chap26.Problem_26_35
import BauschkeLean.Chap26.Theorem_26_34

open Filter
open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator Topology

universe u v

noncomputable section

namespace SetValuedOperator

open ContinuousLinearMap
open ERealFunction

-- Semantic recall/local precedent: `lean_leansearch` surfaced only generic direct-sum/operator-
-- norm results, so this item follows the verified local Chapter 26 owners
-- `finite_family_composite_primal_inclusion_solution_set`,
-- `finite_family_composite_dual_inclusion_solution_set`,
-- `composite_kuhn_tucker_points`, and
-- `compositeForwardBackwardForwardIteration` with its canonical direct-sum bridges
-- `familyOperator` and `toLpOperator`.
--
-- Source/core/bridge triage:
-- - `source-facing`: the finite-family recursion `(26.103)` and the corollary conclusions stated
--   with primal/dual residuals and weak limits for its recursive sequences.
-- - `core/canonical`: the direct-sum range owner
--   `A + (toLpOperator L).adjointImage ((familyOperator B).translate r)`, the product-space
--   forward-backward-forward sequences from `Theorem_26_34`, and the Kuhn--Tucker owner
--   `composite_kuhn_tucker_points`.
-- - `bridge/view`: this file states the finite-family corollaries directly with the specialized
--   Chapter 26 product-space owners through `familyOperator` and `toLpOperator`, rather than
--   republishing a parallel finite-family wrapper API for the same recursive sequences.

variable {I : Type v} {H : Type u} {K : I → Type u}
variable [Fintype I]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- Corollary 26.36 (1): under the source range assumption `(26.102)` and the finite-family
forward-backward-forward recursion `(26.103)`, the primal residuals `x_n - p_{1,n}` converge
strongly to `0`. -/
theorem finite_family_compositeForwardBackwardForward_primalResidual_tendsto_zero
    (z : H) (A : SetValuedOperator H H) (r : lp K 2)
    (B : ∀ i, SetValuedOperator (K i) (K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hA_max : Maximal IsMonotone A)
    (hB_max : ∀ i, Maximal IsMonotone (B i))
    (hz :
      z ∈ SetValuedOperator.range
        (A + (toLpOperator L).adjointImage ((familyOperator B).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (JγM : H × lp K 2 → H × lp K 2)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r (familyOperator B))])
    (x0 : H) (v0 : lp K 2) :
    Tendsto
      (fun n ↦
        compositeForwardBackwardForwardPrimalIteration
            z A r (familyOperator B) (toLpOperator L) γ JγM x0 v0 n -
          compositeForwardBackwardForwardPrimalResolventSequence
            z A r (familyOperator B) (toLpOperator L) γ JγM x0 v0 n)
      atTop (𝓝 (0 : H)) := sorry

/-- Corollary 26.36 (2): under the source range assumption `(26.102)` and the finite-family
forward-backward-forward recursion `(26.103)`, every dual residual `v_{i,n} - p_{2,i,n}`
converges strongly to `0`. -/
theorem finite_family_compositeForwardBackwardForward_dualResidual_tendsto_zero
    (z : H) (A : SetValuedOperator H H) (r : lp K 2)
    (B : ∀ i, SetValuedOperator (K i) (K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hA_max : Maximal IsMonotone A)
    (hB_max : ∀ i, Maximal IsMonotone (B i))
    (hz :
      z ∈ SetValuedOperator.range
        (A + (toLpOperator L).adjointImage ((familyOperator B).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (JγM : H × lp K 2 → H × lp K 2)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r (familyOperator B))])
    (x0 : H) (v0 : lp K 2) :
    ∀ i : I,
      Tendsto
        (fun n ↦
          compositeForwardBackwardForwardDualIteration
              z A r (familyOperator B) (toLpOperator L) γ JγM x0 v0 n i -
            compositeForwardBackwardForwardDualResolventSequence
              z A r (familyOperator B) (toLpOperator L) γ JγM x0 v0 n i)
        atTop (𝓝 (0 : K i)) := sorry

/-- Corollary 26.36 (3): under `(26.102)` and `(26.103)`, there exists a weak-limit solution
pair `(x̄, v̄)` whose components solve the finite-family primal and dual inclusions, satisfy the
source inclusion relations, and attract `x_n` and `v_{i,n}` weakly. -/
theorem finite_family_compositeForwardBackwardForward_exists_weakLimit_solution
    (z : H) (A : SetValuedOperator H H) (r : lp K 2)
    (B : ∀ i, SetValuedOperator (K i) (K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hA_max : Maximal IsMonotone A)
    (hB_max : ∀ i, Maximal IsMonotone (B i))
    (hz :
      z ∈ SetValuedOperator.range
        (A + (toLpOperator L).adjointImage ((familyOperator B).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (JγM : H × lp K 2 → H × lp K 2)
    (hJγM :
      JγM.toSetValuedOperator =
        J[((γ : ℝ) • composite_kuhn_tucker_operator z A r (familyOperator B))])
    (x0 : H) (v0 : lp K 2) :
    ∃ xbar : H, ∃ vbar : lp K 2,
      xbar ∈ finite_family_composite_primal_inclusion_solution_set z A r B L ∧
      vbar ∈ finite_family_composite_dual_inclusion_solution_set z A r B L ∧
      z - ∑ i, (L i).adjoint (vbar i) ∈ A xbar ∧
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (compositeForwardBackwardForwardPrimalIteration
              z A r (familyOperator B) (toLpOperator L) γ JγM x0 v0 n))
        atTop (𝓝 (toWeakSpace ℝ H xbar)) ∧
      (∀ i : I, L i xbar - r i ∈ (B i)⁻¹ (vbar i)) ∧
      ∀ i : I,
        Tendsto
          (fun n ↦
            toWeakSpace ℝ (K i)
              (compositeForwardBackwardForwardDualIteration
                z A r (familyOperator B) (toLpOperator L) γ JγM x0 v0 n i))
          atTop
          (𝓝 (toWeakSpace ℝ (K i) (vbar i))) := sorry

end SetValuedOperator
