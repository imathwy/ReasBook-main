import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap28.Problem_28_20
import BauschkeLean.Chap26.Corollary_26_36

open Filter
open ContinuousLinearMap
open SetValuedOperator
open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator Topology

universe u v

noncomputable section

namespace ERealFunction

section FiniteFamilyCompositePrimalDualAlgorithm

variable {I : Type v} {H : Type u} {K : I → Type u}
variable [Fintype I]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

-- Semantic recall: the owner abstractions here are Chapter 26's finite-family composite
-- forward-backward-forward recursion and Chapter 15/19's composite objective owners. The source
-- proximal formulas are therefore expressed through one explicit product-space resolvent map,
-- while the theorem surface uses the canonical Chapter 26 sequences directly.

private def lpFamily
    (w : ∀ i, K i) : lp K 2 :=
  (lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 w)

omit [∀ i, CompleteSpace (K i)] in
@[simp] private theorem lpFamily_apply
    (w : ∀ i, K i) (i : I) :
    lpFamily w i = w i := by
  change ((lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 w)) i = w i
  rw [coe_lpPiLpₗᵢ_symm]

/-- The canonical product-space resolvent realizer for the subdifferential specialization of the
finite-family forward-backward-forward recursion from Proposition 28.21. -/
private def finiteFamilySubdifferentialForwardBackwardForwardResolvent
    {h : H → Set.Ioi (⊥ : EReal)} (hh : h ∈ Γ₀(H)) (z : H) (r : lp K 2)
    {g : ∀ i, K i → Set.Ioi (⊥ : EReal)} (hg : ∀ i, g i ∈ Γ₀(K i))
    (γ : PosReal) : H × lp K 2 → H × lp K 2 :=
  fun xv ↦
    ( Prox[γ, h, hh] (xv.1 + (γ : ℝ) • z)
    , lpFamily fun i ↦
        xv.2 i -
          (γ : ℝ) •
            (r i + Prox[(γ⁻¹ : PosReal), g i, hg i] (((γ : ℝ)⁻¹) • xv.2 i - r i)) )

/-- Proposition 28.21 (1): under the source range assumption `(28.76)` and the recursion
`(28.77)`, the primal residuals `x_n - p_{1,n}` of the canonical Chapter 26 finite-family
forward-backward-forward specialization converge strongly to `0`. -/
theorem finite_family_subdifferential_forward_backward_forward_primal_residual_tendsto_zero
    {h : H → Set.Ioi (⊥ : EReal)} (hh : h ∈ Γ₀(H)) (z : H) (r : lp K 2)
    {g : ∀ i, K i → Set.Ioi (⊥ : EReal)} (hg : ∀ i, g i ∈ Γ₀(K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hz :
      z ∈ SetValuedOperator.range
        ((∂ h) +
          (ContinuousLinearMap.toLpOperator L).adjointImage
            ((SetValuedOperator.familyOperator fun i ↦ ∂ (g i)).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (x0 : H) (v0 : lp K 2) :
    let JγM :=
      finiteFamilySubdifferentialForwardBackwardForwardResolvent hh z r hg γ
    let x :=
      compositeForwardBackwardForwardPrimalIteration
        z (∂ h) r (familyOperator fun i ↦ ∂ (g i)) (toLpOperator L) γ JγM x0 v0
    let p1 :=
      compositeForwardBackwardForwardPrimalResolventSequence
        z (∂ h) r (familyOperator fun i ↦ ∂ (g i)) (toLpOperator L) γ JγM x0 v0
    Tendsto (fun n ↦ x n - p1 n) atTop (𝓝 (0 : H)) := sorry

/-- Proposition 28.21 (2): under the source range assumption `(28.76)` and the recursion
`(28.77)`, every dual residual `v_{i,n} - p_{2,i,n}` of the canonical Chapter 26 finite-family
forward-backward-forward specialization converges strongly to `0`. -/
theorem finite_family_subdifferential_forward_backward_forward_dual_residual_tendsto_zero
    {h : H → Set.Ioi (⊥ : EReal)} (hh : h ∈ Γ₀(H)) (z : H) (r : lp K 2)
    {g : ∀ i, K i → Set.Ioi (⊥ : EReal)} (hg : ∀ i, g i ∈ Γ₀(K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hz :
      z ∈ SetValuedOperator.range
        ((∂ h) +
          (ContinuousLinearMap.toLpOperator L).adjointImage
            ((SetValuedOperator.familyOperator fun i ↦ ∂ (g i)).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (x0 : H) (v0 : lp K 2) :
    let JγM :=
      finiteFamilySubdifferentialForwardBackwardForwardResolvent hh z r hg γ
    let v :=
      compositeForwardBackwardForwardDualIteration
        z (∂ h) r (familyOperator fun i ↦ ∂ (g i)) (toLpOperator L) γ JγM x0 v0
    let p2 :=
      compositeForwardBackwardForwardDualResolventSequence
        z (∂ h) r (familyOperator fun i ↦ ∂ (g i)) (toLpOperator L) γ JγM x0 v0
    ∀ i : I, Tendsto (fun n ↦ v n i - p2 n i) atTop (𝓝 (0 : K i)) := sorry

/-- Proposition 28.21 (3): under the source range assumption `(28.76)` and the recursion
`(28.77)`, there exist primal and dual solutions of the Problem 28.20 objectives, represented by
the canonical Chapter 15/19 objective owners, whose subdifferential relations match the source
and to which the canonical Chapter 26 primal and dual iterates converge weakly. -/
theorem finite_family_subdifferential_forward_backward_forward_exists_primal_dual_weak_limits
    {h : H → Set.Ioi (⊥ : EReal)} (hh : h ∈ Γ₀(H)) (z : H) (r : lp K 2)
    {g : ∀ i, K i → Set.Ioi (⊥ : EReal)} (hg : ∀ i, g i ∈ Γ₀(K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hz :
      z ∈ SetValuedOperator.range
        ((∂ h) +
          (ContinuousLinearMap.toLpOperator L).adjointImage
            ((SetValuedOperator.familyOperator fun i ↦ ∂ (g i)).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (x0 : H) (v0 : lp K 2) :
    let JγM :=
      finiteFamilySubdifferentialForwardBackwardForwardResolvent hh z r hg γ
    let x :=
      compositeForwardBackwardForwardPrimalIteration
        z (∂ h) r (familyOperator fun i ↦ ∂ (g i)) (toLpOperator L) γ JγM x0 v0
    let v :=
      compositeForwardBackwardForwardDualIteration
        z (∂ h) r (familyOperator fun i ↦ ∂ (g i)) (toLpOperator L) γ JγM x0 v0
    let primalObj :=
      compositePrimalObjective (linearTilt z h) (shiftedHilbertSum r g) (toLpOperator L)
    let dualObj :=
      compositeDualObjective (linearTilt z h) (shiftedHilbertSum r g) (toLpOperator L)
    ∃ xbar : H, ∃ vbar : lp K 2,
      xbar ∈ Argmin primalObj ∧
        vbar ∈ Argmin dualObj ∧
        z - ∑ i, (L i).adjoint (vbar i) ∈ (∂ h) xbar ∧
        Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop
          (𝓝 (toWeakSpace ℝ H xbar)) ∧
        (∀ i : I, L i xbar - r i ∈ (∂ ((g i)∗[hg i])) (vbar i)) ∧
        ∀ i : I,
          Tendsto (fun n ↦ toWeakSpace ℝ (K i) (v n i)) atTop
            (𝓝 (toWeakSpace ℝ (K i) (vbar i))) := sorry

end FiniteFamilyCompositePrimalDualAlgorithm

end ERealFunction
