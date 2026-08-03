import Mathlib.Tactic.Recall
import BauschkeLean.Chap16.Proposition_16_9
import BauschkeLean.Chap16.Theorem_16_58
import BauschkeLean.Chap19.Theorem_19_1
import BauschkeLean.Chap28.Proposition_28_21

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open SetValuedOperator
open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Remark 28.22 observes that, in the setting of Proposition 28.21,
  Proposition 28.21 already provides a primal minimizer for the finite-family composite primal
  objective, and therefore the source condition `(28.76)` may be replaced by nonemptiness of the
  corresponding zero set.
- `core/canonical`: the Chapter 28 owner
  `finite_family_subdifferential_forward_backward_forward_exists_primal_dual_weak_limits`
  already packages the primal argmin witness, while the core zero-set owners remain
  `linearTilt`, `shiftedHilbertSum`, `adjointImageSubdifferential`, and `∂`.
- `bridge/view`: this file adds only the two thin bridge theorems extracting the primal
  nonemptiness and transferring it to the corresponding zero-set owner; it introduces no duplicate
  wrapper API.

Primitive data: none beyond the hypotheses already packaged by the recalled Chapter 28 owner and
the corresponding subgradient witness.
Derived API: the primal argmin nonemptiness bridge and its zero-set nonemptiness consequence.
-/

/-
Remark 28.22: in the setting of Proposition 28.21, the Chapter 28 weak-limit existence theorem
already yields a primal minimizer, hence `Argmin (f + g ∘ L) ≠ ∅`; equivalently for the Chapter 28
tilted finite-family owner, `(28.76)` implies nonemptiness of the associated zero set.
-/
noncomputable section

universe u v

namespace ERealFunction

section FiniteFamilyCompositePrimalDualRemark

variable {I : Type v} {H : Type u} {K : I → Type u}
variable [Fintype I]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- Remark 28.22: Proposition 28.21 already yields a primal minimizer for the finite-family
composite primal objective, so its argmin set is nonempty. -/
theorem finite_family_subdifferential_forward_backward_forward_primal_argmin_nonempty
    {h : H → Set.Ioi (⊥ : EReal)} (hh : h ∈ Γ₀(H)) (z : H) (r : lp K 2)
    {g : ∀ i, K i → Set.Ioi (⊥ : EReal)} (hg : ∀ i, g i ∈ Γ₀(K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hz :
      z ∈ SetValuedOperator.range
        ((∂ h) +
          (toLpOperator L).adjointImage
            ((familyOperator fun i ↦ ∂ (g i)).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (x0 : H) (v0 : lp K 2) :
    (Argmin
      (compositePrimalObjective
        (linearTilt z h) (shiftedHilbertSum r g) (toLpOperator L))).Nonempty := by
  rcases
      finite_family_subdifferential_forward_backward_forward_exists_primal_dual_weak_limits
        hh z r hg L hz γ hγ_lt x0 v0 with
    ⟨xbar, _, hxbar, _, _, _, _, _⟩
  exact ⟨xbar, hxbar⟩

/-- Remark 28.22: the primal-dual witness furnished by Proposition 28.21 already yields a point
in the zero set of the finite-family tilted subdifferential sum, so the range condition `(28.76)`
implies nonemptiness of that zero set. -/
theorem finite_family_subdifferential_forward_backward_forward_zeros_subdifferential_sum_nonempty
    {h : H → Set.Ioi (⊥ : EReal)} (hh : h ∈ Γ₀(H)) (z : H) (r : lp K 2)
    {g : ∀ i, K i → Set.Ioi (⊥ : EReal)} (hg : ∀ i, g i ∈ Γ₀(K i))
    (L : ∀ i, H →L[ℝ] K i)
    (hz :
      z ∈ SetValuedOperator.range
        ((∂ h) +
          (toLpOperator L).adjointImage
            ((familyOperator fun i ↦ ∂ (g i)).translate r)))
    (γ : PosReal)
    (hγ_lt : (γ : ℝ) < (1 : ℝ) / Real.sqrt (∑ i, ‖L i‖ ^ 2))
    (x0 : H) (v0 : lp K 2) :
    (((∂ (linearTilt z h)) +
      ContinuousLinearMap.adjointImageSubdifferential
        (toLpOperator L) (shiftedHilbertSum r g)).zeros).Nonempty := by
  rcases
      finite_family_subdifferential_forward_backward_forward_exists_primal_dual_weak_limits
        hh z r hg L hz γ hγ_lt x0 v0 with
    ⟨xbar, vbar, _, _, hzbar, _, hvbar, _⟩
  have hlinearEq : linearTilt z h = affineTiltIoi h hh z := by
    ext x
    simp [linearTilt, affineTiltEReal, sub_eq_add_neg]
  have hshiftedEq :
      shiftedHilbertSum r g = directSumFunction (fun i y ↦ g i (y - r i)) := by
    ext y
    simpa using congrArg (fun φ ↦ φ y)
      (shiftedHilbertSum_asEReal_eq_directSumFunction_shifted r g)
  have hdom : ∀ i, (effectiveDomain (fun y : K i ↦ g i (y - r i))).Nonempty := by
    intro i
    rcases (hg i).2.nonempty with ⟨y, hy⟩
    refine ⟨y + r i, ?_⟩
    simpa [mem_effectiveDomain_iff, sub_eq_add_neg, add_assoc] using hy
  refine ⟨xbar, ?_⟩
  rw [SetValuedOperator.mem_zeros_iff]
  refine ⟨-(toLpOperator L).adjoint vbar, ?_, (toLpOperator L).adjoint vbar, ?_, by simp⟩
  · rw [hlinearEq]
    refine (mem_subdifferential_affineTiltIoi_iff h hh z xbar (-(toLpOperator L).adjoint vbar)).2 ?_
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      ContinuousLinearMap.toLpOperator_adjoint_apply_eq_sum] using hzbar
  · rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
    refine ⟨vbar, ?_, rfl⟩
    rw [hshiftedEq]
    rw [subdifferential_directSumFunction_eq_coordinatewise
      (fun i y ↦ g i (y - r i)) hdom ((toLpOperator L) xbar)]
    intro i
    have hvi : vbar i ∈ (∂ (g i)) (L i xbar - r i) := by
      exact
        (mem_subdifferential_iff_mem_subdifferential_gammaZeroConjugate
          (g i) (hg i) (L i xbar - r i) (vbar i)).2 (hvbar i)
    have hvi' : vbar i ∈ (∂ (g i)) (-r i + L i xbar) := by
      simpa [sub_eq_add_neg, add_comm] using hvi
    have htranslated :
        vbar i ∈ (∂ fun y : K i ↦ g i (y - r i)) (L i xbar) := by
      simpa [sub_eq_add_neg, add_comm] using
        ((mem_subdifferential_translate_iff :
          vbar i ∈ (∂ fun y : K i ↦ g i (-r i + y)) (L i xbar) ↔
            vbar i ∈ (∂ (g i)) (-r i + L i xbar)).2 hvi')
    simpa using htranslated

end FiniteFamilyCompositePrimalDualRemark

recall finite_family_subdifferential_forward_backward_forward_exists_primal_dual_weak_limits

end ERealFunction
