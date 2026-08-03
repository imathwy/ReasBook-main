import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap20.Corollary_20_28
import BauschkeLean.Chap21.Corollary_21_14
import BauschkeLean.Chap25.Corollary_25_5
import BauschkeLean.Chap26.Theorem_26_17

open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall: `lean_leansearch` returned only generic projection/convexity owners for this
-- remark, so the file uses the verified local Chapter 20/21/25 owners
-- `Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous`,
-- `convex_closure_dom_of_maximal`, `Maximal.add_of_sumRegularity`, and the direct Chapter 26
-- forward-backward-forward recursion equations.

/- Remark 26.18: the sufficient conditions for maximal monotonicity of `A + B` mentioned here
are already formalized by `Maximal.add_of_cone_dom_sub_eq_span` and
`Maximal.add_of_sumRegularity`. The constraint set `C` from Theorem 26.17 already restricts the
target set to `C ∩ (A + B).zeros`, so the zeros selected by the algorithm are constrained by
`C`. -/

/-- Remark 26.18 (1): if `A` is maximally monotone and `A.dom` is closed, then `A.dom` is convex;
hence `A.dom` is an admissible choice of constraint set `C` in Theorem 26.17. -/
theorem convex_dom_of_isClosed_of_maximal
    (A : SetValuedOperator H H) (hA_max : Maximal IsMonotone A) (hA_closed : IsClosed A.dom) :
    Convex ℝ A.dom := by
  simpa [hA_closed.closure_eq] using convex_closure_dom_of_maximal A hA_max

/-- Remark 26.18 (2): if `B : H → H` is monotone and continuous on `H`, then the associated
singleton-valued operator `B.toSetValuedOperator` is maximally monotone, and therefore
`A + B.toSetValuedOperator` is maximally monotone by Corollary 25.5(i). -/
theorem maximal_add_toSetValuedOperator_of_monotone_continuous
    {A : SetValuedOperator H H} {B : H → H}
    (hA_max : Maximal IsMonotone A) (hB_mono : B.toSetValuedOperator.IsMonotone)
    (hB_cont : Continuous B) :
    Maximal IsMonotone (A + B.toSetValuedOperator) := by
  have hB_max :
      Maximal IsMonotone B.toSetValuedOperator :=
    Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous B hB_mono hB_cont
  refine Maximal.add_of_sumRegularity hA_max hB_max ?_
  left
  ext x
  rw [mem_dom_iff, Function.toSetValuedOperator_apply]
  simp

private theorem isChebyshev_univ : IsChebyshev (Set.univ : Set H) :=
  isChebyshev_of_nonempty_isClosed_convex ⟨0, Set.mem_univ 0⟩ isClosed_univ convex_univ

private theorem projectionPoint_univ_eq_self (x : H) :
    P[Set.univ, isChebyshev_univ] x = x := by
  symm
  refine
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      ⟨0, Set.mem_univ 0⟩ isClosed_univ convex_univ).2 ?_
  refine ⟨by simp, ?_⟩
  intro y hy
  simp

/-- When the constraint set is `H`, the projected Tseng orbit starts at `x₀`. -/
@[simp] theorem projectedForwardBackwardForwardIteration_univ_zero
    (JγA : H → H) (B : H → H) (γ : PosReal) (x0 : H) :
    projectedForwardBackwardForwardIteration
      JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ 0 = x0 := by
  exact
    projectedForwardBackwardForwardIteration_zero
      JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩

/-- When the constraint set is `H`, the predictor sequence is the unconstrained forward step
`yₙ = xₙ - γ B xₙ`. -/
@[simp] theorem projectedForwardBackwardForwardPredictorSequence_univ_apply
    (JγA : H → H) (B : H → H) (γ : PosReal) (x0 : H) (n : ℕ) :
    projectedForwardBackwardForwardPredictorSequence
        JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ n =
      projectedForwardBackwardForwardIteration
          JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ n -
        (γ : ℝ) •
          B
            (projectedForwardBackwardForwardIteration
              JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ n) := by
  exact
    projectedForwardBackwardForwardPredictorSequence_apply
      JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ n

/-- When the constraint set is `H`, the canonical resolvent sequence is still realized by the
chosen single-valued realizer `JγA`. -/
theorem projectedForwardBackwardForwardResolventSequence_univ_eq_resolvent
    {A : SetValuedOperator H H} {B : H → H} {γ : PosReal}
    (JγA : H → H) (hJγA : JγA.toSetValuedOperator = J[((γ : ℝ) • A)]) (x0 : H) (n : ℕ) :
    J[((γ : ℝ) • A)]
        (projectedForwardBackwardForwardPredictorSequence
          JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ n) =
      ({projectedForwardBackwardForwardResolventSequence
          JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ n} : Set H) := by
  rw [← hJγA, Function.toSetValuedOperator_apply, Set.singleton_eq_singleton_iff]
  exact
    projectedForwardBackwardForwardResolventSequence_apply
      JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ n

/-- When the constraint set is `H`, the projected Tseng recursion reduces to the unconstrained
forward-backward-forward update `xₙ₊₁ = xₙ - yₙ + zₙ - γ B zₙ`. -/
theorem projectedForwardBackwardForwardIteration_univ_succ
    (JγA : H → H) (B : H → H) (γ : PosReal) (x0 : H) (n : ℕ) :
    projectedForwardBackwardForwardIteration
        JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩ (n + 1) =
      let x :=
        projectedForwardBackwardForwardIteration
          JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩
      let y :=
        projectedForwardBackwardForwardPredictorSequence
          JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩
      let z :=
        projectedForwardBackwardForwardResolventSequence
          JγA B (Set.univ : Set H) isChebyshev_univ γ ⟨x0, Set.mem_univ x0⟩
      x n - y n + z n - (γ : ℝ) • B (z n) := by
  simp only [projectedForwardBackwardForwardIteration_succ,
    projectedForwardBackwardForwardPredictorSequence_apply,
    projectedForwardBackwardForwardResolventSequence_apply]
  rw [projectionPoint_univ_eq_self]
  simp [sub_eq_add_neg, add_assoc]

end SetValuedOperator
