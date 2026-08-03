import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap04.Definition_4_33
import BauschkeLean.Chap23.ResolventRealizer
import BauschkeLean.Chap26.Text_26_0_1

open Function
open scoped InnerProductSpace Pointwise Set SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

noncomputable section

section HilbertComplete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The forward-backward splitting operator `T_{γA,γB} = J_{γA} ∘ (Id - γ B)` for a
single-valued `B`. -/
def forwardBackwardSplittingOperator
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (γ : PosReal) : H → H :=
  fun x ↦ resolventMap A hA γ (x - (γ : ℝ) • B x)

/-- The forward-backward splitting operator acts by `x ↦ J_{γA}(x - γ B x)`. -/
theorem forwardBackwardSplittingOperator_apply
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (γ : PosReal) (x : H) :
    forwardBackwardSplittingOperator A hA B γ x =
      resolventMap A hA γ (x - (γ : ℝ) • B x) := rfl

/-- If `A` is maximally monotone and `B : H → H` is single-valued, then the primal solution set
is the fixed-point set of the forward-backward splitting operator `T_{γA,γB}`. -/
theorem primal_inclusion_solution_set_eq_fixedPoints_forwardBackwardSplittingOperator
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (γ : PosReal) :
    primal_inclusion_solution_set A B.toSetValuedOperator =
      fixedPoints (forwardBackwardSplittingOperator A hA B γ) := by
  sorry

/-- If `B` is `β`-cocoercive on `H` and `γ ∈ ]0, 2β[`, then the forward-backward splitting
operator `T_{γA,γB}` is `(2β) / (4β - γ)`-averaged. -/
theorem forwardBackwardSplittingOperator_averaged_of_cocoercive
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (β γ : PosReal)
    (hB : CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x ↦ B x))
    (hγ : (γ : ℝ) < 2 * (β : ℝ)) :
    Averaged
      (2 * (β : ℝ) / (4 * (β : ℝ) - (γ : ℝ)))
      (forwardBackwardSplittingOperator A hA B γ) := by
  sorry

end HilbertComplete

end

end SetValuedOperator
