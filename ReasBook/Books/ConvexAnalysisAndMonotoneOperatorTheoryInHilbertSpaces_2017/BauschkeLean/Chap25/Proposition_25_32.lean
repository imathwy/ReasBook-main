import Mathlib
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_24
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Proposition_16_61
import BauschkeLean.Chap25.Definition_25_29
import BauschkeLean.Chap25.Definition_25_39
import BauschkeLean.Chap25.Proposition_25_43

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace ERealFunction

section ParallelSum

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 25.32: let `f, g ∈ Γ₀(H)` and suppose that
`0 ∈ sri (effectiveDomain (f∗[hf]) - effectiveDomain (g∗[hg]))`.
Then the parallel sum of the subdifferentials of `f` and `g` is the subdifferential of the
textbook function parallel sum `f boxdot g`, canonically identified here with the existing
infimal convolution `f □ g`. This is equation `(25.35)`. -/
theorem parallelSum_subdifferential_eq_subdifferential_parallelSum
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - effectiveDomain (g∗[hg]))) :
    SetValuedOperator.parallelSum (∂ f) (∂ g) = ∂ (f □ g) := by
  have hpost :
      ((ContinuousLinearMap.id ℝ H) ▷ f) = (f : H → EReal) := by
    funext x
    simp [ERealFunction.infimalPostcomposition]
  have hcomp :
      (((ContinuousLinearMap.id ℝ H) ▷ ∂ f) : SetValuedOperator H H) = ∂ f := by
    ext x u
    rw [ContinuousLinearMap.mem_parallelComposition_iff]
    constructor
    · rintro ⟨y, hy, hu⟩
      have hy' : y = x := by
        simpa using hy
      subst y
      simpa using hu
    · intro hu
      exact ⟨x, rfl, by simpa using hu⟩
  have hsriId :
      (0 : H) ∈
        sri
          (effectiveDomain (f∗[hf]) -
            (ContinuousLinearMap.id ℝ H).adjoint '' effectiveDomain (g∗[hg])) := by
    simpa using hsri
  have hmain :
      ∂ ((((ContinuousLinearMap.id ℝ H) ▷ f) □ g)) =
        SetValuedOperator.parallelSum
          (((ContinuousLinearMap.id ℝ H) ▷ ∂ f) : SetValuedOperator H H) (∂ g) :=
    subdifferential_infimalPostcomposition_infimalConvolution_eq_parallelSum_of_zero_mem_sri_conjugateDomains
      (hf := hf)
      (hg := hg)
      (L := ContinuousLinearMap.id ℝ H)
      (hsri := hsriId)
  calc
    SetValuedOperator.parallelSum (∂ f) (∂ g)
        =
          SetValuedOperator.parallelSum
            (((ContinuousLinearMap.id ℝ H) ▷ ∂ f) : SetValuedOperator H H) (∂ g) := by
            rw [hcomp]
    _ = ∂ ((((ContinuousLinearMap.id ℝ H) ▷ f) □ g)) := by
          symm
          exact hmain
    _ = ∂ (f □ g) := by
          rw [hpost]

end ParallelSum

end ERealFunction
