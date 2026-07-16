import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_33_1
import StacksProject_2024.stacks_project.Chap24.Lemma_24_26_8

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite
namespace DifferentialGradedAlgebra

section

variable {X : RingedSite.{u, v}} (𝒜 : DifferentialGradedAlgebra X)
variable [HasColimitsOfShape ℕ 𝒜.moduleCat] [HasExactColimitsOfShape ℕ 𝒜.moduleCat]

-- Semantic search note: `lean_leansearch` recalled the canonical degree-zero derived embedding
-- through `DerivedCategory.singleFunctors`; the final owner/API choice was then checked against
-- Chapter 13's `IsHomotopyColimitOf` owner and the repo's `singleFunctorIsoCompQ` usage, so the
-- public surface is the degree-zero derived object of the dg-module colimit.

/-- Lemma 24.27.2: let `(\mathcal C, \mathcal O)` be a ringed site, let
`(\mathcal A, \mathrm d)` be a sheaf of differential graded algebras on it, and let
`\mathcal M_0 \to \mathcal M_1 \to \mathcal M_2 \to \cdots` be a sequential system of
differential graded `\mathcal A`-modules. Then the derived colimit in `D(\mathcal A, \mathrm d)`
is represented by the ordinary colimit dg module, viewed as a degree-zero object of the derived
category; the countable direct sum needed to form the homotopy colimit is the direct-sum
hypothesis supplied in Chapter `24` by Lemma `24.26.8`. -/
@[stacks 0FTC]
theorem dgModuleColimit_is_homotopy_colimit
    (M : ℕ → 𝒜.moduleCat) (f : ∀ n, M n ⟶ M (n + 1))
    [HasCoproduct (((Functor.ofSequence f) ⋙ DerivedCategory.singleFunctor 𝒜.moduleCat 0).obj)] :
    IsHomotopyColimitOf
      ((Functor.ofSequence f) ⋙ DerivedCategory.singleFunctor 𝒜.moduleCat 0)
      ((DerivedCategory.singleFunctor 𝒜.moduleCat 0).obj (colimit (Functor.ofSequence f))) := sorry

end

end DifferentialGradedAlgebra
end RingedSite
