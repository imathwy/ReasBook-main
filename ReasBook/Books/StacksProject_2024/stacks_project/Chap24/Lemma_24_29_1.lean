import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.Chap13.Lemma_13_14_15
import StacksProject_2024.Chap13.Lemma_13_31_6
import StacksProject_2024.Chap24.Lemma_24_26_7

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v uGr vGr uD vD

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite
namespace DifferentialGradedAlgebra

section

variable {X : RingedSite.{u, v}} (𝒜 : DifferentialGradedAlgebra X)
variable {GrModA : Type uGr} [Category.{vGr} GrModA] [Abelian GrModA]
variable {𝒟 : Type uD} [Category.{vD} 𝒟]
variable [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟]
variable [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
variable [Pretriangulated 𝒟] [IsTriangulated 𝒟]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜.moduleCat (up ℤ)
local notation "KQ" => HomotopyCategory.quotient 𝒜.moduleCat (up ℤ)

-- Semantic search note: `lean_leansearch` returned the canonical pointwise/right-derived owners
-- `Functor.HasRightDerivedFunctor` and `Functor.ComputesRightDerivedAt`; the Chapter 24
-- source-facing specialization below follows `Chap13/Lemma_13_14_15.lean`,
-- `Chap13/Lemma_13_31_6.lean`, and `Chap24/Lemma_24_26_7.lean`.

variable (forgetToGraded : CochainComplex 𝒜.moduleCat ℤ ⥤ GrModA)
variable (T : HomotopyCategory 𝒜.moduleCat (up ℤ) ⥤ 𝒟)
variable [T.CommShift ℤ] [T.IsTriangulated]

/-- Lemma 24.29.1: let `(\mathcal C, \mathcal O)` be a ringed site, let `(\mathcal A, d)` be a
sheaf of differential graded algebras on it, and let
`T : K(\textit{Mod}(\mathcal A, d)) ⥤ \mathcal D` be an exact functor to a triangulated category.
Then `T` has a right derived extension from `K(\textit{Mod}(\mathcal A, d))` to
`D(\mathcal A, d)`, formalized canonically as existence of the right derived functor of `T` with
respect to quasi-isomorphisms. -/
@[stacks 0FTN]
theorem exactFunctor_hasRightDerivedExtension :
    T.HasRightDerivedFunctor Qis := sorry

/-- A graded-injective K-injective differential graded `\mathcal A`-module computes the right
derived extension of `T`; equivalently, the right derived functor takes its image in
`D(\mathcal A, d)` to `T(\mathcal I)` up to the canonical comparison isomorphism. -/
@[stacks 0FTN]
theorem computesRightDerivedExtensionAt_of_isGradedInjective_and_isKInjective
    (I : CochainComplex 𝒜.moduleCat ℤ) [I.IsKInjective]
    [DifferentialGradedModule.IsGradedInjective forgetToGraded I] :
    T.ComputesRightDerivedAt Qis ((KQ).obj I) := sorry

end

end DifferentialGradedAlgebra
end RingedSite
