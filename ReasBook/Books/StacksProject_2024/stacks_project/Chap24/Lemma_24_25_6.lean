import StacksProject_2024.Chap24.Definition_24_13_1

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _

namespace DifferentialGradedModule

/-- A set-indexed family of acyclic differential graded `\mathcal A`-modules that detects every
nonzero acyclic module by a monomorphism from one member of the family. -/
class IsAcyclicMonoTestFamily
    (𝒜 : DGAO) {S : Type _} (Ms : S → DGModA 𝒜) : Prop where
  /-- Every member of the family is acyclic. -/
  acyclic : ∀ s : S, HomologicalComplex.Acyclic (Ms s).toComplex
  /-- Every nonzero acyclic differential graded `\mathcal A`-module admits a monomorphism from
  one member of the family. -/
  exists_mono {M : DGModA 𝒜} (_ : HomologicalComplex.Acyclic M.toComplex)
      (_ : ¬ IsZero M) :
      ∃ s : S, ∃ f : Ms s ⟶ M, Mono f

namespace IsAcyclicMonoTestFamily

variable {𝒜 : DGAO} {S : Type _} {Ms : S → DGModA 𝒜}

/-- Each member of an acyclic mono test family is acyclic. -/
theorem member_acyclic [IsAcyclicMonoTestFamily 𝒜 Ms] (s : S) :
    HomologicalComplex.Acyclic (Ms s).toComplex :=
  (inferInstance : IsAcyclicMonoTestFamily 𝒜 Ms).acyclic s

/-- A test family detects every nonzero acyclic differential graded `\mathcal A`-module by a
monomorphism from one of its members. -/
theorem exists_mono_of_acyclic [IsAcyclicMonoTestFamily 𝒜 Ms]
    {M : DGModA 𝒜} (_ : HomologicalComplex.Acyclic M.toComplex)
    (_ : ¬ IsZero M) :
    ∃ s : S, ∃ f : Ms s ⟶ M, Mono f :=
  (inferInstance : IsAcyclicMonoTestFamily 𝒜 Ms).exists_mono ‹_› ‹_›

end IsAcyclicMonoTestFamily
end DifferentialGradedModule
end

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _

namespace DifferentialGradedModule

/-- Lemma 24.25.6: for a ringed site `(\mathcal C, \mathcal O)` and a sheaf of differential
graded algebras `(\mathcal A, d)` on it, there is a set-indexed family of acyclic differential
graded `\mathcal A`-modules such that every nonzero acyclic differential graded
`\mathcal A`-module admits an injective map from one member of the family. -/
@[stacks 0FST]
theorem exists_acyclic_mono_test_family (𝒜 : DGAO) :
    ∃ (S : Type _) (Ms : S → DGModA 𝒜), IsAcyclicMonoTestFamily 𝒜 Ms := sorry

end DifferentialGradedModule
end
end SheafOfModules.RingedSite
