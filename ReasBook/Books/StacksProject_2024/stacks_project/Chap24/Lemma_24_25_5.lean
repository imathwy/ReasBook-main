import Mathlib
import StacksProject_2024.stacks_project.Chap24.Definition_24_25_2
import StacksProject_2024.stacks_project.Chap24.Lemma_24_24_2
import StacksProject_2024.stacks_project.Chap24.Lemma_24_25_1

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)
local notation "DGModA" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedModule.moduleCategory
    (C := C) (J := J) (𝒪 := 𝒪)
local notation "GrModA" =>
  _root_.SheafOfModules.RingedSite.UnderlyingGradedModule.moduleCategory
    (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic search note: `lean_leansearch` surfaced only generic injective/extension-property
-- results, so the owner/API choice here was verified against the local Chapter 24 operators
-- `exists_injectiveTestFamily`, `gradedHull`, and `gradedHull_acyclic`.

namespace DifferentialGradedModule

/-- A family of monomorphisms between acyclic differential graded modules that detects graded
injectivity by the extension property. -/
class IsAcyclicMonoTestFamilyForIsGradedInjective
    (𝒜 : DGAO) {T : Type _} (ℳ ℳ' : T → DGModA 𝒜) (ι : ∀ t, ℳ t ⟶ ℳ' t) : Prop where
  /-- Each test map in the family is a monomorphism. -/
  mono : ∀ t, Mono (ι t)
  /-- Each source object in the family is acyclic. -/
  source_acyclic : ∀ t, HomologicalComplex.Acyclic (ℳ t).toComplex
  /-- Each target object in the family is acyclic. -/
  target_acyclic : ∀ t, HomologicalComplex.Acyclic (ℳ' t).toComplex
  /-- Graded injectivity is equivalent to lifting against every map in the family. -/
  gradedInjective_iff :
    ∀ ℐ : DGModA 𝒜,
      _root_.DifferentialGradedModule.IsGradedInjective (forgetToGraded 𝒜) ℐ ↔
        ∀ t (f : ℳ t ⟶ ℐ), ∃ g : ℳ' t ⟶ ℐ, ι t ≫ g = f

/-- Lemma 24.25.5: let `(\mathcal C, \mathcal O)` be a ringed site and let `(\mathcal A, \mathrm d)`
be a sheaf of differential graded algebras on it. Then there exists a set-indexed family of
injective maps `\mathcal M_t \to \mathcal M'_t` between acyclic differential graded
`\mathcal A`-modules such that a differential graded `\mathcal A`-module `\mathcal I` is graded
injective if and only if every morphism `\mathcal M_t \to \mathcal I` extends across
`\mathcal M_t \to \mathcal M'_t`. -/
theorem exists_acyclicMonoTestFamily_for_isGradedInjective
    (𝒜 : DGAO) :
    ∃ (T : Type _) (ℳ ℳ' : T → DGModA 𝒜) (ι : ∀ t, ℳ t ⟶ ℳ' t),
      IsAcyclicMonoTestFamilyForIsGradedInjective 𝒜 ℳ ℳ' ι := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
