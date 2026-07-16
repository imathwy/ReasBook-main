import Mathlib
import StacksProject_2024.stacks_project.Chap24.Lemma_24_25_5

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

-- Semantic search note: `lean_leansearch` surfaced only generic K-injective and lifting-property
-- owners, so the statement below is anchored to the local Chapter 24 test-family owner
-- `IsAcyclicMonoTestFamilyForIsGradedInjective` from `Lemma_24_25_5.lean`, while the K-injective
-- side is expressed on the underlying cochain complex `I.toComplex`, matching the chapter's
-- acyclicity owner.

namespace DifferentialGradedModule

/-- A family of monomorphisms between acyclic differential graded modules that detects the
combination of K-injectivity of the underlying cochain complex and graded injectivity by the
extension property. -/
@[stacks 0FSY]
class IsAcyclicMonoTestFamilyForIsKInjectiveAndIsGradedInjective
    (𝒜 : DGAO) {R : Type _} (ℳ ℳ' : R → DGModA 𝒜) (ι : ∀ r, ℳ r ⟶ ℳ' r) : Prop where
  /-- The same family already detects graded injectivity. -/
  toIsAcyclicMonoTestFamilyForIsGradedInjective :
    IsAcyclicMonoTestFamilyForIsGradedInjective 𝒜 ℳ ℳ' ι
  /-- K-injectivity of the underlying cochain complex together with graded injectivity is
  equivalent to lifting against every map in the family. -/
  kInjective_and_gradedInjective_iff :
    ∀ ℐ : DGModA 𝒜,
      (ℐ.toComplex.IsKInjective ∧
        _root_.DifferentialGradedModule.IsGradedInjective (forgetToGraded 𝒜) ℐ) ↔
          ∀ r (f : ℳ r ⟶ ℐ), ∃ g : ℳ' r ⟶ ℐ, ι r ≫ g = f

/-- Any K-injective-and-graded-injective test family is in particular a graded-injective test
family. -/
@[stacks 0FSY]
instance instIsAcyclicMonoTestFamilyForIsGradedInjective
    (𝒜 : DGAO) {R : Type _} {ℳ ℳ' : R → DGModA 𝒜} {ι : ∀ r, ℳ r ⟶ ℳ' r}
    [h : IsAcyclicMonoTestFamilyForIsKInjectiveAndIsGradedInjective 𝒜 ℳ ℳ' ι] :
    IsAcyclicMonoTestFamilyForIsGradedInjective 𝒜 ℳ ℳ' ι :=
  h.toIsAcyclicMonoTestFamilyForIsGradedInjective

/-- Lemma 24.25.11: there exists a set-indexed family of injective maps between acyclic
differential graded modules on a ringed site that detects the conjunction of K-injectivity of the
underlying cochain complex and graded injectivity by the extension property. -/
@[stacks 0FSY]
theorem exists_acyclicMonoTestFamily_for_isKInjective_and_isGradedInjective
    (𝒜 : DGAO) :
    ∃ (R : Type _) (ℳ ℳ' : R → DGModA 𝒜) (ι : ∀ r, ℳ r ⟶ ℳ' r),
      IsAcyclicMonoTestFamilyForIsKInjectiveAndIsGradedInjective 𝒜 ℳ ℳ' ι := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
