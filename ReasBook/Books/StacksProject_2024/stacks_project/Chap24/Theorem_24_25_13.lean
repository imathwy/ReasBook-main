import Mathlib
import StacksProject_2024.stacks_project.Chap24.Definition_24_13_1
import StacksProject_2024.stacks_project.Chap24.Definition_24_25_2
import StacksProject_2024.stacks_project.Chap24.Lemma_24_13_2

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

-- Semantic search note: `lean_leansearch` surfaced the generic owners `QuasiIso` and
-- `CochainComplex.IsKInjective`; the source-facing statement below is therefore anchored to the
-- local Chapter 24 dg-module owner `DGModA`, the forgetful functor `forgetToGraded`, and the
-- ringed-site ambient context already used in `Lemma_24_25_11` and `Lemma_24_25_12`.

namespace DifferentialGradedModule

/-- A differential graded module whose underlying graded module is injective and whose underlying
cochain complex is K-injective. -/
@[stacks 0FT0]
class IsKInjectiveAndIsGradedInjective (𝒜 : DGAO) (ℐ : DGModA 𝒜) : Prop where
  /-- The underlying graded module is injective. -/
  isGradedInjective :
    _root_.DifferentialGradedModule.IsGradedInjective (forgetToGraded 𝒜) ℐ
  /-- The underlying cochain complex is K-injective. -/
  isKInjective : ℐ.toComplex.IsKInjective

/-- Theorem 24.25.13: for a ringed site `(\mathcal C, \mathcal O)` and a sheaf of differential
graded algebras `(\mathcal A, \mathrm d)` on it, there is a functorial assignment
`\mathcal M \mapsto \mathcal I(\mathcal M)` together with a quasi-isomorphism
`\mathcal M \to \mathcal I(\mathcal M)` such that every `\mathcal I(\mathcal M)` is graded
injective and K-injective. -/
@[stacks 0FT0]
theorem exists_functorial_quasiIso_to_isGradedInjective_and_isKInjective
    (𝒜 : DGAO) :
    ∃ (I : DGModA 𝒜 ⥤ DGModA 𝒜) (η : 𝟭 (DGModA 𝒜) ⟶ I),
      ∀ ℳ : DGModA 𝒜,
        QuasiIso (η.app ℳ).toCochainMap ∧
          IsKInjectiveAndIsGradedInjective 𝒜 (I.obj ℳ) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
