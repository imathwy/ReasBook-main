import Mathlib
import StacksProject_2024.stacks_project.Chap24.Definition_24_25_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w uDG vDG uGr vGr

/- Semantic search note: `lean_leansearch` is unavailable in this runner, so the owner/API choice
was checked against the local graded-injective owner `Definition_24_25_2`, the upstream-style
product recall `Chap12/Lemma_12_27_3.lean`, and the Chapter 24 product analogue
`Lemma_24_25_8.lean`. -/

namespace DifferentialGradedModule

section

variable {DGModA : Type uDG} {GrModA : Type uGr}
variable [Category.{vDG} DGModA] [Category.{vGr} GrModA]
variable (forgetToGraded : DGModA ⥤ GrModA)
variable {T : Type w} (ℐ : T → DGModA)
variable [HasProduct ℐ]
variable [HasProduct (fun t ↦ forgetToGraded.obj (ℐ t))]
variable [PreservesLimit (Discrete.functor ℐ) forgetToGraded]
variable [∀ t, IsGradedInjective forgetToGraded (ℐ t)]

/-- If the forgetful functor to graded modules preserves the product of a family of graded-injective
differential graded modules, then that product is graded injective. -/
instance instIsGradedInjectiveProduct :
    IsGradedInjective forgetToGraded (∏ᶜ ℐ) :=
  (isGradedInjective_iff_injective _ _).2 <|
    Injective.of_iso (PreservesProduct.iso forgetToGraded ℐ).symm inferInstance

/-- Lemma 24.25.4: let `(\mathcal C, \mathcal O)` be a ringed site, let `(\mathcal A, d)` be a
sheaf of differential graded algebras on it, and let `ℐ : T → \mathrm{Mod}(\mathcal A, d)` be a
family of graded-injective differential graded `\mathcal A`-modules. If the forgetful functor to
graded `\mathcal A`-modules preserves this product, then the product differential graded module is
graded injective. -/
theorem product_isGradedInjective
    : IsGradedInjective forgetToGraded (∏ᶜ ℐ) :=
  inferInstance

end

end DifferentialGradedModule
