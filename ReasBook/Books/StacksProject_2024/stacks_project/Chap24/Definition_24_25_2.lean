import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe uDG vDG uGr vGr

/- Semantic search note: `lean_leansearch` is unavailable in this environment, so the owner choice
was checked against local Chapter 24 precedent (`Definition_24_21_1`) and the filtered analogue
`CategoryTheory.IsFilteredInjective` from Chapter 13. -/

namespace DifferentialGradedModule

section

variable {DGModA : Type uDG} {GrModA : Type uGr}
variable [Category.{vDG} DGModA] [Category.{vGr} GrModA]

/-- Definition 24.25.2: for a fixed forgetful functor from differential graded `\mathcal A`-modules
to graded `\mathcal A`-modules, a differential graded `\mathcal A`-module `\mathcal I` is graded
injective if its underlying graded `\mathcal A`-module is an injective object of the category of
graded `\mathcal A`-modules. -/
class IsGradedInjective
    (forgetToGraded : DGModA ⥤ GrModA) (ℐ : DGModA) : Prop where
  /-- The underlying graded `\mathcal A`-module of a graded-injective differential graded module is
  injective. -/
  injective : Injective (forgetToGraded.obj ℐ)

attribute [instance] IsGradedInjective.injective

/-- If the underlying graded module is injective, then the differential graded module is graded
injective. -/
instance instIsGradedInjectiveOfInjective
    (forgetToGraded : DGModA ⥤ GrModA) (ℐ : DGModA)
    [Injective (forgetToGraded.obj ℐ)] :
    IsGradedInjective forgetToGraded ℐ where
  injective := inferInstance

/-- Unfolding graded injectivity says exactly that the underlying graded module is injective. -/
theorem isGradedInjective_iff_injective
    (forgetToGraded : DGModA ⥤ GrModA) (ℐ : DGModA) :
    IsGradedInjective forgetToGraded ℐ ↔ Injective (forgetToGraded.obj ℐ) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end

end DifferentialGradedModule
