import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Widesubcategory
import StacksProject_2024.stacks_project.Chap22.Definition_22_25_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe w v u

namespace GradedCategory

section

open Limits
open scoped GradedCategory

variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]
variable [GradedCategory R C]

/- Source/core/bridge triage for Definition 22.25.3:
- source-facing: `GradedCategory.DegreeZero`, the category `𝒜^0` with the same objects as `𝒜`
  and degree-`0` morphisms;
- core/canonical: the ambient `WideSubcategory` cut out by the degree-`0` morphism property;
- bridge/view: the canonical `wideSubcategoryInclusion` from `𝒜^0` into `𝒜`. -/

/-- The morphism property of lying in the degree-`0` graded piece of a graded category. -/
def degreeZeroMorphismProperty : MorphismProperty C :=
  fun X Y f ↦ f ∈ (Hom^0(X, Y) : Submodule R (X ⟶ Y))

/-- A morphism satisfies `degreeZeroMorphismProperty` exactly when it lies in the degree-`0`
graded piece. -/
@[simp] theorem degreeZeroMorphismProperty_iff {X Y : C} {f : X ⟶ Y} :
    degreeZeroMorphismProperty f ↔ f ∈ (Hom^0(X, Y) : Submodule R (X ⟶ Y)) :=
  Iff.rfl

/-- The degree-`0` morphisms in a graded category are closed under identities and composition. -/
instance instIsMultiplicativeDegreeZeroMorphismProperty :
    MorphismProperty.IsMultiplicative (degreeZeroMorphismProperty : MorphismProperty C) where
  id_mem X := by
    simpa using GradedCategory.id_mem_homDegree_zero X
  comp_mem _f _g hf hg := by
    simpa using GradedCategory.comp_mem hf hg

/-- Definition 22.25.3: for a graded category `𝒜` over `R`, `𝒜^0` is the category with the same
objects as `𝒜` and with morphisms given by the degree-`0` graded piece
`Hom_{𝒜^0}(X, Y) = Hom^0_𝒜(X, Y)`. -/
@[stacks 09ML]
abbrev DegreeZero (C : Type u) [Category.{v} C] [Preadditive C] [GradedCategory R C] : Type u :=
  WideSubcategory (degreeZeroMorphismProperty : MorphismProperty C)

/- Lean surface notation for the source-facing degree-zero category `𝒜^0`. -/
scoped notation:max C:max "^0" => GradedCategory.DegreeZero C

namespace DegreeZero

/-- A morphism in the degree-`0` category is, by definition, a degree-`0` morphism in the ambient
graded category. -/
@[simp] theorem hom_mem_homDegree_zero
    {X Y : C^0} (f : X ⟶ Y) :
    f.hom ∈ (Hom^0(X.obj, Y.obj) : Submodule R (X.obj ⟶ Y.obj)) :=
  f.property

/-- The degree-`0` category has the canonical zero morphisms induced by the degree-`0` submodule. -/
instance instHasZeroMorphisms :
    Limits.HasZeroMorphisms (C^0) where
  zero X Y :=
    ⟨0, by
      simpa using
        (show (0 : X.obj ⟶ Y.obj) ∈
            (Hom^0(X.obj, Y.obj) : Submodule R (X.obj ⟶ Y.obj)) from
          Submodule.zero_mem _)⟩
  comp_zero := by
    intro X Y f Z
    apply WideSubcategory.hom_ext
    change f.hom ≫ (0 : Y.obj ⟶ Z.obj) = (0 : X.obj ⟶ Z.obj)
    exact Limits.comp_zero
  zero_comp := by
    intro X Y Z f
    apply WideSubcategory.hom_ext
    change (0 : X.obj ⟶ Y.obj) ≫ f.hom = (0 : X.obj ⟶ Z.obj)
    exact Limits.zero_comp

end DegreeZero

end

end GradedCategory

end CategoryTheory
