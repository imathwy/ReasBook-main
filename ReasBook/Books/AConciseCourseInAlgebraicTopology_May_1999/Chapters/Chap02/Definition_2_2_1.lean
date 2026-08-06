import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/- Definition 2.2.1: a covariant functor from `C` to `D` is the canonical mathlib notion
`C ⥤ D` (equivalently, `CategoryTheory.Functor C D`), with an object map, a morphism map, and
axioms expressing preservation of identity morphisms and composition. -/
#check (C ⥤ D)

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- A functor assigns to each object `X` of `C` an object `F.obj X` of `D`. -/
recall CategoryTheory.Functor.obj (F : C ⥤ D) (X : C) : D

/- A functor assigns to each morphism `f : X ⟶ Y` a morphism `F.map f : F.obj X ⟶ F.obj Y`. -/
recall CategoryTheory.Functor.map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    F.obj X ⟶ F.obj Y

/- A functor preserves identity morphisms. -/
recall CategoryTheory.Functor.map_id (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X)

/- A functor preserves composition of morphisms. -/
recall CategoryTheory.Functor.map_comp (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g
