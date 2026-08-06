import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (D : Type u₁) [Category.{v₁} D]
variable (C : Type u₂) [Category.{v₂} C]
variable (F G : D ⥤ C)
variable (X : C)

/- Definition 2.6.2: a morphism of `D`-shaped diagrams is the canonical natural transformation
between functors `F G : D ⥤ C`, namely `F ⟶ G`. -/
#check (F ⟶ G)

/- A fixed object `X : C` determines the constant `D`-shaped diagram in `C`. -/
#check ((Functor.const D).obj X)

variable {D : Type u₁} [Category.{v₁} D]
variable {C : Type u₂} [Category.{v₂} C]

/- The constant `D`-shaped diagram on `X` takes every object of `D` to `X`. -/
recall Functor.const_obj_obj (X : C) (j : D) :
    ((Functor.const D).obj X).obj j = X

/- The constant `D`-shaped diagram on `X` sends every morphism of `D` to `𝟙 X`. -/
recall Functor.const_obj_map (X : C) {j j' : D} (f : j ⟶ j') :
    ((Functor.const D).obj X).map f = 𝟙 X
