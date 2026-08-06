module

import Mathlib.CategoryTheory.Category.Basic

public section

universe v u

open CategoryTheory

variable (C : Type u)

/- Definition 2.1.1: a category consists of objects, hom-sets, identity morphisms, and a
composition law satisfying the left and right unit laws and associativity. The canonical mathlib
owner for this notion is `Category.{v} C`. -/
#check (Category.{v} C : Type (max u (v + 1)))

section

variable [Category.{v} C]
variable {X Y Z W : C}

/- The underlying data layer of a category is `CategoryStruct`. -/
#check (CategoryStruct.{v} C : Type (max u (v + 1)))

/- Identity morphisms are the `CategoryStruct.id` data. -/
#check CategoryStruct.id

/- Composition is the `CategoryStruct.comp` data. -/
#check CategoryStruct.comp

/- Left unit law. -/
#check (Category.id_comp : ∀ {X Y : C} (f : X ⟶ Y), 𝟙 X ≫ f = f)

/- Right unit law. -/
#check (Category.comp_id : ∀ {X Y : C} (f : X ⟶ Y), f ≫ 𝟙 Y = f)

/- Associativity law. -/
#check (Category.assoc :
  ∀ {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h)

end
