import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_2_1 (from Chap02) -/
universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/- Definition 2.2.1: a covariant functor from `C` to `D` is the canonical mathlib notion
`C ⥤ D` (equivalently, `CategoryTheory.Functor C D`), with an object map, a morphism map, and
axioms expressing preservation of identity morphisms and composition. -/
#check (C ⥤ D)

/-! ### Definition_2_2_2 (from Chap02) -/
universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/- Definition 2.2.2: a contravariant functor from `C` to `D` is equivalently a covariant
functor from the opposite category `Cᵒᵖ` to `D`, so it reverses the direction of morphisms while
keeping the same underlying objects. -/
#check (Cᵒᵖ ⥤ D)

/-! ### Example_2_2_3 (from Chap02) -/
universe u

open CategoryTheory

/- Example 2.2.3: the forgetful functor from topological spaces to sets is a basic example of a
functor. -/
#check (forget TopCat)

/- The forgetful functor from abelian groups to sets is another basic example of a functor. -/
#check (forget AddCommGrpCat)

/- The free abelian group construction defines a functor from sets to abelian groups. -/
recall AddCommGrpCat.free : Type u ⥤ AddCommGrpCat.{u}
