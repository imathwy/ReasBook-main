import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Tactic.Recall

open CategoryTheory

universe u v

variable (A : TopCat)

/-
Definition 6.5.1. For a space `A : TopCat`, the category of spaces under `A` is `Under A`.
An object of `Under A` is a map `A ⟶ X`, implemented by `Under.mk`. A morphism in `Under A`
is induced from a map of targets by `Under.homMk`, and the commuting triangle is recorded by
`Under.w`.
-/
#check Under A

variable {T : Type u} [Category.{v} T] {X Y : T}

/- An object of an under category, hence of `Under A` for spaces, is a map with fixed source. -/
recall Under.mk (f : X ⟶ Y) : Under X

/- A morphism in an under category, hence in `Under A` for spaces, is a map between targets whose
triangle with the structure maps commutes. -/
recall Under.homMk {U V : Under X} (f : U.right ⟶ V.right)
    (hf : U.hom ≫ f = V.hom) : U ⟶ V

/- Every morphism in an under category satisfies the defining commutative-triangle relation. -/
recall Under.w {U V : Under X} (f : U ⟶ V) : U.hom ≫ f.right = V.hom

/- The category of spaces under `A` inherits its category structure from the canonical instance
on the under category. -/
#check (inferInstance : Category (Under A))
