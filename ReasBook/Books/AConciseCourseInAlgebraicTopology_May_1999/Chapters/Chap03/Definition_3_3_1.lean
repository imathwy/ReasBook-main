import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall: `CategoryTheory.Under`, `Under.mk`, `Under.homMk`, and `Under.w` in
-- `Mathlib.CategoryTheory.Comma.Over.Basic` give the canonical API for categories under a fixed
-- object.

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {x : C}

/- Definition 3.3.1: the under-category `x\C` is the canonical category `Under x`, whose
objects are morphisms with source `x` and whose morphisms are commutative triangles over `x`. -/
#check Under x

section UnderApi

variable {T : Type u} [Category.{v} T]
variable {X Y : T}

/- An object of the under-category `Under X` is given by a morphism `X ⟶ Y`. -/
recall Under.mk (f : X ⟶ Y) : Under X

/- A morphism in `Under X` is a map between codomains whose triangle with the structure maps
commutes. -/
recall Under.homMk {U V : Under X} (γ : U.right ⟶ V.right)
    (hγ : U.hom ≫ γ = V.hom) : U ⟶ V

/- Every morphism in the under-category satisfies the defining commutative-triangle relation. -/
recall Under.w {U V : Under X} (γ : U ⟶ V) : U.hom ≫ γ.right = V.hom

end UnderApi

/- The under-category inherits its category structure from the canonical mathlib instance. -/
#check (inferInstance : Category (Under x))
