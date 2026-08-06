import Mathlib.CategoryTheory.Quotient
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

/- Definition 2.4.3: given a homotopy relation on a category `C`, the homotopy category `hC`
is realized by the quotient category `CategoryTheory.Quotient r`, which has the same objects as
`C` and morphisms given by homotopy classes of maps. -/
recall CategoryTheory.Quotient (C : Type u) [Category.{v} C] (r : HomRel C) : Type u

variable (C : Type u) [Category.{v} C] (r : HomRel C)

/- The quotient category has the same objects as `C`. -/
recall CategoryTheory.Quotient.equiv (r : HomRel C) : CategoryTheory.Quotient r ≃ C

/- The canonical functor `C ⥤ CategoryTheory.Quotient r` is the identity on objects and sends a
morphism to its class in the quotient. -/
recall CategoryTheory.Quotient.functor (r : HomRel C) : C ⥤ CategoryTheory.Quotient r
