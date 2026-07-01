import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Definition 1.1.3: an algebraic-topological invariant with values in a category `C` is modeled
by a functor from topological spaces to `C`, sending each space `X` to an object `A(X)` and each
continuous map `p : X ⟶ Y` to the induced morphism `A(p) = p_*`. -/
#check TopCat ⥤ C
