import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 2.4.3: given a homotopy relation on a category `C`, the homotopy category `hC`
is realized by the quotient category `CategoryTheory.Quotient r`, which has the same objects as
`C` and morphisms given by homotopy classes of maps. -/
recall CategoryTheory.Quotient (C : Type u) [CategoryTheory.Category.{v} C] (r : HomRel C) :
  Type u
