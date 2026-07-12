import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

/- Definition 2.1.1: a category consists of objects, morphism sets `C(A, B)`, identity
morphisms `id_A`, and an associative composition law satisfying the left and right unit laws. -/
recall Category (C : Type u) : Type (max u (v + 1))
