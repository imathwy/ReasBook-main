import Mathlib

open Polynomial

universe u

-- Declarations for this item will be appended below by the statement pipeline.

variable {K : Type u} [Field K]

/- Definition 1.4.40: for a polynomial `P : K[X]`, its splitting field is the canonical field
extension `P.SplittingField`, namely the smallest field extension of `K` over which `P` splits. -/
recall SplittingField (P : K[X]) : Type u
