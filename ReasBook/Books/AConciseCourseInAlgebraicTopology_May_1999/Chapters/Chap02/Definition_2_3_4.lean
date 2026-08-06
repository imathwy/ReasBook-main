import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/- Definition 2.3.4: categories `C` and `D` are equivalent via the canonical mathlib notion
`C ≌ D`, which packages a forward functor, an inverse functor, and natural isomorphisms
identifying each composite with the corresponding identity functor. -/
#check (C ≌ D)

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- An equivalence of categories has a forward functor from `C` to `D`. -/
recall Equivalence.functor

/- An equivalence of categories has an inverse functor from `D` to `C`. -/
recall Equivalence.inverse

/- The unit of an equivalence is a natural isomorphism from the identity on `C` to the composite
of the forward and inverse functors. -/
recall Equivalence.unitIso

/- The counit of an equivalence is a natural isomorphism from the composite of the inverse and
forward functors to the identity on `D`. -/
recall Equivalence.counitIso
