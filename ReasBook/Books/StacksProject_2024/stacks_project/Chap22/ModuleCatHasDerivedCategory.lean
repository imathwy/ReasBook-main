import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat

/-- The standard derived-category structure on `ModuleCat A`. This is the canonical Chapter 22
instance for passing from cochain complexes of `A`-modules to `DerivedCategory (ModuleCat A)`. -/
instance hasDerivedCategory (A : Type u) [Ring A] : HasDerivedCategory (ModuleCat A) :=
  HasDerivedCategory.standard (ModuleCat A)

end ModuleCat
