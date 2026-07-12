import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomotopyCategory

open CategoryTheory
open ComplexShape

universe u

namespace ModuleCat

/-- Chapter 22 owner for differential graded `A`-modules, modeled as cochain complexes of
`A`-modules. -/
abbrev DGMod (A : Type u) [Ring A] := CochainComplex (ModuleCat A) ℤ

/-- Chapter 22 owner for `K(Mod_(A,d))`, modeled as the homotopy category of cochain complexes of
`A`-modules. -/
abbrev KDGMod (A : Type u) [Ring A] := HomotopyCategory (ModuleCat A) (up ℤ)

end ModuleCat
