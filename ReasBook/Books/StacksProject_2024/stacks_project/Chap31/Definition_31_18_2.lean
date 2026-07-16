import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_6

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

open CategoryTheory
open Scheme.IdealSheafData

-- Semantic recall: the Chapter 31 source-facing owner for effective Cartier divisors on ideal
-- sheaf data is already `IsEffectiveCartierDivisor D`, while mathlib provides the scheme-level
-- flatness owner `Flat (g : X ⟶ Y)` and the closed subscheme inclusion `D.subschemeι`.

section

variable {X S : Scheme.{u}}
variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- Definition 31.18.2: for a morphism of schemes `f : X ⟶ S`, a relative effective Cartier
divisor on `X/S` is an effective Cartier divisor `D ⊆ X` whose induced morphism `D ⟶ S` is flat. -/
@[stacks 062T, mk_iff]
class IsRelativeEffectiveCartierDivisor (f : X ⟶ S) (D : X.IdealSheafData) : Prop
    extends D.IsEffectiveCartierDivisor, Flat (D.subschemeι ≫ f)

end

end AlgebraicGeometry
