import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open Scheme.Hom

section

variable {X S : Scheme.{u}}
variable [CategoryTheory.MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- Lemma 31.18.5: if `D` is a relative effective Cartier divisor on `X/S`, if `x` lies in the
support of `D`, and if the local ring `\mathcal O_{X, x}` is Noetherian, then `f` is flat at
`x`. Here the source condition `x ∈ D` is represented by `x ∈ D.support`. -/
theorem IsRelativeEffectiveCartierDivisor.flatAt_of_mem_support
    (f : X ⟶ S) (D : X.IdealSheafData) (x : X)
    [IsRelativeEffectiveCartierDivisor f D] [IsNoetherianRing (X.presheaf.stalk x)]
    (hx : x ∈ D.support) :
    Scheme.Hom.flatAt f x := sorry

/-- Companion bridge to Lemma 31.18.5: under the same hypotheses, the induced stalk map on local
rings is flat. Here the source condition `x ∈ D` is represented by `x ∈ D.support`. -/
theorem IsRelativeEffectiveCartierDivisor.stalkMap_flat_of_mem_support
    (f : X ⟶ S) (D : X.IdealSheafData) (x : X)
    [IsRelativeEffectiveCartierDivisor f D] [IsNoetherianRing (X.presheaf.stalk x)]
    (hx : x ∈ D.support) :
    (f.stalkMap x).hom.Flat := by
  simpa [Scheme.Hom.flatAt] using
    (IsRelativeEffectiveCartierDivisor.flatAt_of_mem_support f D x hx)

end

end AlgebraicGeometry
