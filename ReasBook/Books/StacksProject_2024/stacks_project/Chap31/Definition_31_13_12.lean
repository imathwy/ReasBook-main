import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

universe u

variable {S S' : Scheme.{u}}
variable [MonoidalCategory (RingedSpace.Modules S'.toRingedSpace)]

-- Semantic recall: the Chapter 31 owner for effective Cartier divisors on
-- `S.IdealSheafData` is `IsEffectiveCartierDivisor`. The affine-local
-- nonzerodivisor criterion appears in `Lemma_31_13_2` as a source-facing
-- characterization of that owner. This file only introduces the source-facing
-- pullback-definedness notion from Definition 31.13.12.

/-- Definition 31.13.12: if `D` is an effective Cartier divisor on `S`, then the pullback of `D`
by `f : S' ⟶ S` is defined exactly when the inverse-image closed subscheme `f^{-1}(D)` is an
effective Cartier divisor on `S'`. -/
abbrev pullbackDefined (D : S.IdealSheafData) (f : S' ⟶ S) : Prop :=
  IsEffectiveCartierDivisor (D.comap f)

/-- The pullback of an effective Cartier divisor is defined exactly when the inverse-image closed
subscheme is an effective Cartier divisor. -/
theorem pullbackDefined_iff (D : S.IdealSheafData) (f : S' ⟶ S) :
    pullbackDefined D f ↔ IsEffectiveCartierDivisor (D.comap f) :=
  Iff.rfl

end Scheme.IdealSheafData

end AlgebraicGeometry
