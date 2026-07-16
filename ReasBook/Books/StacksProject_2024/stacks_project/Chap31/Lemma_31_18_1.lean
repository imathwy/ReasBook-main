import Mathlib
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import StacksProject_2024.stacks_project.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced mathlib's base-change stability API for
-- `AlgebraicGeometry.Flat`, and local Chapter 31 precedent fixes the divisor owner as
-- `X.IdealSheafData` with pullback `Scheme.IdealSheafData.comap`. For `f : X ⟶ S` and
-- `g : S' ⟶ S`, the base-changed divisor is therefore `D.comap (pullback.fst f g)` on
-- `pullback f g`, while the induced map to the new base is `pullback.snd f g`.

/-- Lemma 31.18.1: if `D ⊆ X` is a relative effective Cartier divisor over `S`, then for every
base change `g : S' ⟶ S` the inverse-image divisor on `X' = S' ×_S X`, represented here as
`D.comap (pullback.fst f g)` on `pullback f g`, is an effective Cartier divisor. -/
theorem IsRelativeEffectiveCartierDivisor.isEffectiveCartierDivisor_comap_pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D] :
    IsEffectiveCartierDivisor (D.comap (pullback.fst f g)) := sorry

/-- Companion for Lemma 31.18.1: after base change along `g : S' ⟶ S`, the pulled-back divisor is
again relative effective Cartier over the new base morphism `pullback.snd f g`. -/
theorem IsRelativeEffectiveCartierDivisor.comap_pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D] :
    IsRelativeEffectiveCartierDivisor (pullback.snd f g) (D.comap (pullback.fst f g)) := sorry

end AlgebraicGeometry
