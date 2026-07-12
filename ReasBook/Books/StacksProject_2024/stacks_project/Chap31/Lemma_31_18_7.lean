import Mathlib
import StacksProject_2024.Chap29.Definition_29_25_1
import StacksProject_2024.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` pointed to `AlgebraicGeometry.Flat.iff_flat_stalkMap`; local
-- Chapter 29 precedent packages pointwise flatness through the canonical owner
-- `Scheme.Hom.flatAt`, so the source hypothesis outside `D.support` is stated at that layer while
-- the conclusion remains the scheme-level owner `Flat`.

open Scheme.Hom

section

variable {X S : Scheme.{u}}
variable [CategoryTheory.MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- Lemma 31.18.7: let `f : X ⟶ S` be a morphism of schemes and let `D ⊆ X` be a relative
effective Cartier divisor on `X/S`. If every stalk map of `f` is flat at points of `X \ D`,
represented here as points outside `D.support`, then `f` is flat. -/
@[stacks 062W]
theorem IsRelativeEffectiveCartierDivisor.flat_of_flatAt_outside_support
    (f : X ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D]
    (hflat : ∀ x : X, x ∉ D.support → Scheme.Hom.flatAt f x) :
    Flat f := sorry

/-- Companion to Lemma 31.18.7: under the same outside-support flatness hypothesis, `f` is flat
at every point of `X`. This keeps the source-facing hypothesis while exposing the canonical
pointwise flatness conclusion used elsewhere in the repository. -/
theorem IsRelativeEffectiveCartierDivisor.flatAt_of_flatAt_outside_support
    (f : X ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D]
    (hflat : ∀ x : X, x ∉ D.support → Scheme.Hom.flatAt f x) (x : X) :
    Scheme.Hom.flatAt f x := by
  exact
    (Scheme.Hom.flat_iff_forall_flatAt f).1
      (IsRelativeEffectiveCartierDivisor.flat_of_flatAt_outside_support f D hflat) x

end

end AlgebraicGeometry
