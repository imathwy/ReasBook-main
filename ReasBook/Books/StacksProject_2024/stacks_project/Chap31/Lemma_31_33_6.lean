import Mathlib
import StacksProject_2024.Chap31.Definition_31_33_1
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support` and
-- `Scheme.IdealSheafData.subscheme`; local Chapter 31 precedent records blowups by `IsBlowup`
-- and strict transforms by `strictTransform` / `Scheme.Modules.strictTransformModule`.

namespace Scheme.Modules

/-- Lemma 31.33.6 (1): if `b : S' ⟶ S` is the blowup in `Z`, `b' : S'' ⟶ S'`
is the blowup in `Z'`, the center `Y` has underlying set `Z ∪ b(Z')`, and the composite
`b' ≫ b` is the blowup of `S` in `Y`, then the strict transform of a quasi-coherent
module along the composite blowup agrees, after the canonical pullback-associativity transport,
with the strict transform obtained by first transforming along `b` and then along `b'`. -/
@[stacks 080I]
theorem strictTransformModule_eq_pushforward_iteratedStrictTransformModule_of_support_eq_union_image
    {S S' S'' X : Scheme.{u}} (Z : S.IdealSheafData)
    (b : S' ⟶ S) [IsBlowup b Z]
    (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [IsBlowup b' Z']
    (Y : S.IdealSheafData)
    (hY : (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S'))
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (α : Limits.pullback (Limits.pullback.snd f b) b' ⟶ Limits.pullback f (b' ≫ b))
    (hα_fst : α ≫ Limits.pullback.fst f (b' ≫ b) =
      Limits.pullback.fst (Limits.pullback.snd f b) b' ≫ Limits.pullback.fst f b)
    (hα_snd : α ≫ Limits.pullback.snd f (b' ≫ b) =
      Limits.pullback.snd (Limits.pullback.snd f b) b')
    [IsIso α] :
    strictTransformModule (b' ≫ b) (Y.comap (b' ≫ b)) f ℱ =
      (Scheme.Modules.pushforward α).obj
        (strictTransformModule b' (Z'.comap b') (Limits.pullback.snd f b)
          (strictTransformModule b (Z.comap b) f ℱ)) := sorry

end Scheme.Modules

/-- Lemma 31.33.6 (2): in the same situation, the strict transform of a scheme `X` over `S`
along the composite blowup `b' ≫ b` is the iterated strict transform obtained by first
transforming `X` along `b` and then transforming that strict transform along `b'`. The morphism
`g` records the canonical structure of the first strict transform as a scheme over `S'`. -/
@[stacks 080I]
theorem strictTransform_eq_iteratedStrictTransform_of_support_eq_union_image
    {S S' S'' X : Scheme.{u}} (Z : S.IdealSheafData)
    (b : S' ⟶ S) [IsBlowup b Z]
    (Z' : S'.IdealSheafData) (b' : S'' ⟶ S') [IsBlowup b' Z']
    (Y : S.IdealSheafData)
    (hY : (Y.support : Set S) = (Z.support : Set S) ∪ b.base '' (Z'.support : Set S'))
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ S)
    (π : strictTransform b (Z.comap b) f ⟶ X)
    (g : strictTransform b (Z.comap b) f ⟶ S')
    (hπg : π ≫ f = g ≫ b) [IsBlowup π (Z.comap f)] :
    strictTransform (b' ≫ b) (Y.comap (b' ≫ b)) f =
      strictTransform b' (Z'.comap b') g := sorry

end AlgebraicGeometry
