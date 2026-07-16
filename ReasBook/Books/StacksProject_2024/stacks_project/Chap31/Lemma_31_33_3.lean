import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_33_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall note: semantic MCP search was unavailable in this environment; local Chapter 29
-- and Chapter 31 precedent fixes the pointwise flatness owners as `Scheme.Hom.flatAt` and
-- `Scheme.Modules.flatOverAt`, while the strict-transform owner is `strictTransformModule` /
-- `strictTransform` along the exceptional divisor `I.comap b` of a blowup.

namespace Scheme.Modules

/-- Lemma 31.33.3 (2): let `b : S' ⟶ S` be the blowup of `S` in the center defined by `I`, and
let `f : X ⟶ S` be a morphism of schemes. If a quasi-coherent `\mathcal O_X`-module `ℱ` is flat
over `S` at every point of `X` lying over the center `I.support`, then its strict transform along
the exceptional divisor is equal to the pullback module on `X ×_S S'`. -/
@[stacks 080F]
theorem strictTransformModule_eq_pullback_of_flatOverAt_over_center
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hflat : ∀ x : X, f.base x ∈ I.support → flatOverAt ℱ f x) :
    strictTransformModule b (I.comap b) f ℱ =
      (Scheme.Modules.pullback (pullback.fst f b)).obj ℱ := sorry

end Scheme.Modules

/-- Lemma 31.33.3 (1): let `b : S' ⟶ S` be the blowup of `S` in the center defined by `I`, and
let `f : X ⟶ S` be a morphism of schemes. If `X` is flat over `S` at every point of `X` lying
over the center `I.support`, then the strict transform of `X` along the exceptional divisor is
equal to the base change `X ×_S S'`. -/
@[stacks 080F]
theorem strictTransform_eq_pullback_of_flatAt_over_center
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (hflat : ∀ x : X, f.base x ∈ I.support → Scheme.Hom.flatAt f x) :
    strictTransform b (I.comap b) f = pullback f b := sorry

end AlgebraicGeometry
