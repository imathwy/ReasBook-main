import Mathlib
import StacksProject_2024.Chap31.Definition_31_33_1
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.subscheme` /
-- `subschemeι` and the local Chapter 31 files fix the source-facing owners as `IsBlowup`,
-- `strictTransform`, and `strictTransformModule`.

/-- Lemma 31.33.2 (1): in the situation of Definition 31.33.1, if `b : S' ⟶ S`
is the blowup of `S` in the closed subscheme defined by `I`, then the strict transform of
`X` carries the structure of the blowup of `X` in the inverse-image closed subscheme
`I.comap f`, compatibly with the map to `S'`. -/
@[stacks 080E]
theorem strictTransform_exists_isBlowup
    {S S' X : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) :
    ∃ (π : strictTransform b (I.comap b) f ⟶ X) (g : strictTransform b (I.comap b) f ⟶ S'),
      π ≫ f = g ≫ b ∧ IsBlowup π (I.comap f) := sorry

namespace Scheme.Modules

/-- Lemma 31.33.2 (2): in the situation of Definition 31.33.1, for a quasi-coherent
`\mathcal O_X`-module `ℱ`, its strict transform along the blowup `b : S' ⟶ S` is the pushforward
to `X ×_S S'` of the strict transform of `ℱ` relative to the blowup `π : X' ⟶ X`. -/
@[stacks 080E]
theorem strictTransformModule_eq_pushforward_relativeStrictTransform
    {S S' X X' : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (f : X ⟶ S) (π : X' ⟶ X) [IsBlowup π (I.comap f)]
    (g : X' ⟶ S') (h : π ≫ f = g ≫ b)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (strictTransformModule b (I.comap b) f ℱ : (Limits.pullback f b).Modules) =
      ((Scheme.Modules.pushforward
        (Limits.pullback.map (𝟙 X) π f b (𝟙 X) g f rfl h)).obj
        (strictTransformModule π ((I.comap f).comap π) (𝟙 X) ℱ)
        : (Limits.pullback f b).Modules) := sorry

end Scheme.Modules

end AlgebraicGeometry
