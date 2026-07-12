import Mathlib
import StacksProject_2024.Chap31.Definition_31_33_1
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical module pushforward and affine-base-
-- change owners; local Chapter 29/30/31 precedent fixes the source-facing surface here through
-- `IsBlowup`, `strictTransformModule`, and the canonical base-changed morphism
-- `Limits.pullback.map (g ≫ y) b y b g (𝟙 S') (𝟙 S) (by simp) (by simp)`.

/-- Lemma 31.33.4: let `b : S' ⟶ S` be the blowup of `S` in the center defined by `I`, let
`g : X ⟶ Y` be an affine morphism of schemes over `S`, and let `ℱ` be a quasi-coherent
`\mathcal O_X`-module. Then the pushforward of the strict transform of `ℱ` along the base change
of `g` to `S'` is the strict transform of `g_* \mathcal F`. -/
@[stacks 080G]
theorem pushforward_strictTransformModule_eq_strictTransformModule_pushforward_of_isAffineHom
    {S S' X Y : Scheme.{u}} (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
    (g : X ⟶ Y) (y : Y ⟶ S) [IsAffineHom g]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((Scheme.Modules.pushforward
        (Limits.pullback.map (g ≫ y) b y b g (𝟙 S') (𝟙 S) (by simp) (by simp))).obj
      (strictTransformModule b (I.comap b) (g ≫ y) ℱ) : (Limits.pullback y b).Modules) =
      strictTransformModule b (I.comap b) y ((Scheme.Modules.pushforward g).obj ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
