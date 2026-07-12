import Mathlib
import StacksProject_2024.Chap29.Definition_29_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical direct-image owner
-- `AlgebraicGeometry.Scheme.Modules.pushforward` together with the affine-morphism owner
-- `AlgebraicGeometry.IsAffineHom`; the local flatness owner is `Scheme.Modules.flatOver`.

/-- For an affine morphism, the pushforward of a quasi-coherent module is quasi-coherent. -/
instance pushforward_obj_isQuasicoherent_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((pushforward f).obj ℱ).IsQuasicoherent := sorry

/-- Lemma 29.25.4: let `f : X ⟶ Y` be an affine morphism of schemes over a base scheme `S`. Let
`ℱ` be a quasi-coherent `\mathcal O_X`-module. Then `ℱ` is flat over `S` if and only if `f_*ℱ`
is flat over `S`. -/
@[stacks 0FLM]
theorem flatOver_iff_pushforward_flatOver_of_isAffineHom
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffineHom f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    flatOver ℱ (f ≫ g) ↔ flatOver ((Scheme.Modules.pushforward f).obj ℱ) g := sorry

end AlgebraicGeometry.Scheme.Modules
