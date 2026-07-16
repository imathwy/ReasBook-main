import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical owners `Scheme.IsQuasiAffine`,
`QuasiSeparated`, and `QuasiSeparatedSpace`. Local Chapter 29 precedent fixes the source-facing
morphism predicate as `QuasiAffineHom`, so the item is recorded as the relative-over-`S` theorem
and its absolute quasi-affine/quasi-separated scheme corollary. -/

/-- Lemma 29.13.8 (1): if `g : X ⟶ Y` is a morphism over `S`, `X` is quasi-affine over `S`,
and `Y` is quasi-separated over `S`, then `g` is quasi-affine. -/
@[stacks 054G]
theorem QuasiAffineHom.of_over_quasiSeparated
    {X Y S : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S} {g : X ⟶ Y}
    (w : g ≫ y = x) (hx : QuasiAffineHom x) (hy : QuasiSeparated y) :
    QuasiAffineHom g := sorry

/-- Lemma 29.13.8 (2): any morphism from a quasi-affine scheme to a quasi-separated scheme is
quasi-affine. -/
@[stacks 054G]
theorem Scheme.IsQuasiAffine.quasiAffineHom_of_quasiSeparated
    {X Y : Scheme.{u}} (g : X ⟶ Y) (hX : X.IsQuasiAffine) [QuasiSeparatedSpace Y] :
    QuasiAffineHom g := sorry

end AlgebraicGeometry
