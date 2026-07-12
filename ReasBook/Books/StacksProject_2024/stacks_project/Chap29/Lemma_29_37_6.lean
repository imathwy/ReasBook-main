import StacksProject_2024.Chap28.Lemma_28_27_1
import StacksProject_2024.Chap29.Definition_29_13_1
import StacksProject_2024.Chap29.Definition_29_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` recalled the canonical scheme-side quasi-affine owner
`Scheme.IsQuasiAffine`; local Chapter 29 precedent uses `QuasiAffineHom` for quasi-affine
morphisms and `RelativelyAmple f L` for `f`-relatively ample invertible modules. The dependency
Lemma 28.27.1 supplies the structure-sheaf/absolute-ampleness bridge. -/

/-- Lemma 29.37.6: for a morphism of schemes `f : X ⟶ S`, the morphism `f` is quasi-affine if
and only if the structure sheaf `\mathcal O_X` is `f`-relatively ample. -/
@[stacks 0891]
theorem quasiAffineHom_iff_structureSheaf_relativelyAmple
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔ RelativelyAmple f (SheafOfModules.unit X.ringCatSheaf) := sorry

end AlgebraicGeometry
