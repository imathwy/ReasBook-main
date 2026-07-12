import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical mathlib owners
-- `Scheme.IdealSheafData.comap` for pulling back the ideal sheaf defining a closed subscheme and
-- `Scheme.IdealSheafData.comapIso` for its canonical identification with the fibre product.

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : Y.IdealSheafData)

/- Canonical recall for the inverse-image construction: `Z.comap f` is the closed subscheme
datum on `X`, and `Scheme.IdealSheafData.comapIso` identifies it with the canonical chosen
pullback representative. -/
recall Scheme.IdealSheafData.comap
recall Scheme.IdealSheafData.comapIso

#check (Z.comap f : X.IdealSheafData)
#check (Z.comapIso f : (Z.comap f).subscheme ≅ pullback f Z.subschemeι)

/-- Definition 26.17.7: for a morphism of schemes `f : X ⟶ Y` and a closed subscheme
`Z ⊆ Y`, the source-oriented fibre product `Z ×_Y X`, mapped to `X` by its second projection,
has defining ideal sheaf the comap ideal sheaf `Z.comap f`; this is the inverse-image closed
subscheme `f^{-1}(Z)`. -/
@[stacks 01JV]
theorem inverseImageClosedSubscheme_ker_pullback_snd :
    Scheme.Hom.ker (pullback.snd Z.subschemeι f) = Z.comap f := sorry

end AlgebraicGeometry
