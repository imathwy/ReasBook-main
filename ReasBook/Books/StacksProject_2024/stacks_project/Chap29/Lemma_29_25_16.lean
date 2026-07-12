import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y V : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-theoretic-image owner
-- `Scheme.Hom.image`, the ideal-sheaf datum `Scheme.Hom.ker`, the pullback ideal operation
-- `Scheme.IdealSheafData.comap`, and flatness as `AlgebraicGeometry.Flat`. Local Chapter 29
-- base-change files use `pullback.snd g f` for the projection `V ×_Y X ⟶ X`.

/-- Lemma 29.25.16: if `f : X ⟶ Y` is flat and `g : V ⟶ Y` is quasi-compact, then the
scheme-theoretic image of the base change `V ×_Y X ⟶ X` is the inverse image of the
scheme-theoretic image of `g`. The inverse image of the closed subscheme
`Scheme.Hom.image g` is represented by the comapped kernel ideal `g.ker.comap f`. -/
@[stacks 081I]
theorem schemeTheoreticImage_pullback_snd_eq_comap_of_flat
    (f : X ⟶ Y) [Flat f] (g : V ⟶ Y) [QuasiCompact g] :
    Scheme.Hom.image (pullback.snd g f) = (g.ker.comap f).subscheme := sorry

end

end AlgebraicGeometry
