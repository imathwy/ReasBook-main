import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y Y' : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `AlgebraicGeometry.QuasiCompact` and the base-change API around it. Nearby Chapter 29 precedent
-- uses `Surjective` for surjectivity and `pullback.snd f g` for the base-changed morphism.

/-- Lemma 29.23.6: let `f : X ⟶ Y` be a morphism of schemes and let `g : Y' ⟶ Y` be open and
surjective. If the base change `pullback.snd f g : pullback f g ⟶ Y'` is quasi-compact, then `f`
is quasi-compact. -/
@[stacks 04ZE]
theorem quasiCompact_of_isOpenMap_of_surjective_baseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg_open : IsOpenMap g.base) [Surjective g]
    (hqc : QuasiCompact (pullback.snd f g)) :
    QuasiCompact f := sorry

end AlgebraicGeometry
