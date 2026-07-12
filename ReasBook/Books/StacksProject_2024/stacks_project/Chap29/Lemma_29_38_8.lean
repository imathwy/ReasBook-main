import Mathlib
import StacksProject_2024.Chap29.Definition_29_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry
open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall / analogue check:
-- `lean_leansearch` surfaced `AlgebraicGeometry.Scheme.Modules.pullback` as the canonical owner
-- for pulling back quasi-coherent modules along a morphism of schemes, and generic base-change
-- stability owners for scheme-morphism properties. Local Chapter 29 precedent already fixes the
-- source-facing owner for relative very ampleness as `AlgebraicGeometry.RelativelyVeryAmple` in
-- `Definition_29_38_1`, so this item is formalized as the direct pullback-stability theorem for
-- that owner.

/-- Lemma 29.38.8: if an invertible `\mathcal O_X`-module `\mathcal L` is relatively very ample
for `f : X ⟶ S`, then for any base-change square
`X' \xrightarrow{g'} X`, `X' \xrightarrow{f'} S'`, `S' \xrightarrow{g} S`, the pulled-back module
`(g')^* \mathcal L` is relatively very ample for `f'`. -/
@[stacks 0B3F]
theorem RelativelyVeryAmple.of_isPullback
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (hpb : IsPullback g' f' f g)
    (L : X.Modules) [Scheme.Modules.Invertible L]
    [Scheme.Modules.Invertible ((Scheme.Modules.pullback g').obj L)]
    (hL : RelativelyVeryAmple f L) :
    RelativelyVeryAmple f' ((Scheme.Modules.pullback g').obj L) := sorry

end AlgebraicGeometry
