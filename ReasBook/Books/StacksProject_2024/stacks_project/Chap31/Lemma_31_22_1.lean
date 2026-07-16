import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the base-change-stable ambient scheme owners
-- `Flat` and `IsImmersion`; local Chapter 31 precedent fixes the absolute owners as
-- `IsH1RegularImmersion` and `IsQuasiRegularImmersion`, and the relative owners as
-- `RelativeH1RegularImmersion` and `RelativeQuasiRegularImmersion`, while the base-changed
-- immersion into `X' = S' ×_S X` is the canonical pullback morphism
-- `pullback.snd i (pullback.fst f g)`.

/-- Lemma 31.22.1 (1): if `i : Z ⟶ X` is a relative `H_1`-regular immersion over
`f : X ⟶ S`, then after any base change `g : S' ⟶ S` the induced immersion
`pullback.snd i (pullback.fst f g) : pullback i (pullback.fst f g) ⟶ pullback f g`
is again `H_1`-regular. This is the source statement with the flatness hypothesis bundled into
`RelativeH1RegularImmersion f i`. -/
@[stacks 063R]
theorem RelativeH1RegularImmersion.h1RegularImmersion_pullback_snd
    {X S S' Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [RelativeH1RegularImmersion f i] (g : S' ⟶ S) :
    IsH1RegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

/-- Lemma 31.22.1 (2): if `i : Z ⟶ X` is a relative quasi-regular immersion over
`f : X ⟶ S`, then after any base change `g : S' ⟶ S` the induced immersion
`pullback.snd i (pullback.fst f g) : pullback i (pullback.fst f g) ⟶ pullback f g`
is again quasi-regular. This is the source statement with the flatness hypothesis bundled into
`RelativeQuasiRegularImmersion f i`. -/
@[stacks 063R]
theorem RelativeQuasiRegularImmersion.quasiRegularImmersion_pullback_snd
    {X S S' Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [RelativeQuasiRegularImmersion f i] (g : S' ⟶ S) :
    IsQuasiRegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

end AlgebraicGeometry
