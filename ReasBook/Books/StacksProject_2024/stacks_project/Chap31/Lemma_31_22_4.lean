import Mathlib
import StacksProject_2024.Chap31.Definition_31_21_1
import StacksProject_2024.Chap31.Definition_31_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners `Flat`,
-- `LocallyOfFinitePresentation`, and `IsImmersion`; local Chapter 31 precedent fixes the source
-- hypothesis as `RelativeQuasiRegularImmersion f i`, the conclusion as `IsRegularImmersion i`,
-- and the base-changed immersion as `pullback.snd i (pullback.fst f g)`.

/-- Lemma 31.22.4 (1): if `X ⟶ S` is flat and locally of finite presentation and
`i : Z ⟶ X` is a relative quasi-regular immersion over `S`, then `i` is a regular immersion. -/
@[stacks 063U]
theorem RelativeQuasiRegularImmersion.isRegularImmersion_of_flat_locallyOfFinitePresentation
    {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [Flat f] [LocallyOfFinitePresentation f] [RelativeQuasiRegularImmersion f i] :
    IsRegularImmersion i := sorry

/-- Lemma 31.22.4 (2): under the hypotheses of part (1), after any base change
`g : S' ⟶ S` the induced immersion
`pullback.snd i (pullback.fst f g) : pullback i (pullback.fst f g) ⟶ pullback f g`
is again a regular immersion. -/
@[stacks 063U]
theorem RelativeQuasiRegularImmersion.isRegularImmersion_pullback_snd_of_flat_locallyOfFinitePresentation
    {X S S' Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
    [Flat f] [LocallyOfFinitePresentation f] [RelativeQuasiRegularImmersion f i]
    (g : S' ⟶ S) :
    IsRegularImmersion (pullback.snd i (pullback.fst f g)) := sorry

end AlgebraicGeometry
