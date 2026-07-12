import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical base-change instances
-- `IsClosedImmersion.isStableUnderBaseChange`, `IsOpenImmersion.instSndScheme`, and
-- `IsImmersion.isStableUnderBaseChange`, plus the ideal-sheaf API `Scheme.Hom.ker` and
-- `Scheme.IdealSheafData.comap`.

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Lemma 26.17.6 (1): closed immersions of schemes are stable under base change: if
`f : X ⟶ S` is a closed immersion, then the projection `X ×_S Y ⟶ Y` is a closed immersion. -/
@[stacks 01JU]
theorem isClosedImmersion_pullback_snd_of_isClosedImmersion [IsClosedImmersion f] :
    IsClosedImmersion (pullback.snd f g) := sorry

/-- Lemma 26.17.6 (2): if the closed immersion `f : X ⟶ S` corresponds to an ideal sheaf `I` on
`S`, then after base change along `g : Y ⟶ S`, the projection `X ×_S Y ⟶ Y` corresponds to the
comap ideal sheaf `I.comap g`, i.e. the image of `g^* I -> O_Y`. -/
@[stacks 01JU]
theorem ker_pullback_snd_eq_comap_of_ker_eq
    [IsClosedImmersion f] (I : S.IdealSheafData) (hI : Scheme.Hom.ker f = I) :
    Scheme.Hom.ker (pullback.snd f g) = I.comap g := sorry

/-- Lemma 26.17.6 (3): open immersions of schemes are stable under base change: if
`f : X ⟶ S` is an open immersion, then the projection `X ×_S Y ⟶ Y` is an open immersion. -/
@[stacks 01JU]
theorem isOpenImmersion_pullback_snd_of_isOpenImmersion [IsOpenImmersion f] :
    IsOpenImmersion (pullback.snd f g) := sorry

/-- Lemma 26.17.6 (4): immersions of schemes are stable under base change: if `f : X ⟶ S` is an
immersion, then the projection `X ×_S Y ⟶ Y` is an immersion. -/
@[stacks 01JU]
theorem isImmersion_pullback_snd_of_isImmersion [IsImmersion f] :
    IsImmersion (pullback.snd f g) := sorry

end AlgebraicGeometry
