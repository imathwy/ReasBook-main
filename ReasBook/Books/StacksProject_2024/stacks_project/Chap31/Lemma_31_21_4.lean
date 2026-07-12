import Mathlib
import StacksProject_2024.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section

variable {X X' Z : Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X)

-- Semantic recall: `lean_leansearch` only surfaced generic flat/base-change regular-sequence API.
-- The scheme-level owner was verified locally from `Definition_31_21_1`, and Chapter 29/31
-- base-change precedent fixes the source-facing base-changed morphism as `pullback.snd i f`.

/-- Lemma 31.21.4 (1): flat base change of a regular immersion is a regular immersion. -/
@[stacks 067P]
theorem isRegularImmersion_pullback_snd [IsRegularImmersion i] [Flat f] :
    IsRegularImmersion (pullback.snd i f) := sorry

/-- Any flat base change of a regular immersion is a regular immersion. -/
instance instIsRegularImmersionPullbackSnd [IsRegularImmersion i] [Flat f] :
    IsRegularImmersion (pullback.snd i f) :=
  isRegularImmersion_pullback_snd i f

/-- Lemma 31.21.4 (2): flat base change of a Koszul-regular immersion is a
Koszul-regular immersion. -/
@[stacks 067P]
theorem isKoszulRegularImmersion_pullback_snd [IsKoszulRegularImmersion i] [Flat f] :
    IsKoszulRegularImmersion (pullback.snd i f) := sorry

/-- Any flat base change of a Koszul-regular immersion is a Koszul-regular immersion. -/
instance instIsKoszulRegularImmersionPullbackSnd [IsKoszulRegularImmersion i] [Flat f] :
    IsKoszulRegularImmersion (pullback.snd i f) :=
  isKoszulRegularImmersion_pullback_snd i f

/-- Lemma 31.21.4 (3): flat base change of an `H_1`-regular immersion is an
`H_1`-regular immersion. -/
@[stacks 067P]
theorem isH1RegularImmersion_pullback_snd [IsH1RegularImmersion i] [Flat f] :
    IsH1RegularImmersion (pullback.snd i f) := sorry

/-- Any flat base change of an `H_1`-regular immersion is an `H_1`-regular immersion. -/
instance instIsH1RegularImmersionPullbackSnd [IsH1RegularImmersion i] [Flat f] :
    IsH1RegularImmersion (pullback.snd i f) :=
  isH1RegularImmersion_pullback_snd i f

/-- Lemma 31.21.4 (4): flat base change of a quasi-regular immersion is a
quasi-regular immersion. -/
@[stacks 067P]
theorem isQuasiRegularImmersion_pullback_snd [IsQuasiRegularImmersion i] [Flat f] :
    IsQuasiRegularImmersion (pullback.snd i f) := sorry

/-- Any flat base change of a quasi-regular immersion is a quasi-regular immersion. -/
instance instIsQuasiRegularImmersionPullbackSnd [IsQuasiRegularImmersion i] [Flat f] :
    IsQuasiRegularImmersion (pullback.snd i f) :=
  isQuasiRegularImmersion_pullback_snd i f

end

end AlgebraicGeometry
