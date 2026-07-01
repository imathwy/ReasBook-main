import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic

open CategoryTheory Limits CommRingCat
open IsLocalization.Away

universe u

namespace CategoryTheory
namespace IsPullback

section

variable {R R' B B' Bg Rf Bh Rh : Type u}
variable [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
variable [CommRing Bg] [CommRing Rf] [CommRing Bh] [CommRing Rh]
variable {s : B →+* R} {t : R' →+* R} {left : B' →+* B} {right : B' →+* R'}
variable (h : B')
variable [Algebra B Bg] [IsLocalization.Away (left h) Bg]
variable [Algebra R' Rf] [IsLocalization.Away (right h) Rf]
variable [Algebra B' Bh] [IsLocalization.Away h Bh]
variable [Algebra R Rh] [IsLocalization.Away (s (left h)) Rh]

/- Domain-style sampling for Lemma 15.5.3:
- primary domain: pullback squares in `CommRingCat` together with localization-away base change;
- sampled owner API:
  `CategoryTheory.IsPullback`,
  `CategoryTheory.Under.pushout`,
  `CommRingCat.Under.preservesFiniteLimits_of_flat`,
  `CommRingCat.isPushout_of_isLocalization`;
- best owner abstraction: base change in the under-category via
  `CategoryTheory.Under.pushout`, with the public statement still phrased by the source-facing
  owner `CategoryTheory.IsPullback`;
- primitive-vs-derived split:
  primitive data: the original pullback witness
    `IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)`
    together with the localization-away instances at `h`, `left h`, `right h`, and the common
    image of `h` in `R`;
  derived API: the four localized comparison maps
    `IsLocalization.Away.map ...`, where the `R'_right(h) → R_common` map uses the pullback
    commutativity to identify `t (right h)` with `s (left h)`, obtained by base change along
    `ofHom (algebraMap B' Bh)`, and the resulting localized pullback square.

This item is therefore a `bridge/view` theorem: the canonical engine is that pushout along the
localization map `B' ⟶ B'_h` preserves finite limits because localizations are flat, while
`CommRingCat.isPushout_of_isLocalization` identifies the pushed-out objects with the usual
away-localizations. The source-facing output remains the localized `IsPullback` square. -/

/- Source/core/bridge triage for Lemma 15.5.3:
- source-facing: localizing a cartesian square of commutative rings away from an element of the
  pullback ring;
- core/canonical: `CategoryTheory.IsPullback` together with base change by
  `CategoryTheory.Under.pushout`;
- bridge/view: the localized square built from the canonical localization maps
  `IsLocalization.Away.map`, with the target-side `R'_right(h) → R_common` map derived from the
  pullback commutativity. -/

lemma away_right_of_localization_away (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s)
    (ofHom t)) : IsLocalization.Away (t (right h)) Rh := by
  have hcomm : s (left h) = t (right h) := by
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) h)
  simpa [hcomm] using (inferInstance : IsLocalization.Away (s (left h)) Rh)

/-- The canonical localized comparison map `R'[1 / right(h)] → R[1 / s(left(h))]` induced by the
pullback square. -/
noncomputable def localizationAwayRightMap
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    Rf →+* Rh :=
  letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
  IsLocalization.Away.map Rf Rh t (right h)

/-- Lemma 15.5.3: localizing a cartesian square of commutative rings away from an element of the
pullback ring again gives a cartesian square. -/
-- Proof sketch: start from the owner witness `hsq : IsPullback ...`. The localized comparison maps
-- are the canonical maps between away-localizations, with the target-side map packaged as the
-- explicit bridge `localizationAwayRightMap h hsq`. Regard the square as a pullback in
-- `Under (CommRingCat.of B')`, apply base change along `ofHom (algebraMap B' Bh)`, and use
-- `CommRingCat.Under.preservesFiniteLimits_of_flat` for the flat localization map. Finally
-- identify the pushed-out objects with the away-localizations via
-- `CommRingCat.isPushout_of_isLocalization`.
theorem localization_away
    (hsq : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t)) :
    IsPullback (ofHom (IsLocalization.Away.map Bh Bg left h))
      (ofHom (IsLocalization.Away.map Bh Rf right h))
      (ofHom (IsLocalization.Away.map Bg Rh s (left h)))
      (ofHom (localizationAwayRightMap h hsq)) := by
  letI : IsLocalization.Away (t (right h)) Rh := away_right_of_localization_away h hsq
  let base : of B' ⟶ of Bh := ofHom (algebraMap B' Bh)
  let baseChange : Under (of B') ⥤ Under (of Bh) :=
    Under.pushout base
  have hflat : RingHom.Flat (algebraMap B' Bh) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat Bh (Submonoid.powers h)
  let _ : PreservesFiniteLimits baseChange :=
    CommRingCat.Under.preservesFiniteLimits_of_flat base hflat
  -- Convert the original square to `Under (CommRingCat.of B')`, apply `IsPullback.map` to the
  -- flat base-change functor `baseChange`, and then identify the pushed-out objects with the
  -- away-localizations via the canonical localization pushout squares.
  sorry

end

end IsPullback
end CategoryTheory
