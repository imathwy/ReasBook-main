import Mathlib
import stacks_project.Chap10.Definition_10_135_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Source/core/bridge triage:
* source-facing: the textbook assertions for principal localizations `S_g`;
* core/canonical: the owner classes `IsGlobalCompleteIntersection k S` and
  `IsLocalCompleteIntersection k S` from Definition `10.135.1`;
* bridge/view: permanence along an arbitrary away-localization target `Sg` with
  `[IsLocalization.Away g Sg]`, of which `Localization.Away g` is the canonical model.

The primitive data live in the owner classes from Definition `10.135.1`. This file adds only the
derived principal-localization API from Lemma `10.135.2`; the concrete ring `Localization.Away g`
is only a specialization of the intrinsic away-localization owner.
-/

namespace IsGlobalCompleteIntersection

variable {Sg : Type w} [CommRing Sg] [Algebra S Sg] [Algebra k Sg] [IsScalarTower k S Sg]

-- Proof sketch: unwrap the source-facing owner witness
-- `IsGlobalCompleteIntersection.presentation_or_subsingleton`. The subsingleton convention is
-- preserved by any away-localization target `Sg`, and a presentation witness localizes along the
-- principal open subset without changing the presentation dimension.

/-- Lemma 10.135.2 (1): if a finite type `k`-algebra `S` is a global complete intersection, then
any away localization `Sg` of `S` at `g` is again a global complete intersection. The textbook
ring `S_g` is the special case `Sg = Localization.Away g`. -/
theorem of_isLocalizationAway (g : S) (hS : IsGlobalCompleteIntersection k S)
    [IsLocalization.Away g Sg] : IsGlobalCompleteIntersection k Sg := by
  let _ : IsGlobalCompleteIntersection k S := hS
  sorry

end IsGlobalCompleteIntersection

namespace IsLocalCompleteIntersection

variable {Sg : Type w} [CommRing Sg] [Algebra S Sg] [Algebra k Sg] [IsScalarTower k S Sg]

-- Proof sketch: unwrap the owner field
-- `IsLocalCompleteIntersection.exists_basicOpen_cover`. Localizing the finite basic-open cover to
-- an arbitrary away-localization target `Sg` preserves the unit-ideal condition, and each chart
-- remains a global complete intersection by
-- `IsGlobalCompleteIntersection.of_isLocalizationAway`.

/-- Lemma 10.135.2 (2): if a finite type `k`-algebra `S` is a local complete intersection, then
any away localization `Sg` of `S` at `g` is again a local complete intersection. The textbook
ring `S_g` is the special case `Sg = Localization.Away g`. -/
theorem of_isLocalizationAway (g : S) (hS : IsLocalCompleteIntersection k S)
    [IsLocalization.Away g Sg] : IsLocalCompleteIntersection k Sg := by
  let _ : IsLocalCompleteIntersection k S := hS
  sorry

end IsLocalCompleteIntersection

instance (g : S)
    [hS : IsGlobalCompleteIntersection k S] :
    IsGlobalCompleteIntersection k (Localization.Away g) :=
  IsGlobalCompleteIntersection.of_isLocalizationAway g hS

instance (g : S)
    [hS : IsLocalCompleteIntersection k S] :
    IsLocalCompleteIntersection k (Localization.Away g) :=
  IsLocalCompleteIntersection.of_isLocalizationAway g hS

end
