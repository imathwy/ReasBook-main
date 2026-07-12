import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.AlgebraicGeometry.Properties

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic recall: `lean_leansearch` pointed to mathlib's ring-locality API
-- `LocalizationPreserves` and `OfLocalizationMaximal`. The Stacks definition here is the
-- source-faithful principal-open finite-span variant, so we expose that directly and keep the
-- broader mathlib locality formulations as companion API.

/-- Definition 28.4.1: a property `P` of commutative rings is local if it is preserved by
localization at a single element and can be checked on a finite family of principal opens whose
generators span the unit ideal. -/
class RingPropertyIsLocal (P : CommRingCat.{u} → Prop) : Prop where
  /-- If `P` holds for `R`, then it holds for every principal localization `R_f`. -/
  away : ∀ (R : CommRingCat.{u}) (f : R),
    P R → P (CommRingCat.of (Localization.Away f))
  /-- If a finite family of principal localizations covers `Spec R`, then `P` descends from those
  localizations back to `R`. -/
  ofSpanEqTop : ∀ (R : CommRingCat.{u}) (s : Finset R),
    Ideal.span (s : Set R) = ⊤ →
      (∀ f ∈ s, P (CommRingCat.of (Localization.Away f))) → P R

/-- Helper for Definition 28.4.1: unpack `RingPropertyIsLocal` into its two defining clauses. -/
theorem ringPropertyIsLocal_iff (P : CommRingCat.{u} → Prop) :
    RingPropertyIsLocal P ↔
      (∀ (R : CommRingCat.{u}) (f : R),
        P R → P (CommRingCat.of (Localization.Away f))) ∧
      (∀ (R : CommRingCat.{u}) (s : Finset R),
        Ideal.span (s : Set R) = ⊤ →
          (∀ f ∈ s, P (CommRingCat.of (Localization.Away f))) → P R) := by
  constructor
  · intro h
    exact ⟨h.away, h.ofSpanEqTop⟩
  · rintro ⟨hAway, hOfSpanEqTop⟩
    exact ⟨hAway, hOfSpanEqTop⟩

namespace RingPropertyIsLocal

/-- Companion API for Definition 28.4.1: a local ring property in the Stacks sense is preserved
by arbitrary localizations in the sense of mathlib's `LocalizationPreserves`. -/
theorem localizationPreserves (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P] :
    LocalizationPreserves (fun R [CommRing R] ↦ P (CommRingCat.of R)) := by
  sorry

/-- Companion API for Definition 28.4.1: a local ring property in the Stacks sense satisfies
mathlib's maximal-ideal localization descent criterion. -/
instance ofLocalizationMaximal (P : CommRingCat.{u} → Prop) [RingPropertyIsLocal P] :
    OfLocalizationMaximal (fun R [CommRing R] ↦ P (CommRingCat.of R)) := by
  sorry

end RingPropertyIsLocal
