import Mathlib.RingTheory.LocalProperties.Basic

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall / owner check:
-- `lean_leansearch` identified the bundled local-property owner `RingHom.PropertyIsLocal`, while
-- `lean_leanfinder` surfaced its clause owners in `Mathlib.RingTheory.LocalProperties.Basic`.
-- The source item defines a local property by explicit localization and local-global clauses, so
-- this file keeps the canonical bundled owner as the main entry and adds a thin source-facing
-- companion theorem exposing its clause data.

universe u

namespace RingHom

variable
  (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)

/- Definition 29.14.1: the canonical bundled owner for a local property of ring maps is
`RingHom.PropertyIsLocal`. -/
#check RingHom.PropertyIsLocal

/-- Definition 29.14.1, companion API: unpack the bundled local-property owner into its canonical
mathlib clause owners. -/
theorem propertyIsLocal_iff :
    RingHom.PropertyIsLocal P ↔
      RingHom.LocalizationAwayPreserves P ∧
        RingHom.OfLocalizationSpanTarget P ∧
          RingHom.OfLocalizationSpan P ∧
            RingHom.StableUnderCompositionWithLocalizationAwayTarget P := by
  constructor
  · intro hP
    exact ⟨hP.localizationAwayPreserves, hP.ofLocalizationSpanTarget, hP.ofLocalizationSpan,
      hP.StableUnderCompositionWithLocalizationAwayTarget⟩
  · rintro ⟨hloc, htarget, hsource, hcomp⟩
    exact ⟨hloc, htarget, hsource, hcomp⟩

end RingHom
