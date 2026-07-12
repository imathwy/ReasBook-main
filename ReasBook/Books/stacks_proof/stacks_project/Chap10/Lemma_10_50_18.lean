import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

-- This is a source-facing bridge over the owner theorem `IsDiscreteValuationRing.TFAE`: the
-- primitive ambient data are the domain and valuation-ring structures, while Noetherianity and the
-- DVR/field dichotomy remain theorem-level properties. For the forward direction, a valuation ring
-- is local, so the Noetherian local-domain TFAE upgrades `ValuationRing A` to
-- `IsDiscreteValuationRing A` once we exclude the field case; the reverse direction is by the
-- canonical `IsNoetherianRing` instances for DVRs and fields.
/-- Lemma 10.50.18: a valuation ring is Noetherian if and only if it is either a discrete
valuation ring or a field. -/
@[stacks 00II]
theorem valuationRing_isNoetherianRing_iff_isDiscreteValuationRing_or_isField :
    IsNoetherianRing A ↔ IsDiscreteValuationRing A ∨ IsField A := by
  constructor
  · intro hA
    by_cases hField : IsField A
    · exact Or.inr hField
    · letI : IsNoetherianRing A := hA
      exact Or.inl <|
        ((IsDiscreteValuationRing.TFAE A hField).out 1 0).mp (show ValuationRing A from inferInstance)
  · rintro (hDVR | hField)
    · letI : IsDiscreteValuationRing A := hDVR
      infer_instance
    · letI : Field A := hField.toField
      infer_instance

end
