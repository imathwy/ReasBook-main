import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
* primary domain: Krull dimension of local rings under henselization and strict henselization;
* sampled owner declarations:
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`,
  `henselizationMap_faithfullyFlat`,
  `strictHenselizationMap_faithfullyFlat`,
  `IsHenselizationOf.map_maximalIdeal`,
  `IsStrictHenselizationOf.map_maximalIdeal`;
* owner abstraction: the source-facing statements compare the two local rings by first comparing
  their closed-point localizations, then transporting that equality back to the ambient local rings
  through `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`; faithful-flatness and maximal-ideal
  image are derived owner data supplying that closed-point comparison.
* primitive data: the local ring `R` and the chosen owner instances
  `IsHenselizationOf R Rh` / `IsStrictHenselizationOf R Rsh`;
* derived API: faithful-flatness of the structural maps, extension of the maximal ideal, and the
  zero-dimensional closed fiber at the closed point.

Layer triage:
* `source-facing`: the two equality statements for `ringKrullDim`;
* `core/canonical`: the local owner `ringKrullDim` together with the closed-point localization
  comparison;
* `bridge/view`: the passage between a local ring and the localization at its maximal ideal.
-/

-- Proof sketch: compare the two local rings at their closed points. Lemma `15.45.1` gives
-- faithful flatness of `R → Rh`, hence going down for the maximal ideal of `Rh`, and
-- `IsHenselizationOf.map_maximalIdeal` identifies the closed fiber with the residue field of the
-- localization at `maximalIdeal Rh`, so the closed-point comparison reduces to a zero-dimensional
-- fiber, after which the local and localized Krull dimensions are identified canonically by
-- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` and
-- `IsLocalization.AtPrime.ringKrullDim_eq_height`.
/-- Lemma 15.45.7 (1): a chosen henselization `Rh` of a local ring `R` has the same Krull
dimension as `R`. -/
theorem ringKrullDim_henselization_eq :
    ringKrullDim R = ringKrullDim Rh := by
  sorry

-- Proof sketch: as in part `(1)`, the canonical owner is the closed-point comparison
-- `Localization.AtPrime (maximalIdeal R) → Localization.AtPrime (maximalIdeal Rsh)`. The maximal
-- ideal of `Rsh` is the extension of `maximalIdeal R` by
-- `IsStrictHenselizationOf.map_maximalIdeal`, so the closed fiber is the residue field of the
-- localized target and has Krull dimension `0`; the ambient local equality again follows by the
-- canonical identification of a local ring with its closed-point localization on Krull dimension.
/-- Lemma 15.45.7 (2): a chosen strict henselization `Rsh` of a local ring `R` has the same Krull
dimension as `R`. -/
theorem ringKrullDim_strictHenselization_eq :
    ringKrullDim R = ringKrullDim Rsh := by
  sorry

end
