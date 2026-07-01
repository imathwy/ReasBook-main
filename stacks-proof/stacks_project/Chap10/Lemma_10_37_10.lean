import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-
Lemma 10.37.10 is a `source-facing` TFAE statement. Its `core/canonical` owner abstractions are
`IsIntegrallyClosed` for the global normal-domain clause and `IsNormalRing` for the all-prime
localization clause; the maximal-localization clause is the corresponding `bridge/view`.
-/
/-- Lemma 10.37.10: for a domain `R`, the following are equivalent: `R` is a normal domain, every
localization `Rₚ` at a prime ideal is a normal domain, and every localization `Rₘ` at a maximal
ideal is a normal domain. Using `Definition 10.37.1` and `Definition 10.37.11`, these are
expressed by `IsIntegrallyClosed R`, `IsNormalRing R`, and the corresponding maximal
localizations. -/
-- Proof sketch: the implication from `R` to all prime localizations is the canonical instance
-- `IsIntegrallyClosed R → IsNormalRing R`; maximal ideals are prime for the middle-to-last
-- implication; and the converse is the owner theorem
-- `IsIntegrallyClosed.of_isLocalization_maximal`.
theorem isIntegrallyClosed_tfae :
    List.TFAE
      [ IsIntegrallyClosed R
      , IsNormalRing R
      , ∀ m : MaximalSpectrum R, IsIntegrallyClosed (Localization.AtPrime m.asIdeal)
      ] := by
  tfae_have 1 → 2 := fun h ↦ by
    letI : IsIntegrallyClosed R := h
    infer_instance
  tfae_have 2 → 3 := fun h m ↦ by
    letI : IsNormalRing R := h
    exact isIntegrallyClosed_localizationAtPrime m.toPrimeSpectrum
  tfae_have 3 → 1 := fun h ↦
    IsIntegrallyClosed.of_isLocalization_maximal
      (fun p _ ↦ Localization.AtPrime p)
      fun p _ ↦ by
        simpa using h ⟨p, inferInstance⟩
  tfae_finish
