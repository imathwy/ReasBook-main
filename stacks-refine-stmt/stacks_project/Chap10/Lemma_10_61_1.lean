import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

open PrimeSpectrum TopologicalSpace

-- Layering for this item:
-- * source-facing: infinitude of a nonempty open subset of `Spec(R)`.
-- * core/canonical owners: `Opens (PrimeSpectrum R)` for the open subset, the generic point
--   `(⊥ : PrimeSpectrum R)` of the spectrum of a domain, specialization via
--   `PrimeSpectrum.le_iff_specializes`, and the one-dimensional owner predicate
--   `Ring.KrullDimLE 1 R`.
-- * bridge/view: a finite nonempty open subset contains an open singleton by
--   `exists_isOpen_singleton_of_isOpen_finite`; since every nonempty open subset of `Spec(R)` for
--   a domain contains the generic point, that singleton must be `{⊥}`. An isolated generic point
--   is the owner-level bridge to `Ring.KrullDimLE 1 R`, contradicting `2 ≤ ringKrullDim R`.

private theorem krullDimLE_one_of_isOpen_singleton_genericPoint
    (hgenericOpen : IsOpen ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R))) :
    Ring.KrullDimLE 1 R := by
  sorry

/-- Lemma 10.61.1: if `R` is a Noetherian local domain of Krull dimension at least `2`, then every
nonempty open subset of `Spec(R)` is infinite. The open subset is stated canonically as
`U : Opens (PrimeSpectrum R)`, with nonemptiness expressed owner-canonically by `U ≠ ⊥`; the
conclusion concerns the underlying set of points. -/
theorem infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim
    (U : Opens (PrimeSpectrum R)) (hU : U ≠ ⊥)
    (hdim : 2 ≤ ringKrullDim R) :
    Set.Infinite (U : Set (PrimeSpectrum R)) := by
  classical
  by_contra hfinite
  have hfinite' : Set.Finite (U : Set (PrimeSpectrum R)) :=
    not_not.mp hfinite
  have hne : Set.Nonempty (U : Set (PrimeSpectrum R)) := (U.ne_bot_iff_nonempty).mp hU
  obtain ⟨x, -, hxopen⟩ := exists_isOpen_singleton_of_isOpen_finite hfinite' hne U.2
  have hxbot : x = (⊥ : PrimeSpectrum R) := by
    have hmem : (⊥ : PrimeSpectrum R) ∈ ({x} : Set (PrimeSpectrum R)) :=
      ((PrimeSpectrum.le_iff_specializes (⊥ : PrimeSpectrum R) x).mp bot_le).mem_open hxopen
        (by simp)
    simpa using hmem.symm
  have hgenericOpen : IsOpen ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) := by
    simpa [hxbot] using hxopen
  have hdim1 : Ring.KrullDimLE 1 R :=
    krullDimLE_one_of_isOpen_singleton_genericPoint hgenericOpen
  have hdim' : ringKrullDim R ≤ 1 := Ring.krullDimLE_iff.mp hdim1
  have : ¬ (2 : WithBot ℕ∞) ≤ 1 := by
    simp
  exact this (hdim.trans hdim')

end
