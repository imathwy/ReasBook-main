import StacksProject_2024.Chap05.Lemma_5_19_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Lemma 10.112.1:
- primary domain: Krull dimension of prime spectra under going up / going down.
- owner declarations inspected:
  `topologicalKrullDim_le_of_surjective_specializing_or_generalizing`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `SpecializingMap (PrimeSpectrum.comap f)`,
  `GeneralizingMap (PrimeSpectrum.comap f)`.
- best owner abstraction: the topological Krull-dimension comparison for a surjective map with
  specialization/generalization lifting, specialized along the canonical spectrum map
  `PrimeSpectrum.comap f`.
- primitive data: only the surjectivity of `PrimeSpectrum.comap f` and one of the two canonical
  lifting predicates.
- derived API: the ring-level inequality on `ringKrullDim`.

Layer triage:
- `source-facing`: the ring-theoretic dimension inequality for a ring homomorphism.
- `core/canonical`: `topologicalKrullDim_le_of_surjective_specializing_or_generalizing` and
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.
- `bridge/view`: this file's theorem, transporting the topological owner theorem to
  `ringKrullDim`.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

-- Proof sketch: this is exactly the Chapter 5 topological Krull-dimension comparison specialized
-- to the canonical spectrum map `PrimeSpectrum.comap f`, then transported back to ring-theoretic
-- Krull dimension by `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.
/-- Lemma 10.112.1: if the induced map `Spec(S) → Spec(R)` is surjective and lifts either
specializations or generalizations, equivalently if the ring map satisfies going up or going down,
then `dim(R) ≤ dim(S)`. -/
@[stacks 00OH]
theorem ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
    (f : R →+* S) (hSurj : Function.Surjective (PrimeSpectrum.comap f))
    (hLift :
      SpecializingMap (PrimeSpectrum.comap f) ∨
        GeneralizingMap (PrimeSpectrum.comap f)) :
    ringKrullDim R ≤ ringKrullDim S := by
  let comap : PrimeSpectrum S → PrimeSpectrum R := PrimeSpectrum.comap f
  -- Repackage the source hypotheses along the local alias so they match the Chapter 5 theorem.
  have hSurj' : Function.Surjective comap := by
    simpa [comap] using hSurj
  have hLift' : SpecializingMap comap ∨ GeneralizingMap comap := by
    simpa [comap] using hLift
  -- Apply the topological Krull-dimension inequality on spectra, then translate back to rings.
  simpa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using
    topologicalKrullDim_le_of_surjective_specializing_or_generalizing
      (PrimeSpectrum.continuous_comap f) hSurj' hLift'

end
