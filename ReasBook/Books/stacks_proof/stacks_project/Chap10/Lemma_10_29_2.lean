import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksProject_2024.Chap05.Lemma_5_23_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open Topology

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Layering for this item:
* core/canonical owner: `IsSpectralMap`.
* bridge/view: show the canonical `Spec` map `comap φ` is spectral, then derive constructible
  preimages from the chapter-level owner API `IsSpectralMap.isConstructible_preimage`.
-/

/-- Lemma 10.29.2 (1): for a ring homomorphism `φ : R →+* S`, the induced map
`Spec(S) → Spec(R)` is spectral; equivalently, the preimage of a quasi-compact open subset of
`Spec(R)` is quasi-compact. -/
@[stacks 00F7]
theorem primeSpectrum_comap_isSpectralMap (φ : R →+* S) :
    IsSpectralMap (comap φ) := by
  refine ⟨continuous_comap φ, ?_⟩
  intro U hU_open hU_compact
  classical
  obtain ⟨t, rfl⟩ := isCompact_isOpen_iff.mp ⟨hU_compact, hU_open⟩
  refine (PrimeSpectrum.isCompact_isOpen_iff.mpr ?_).1
  refine ⟨t.image φ, ?_⟩
  rw [Set.preimage_compl, preimage_comap_zeroLocus]
  ext x
  simp

/-- Lemma 10.29.2 (2): the preimage of a constructible subset of `Spec(R)` under the induced map
`Spec(S) → Spec(R)` is constructible in `Spec(S)`. -/
@[stacks 00F7]
theorem primeSpectrum_comap_preimage_isConstructible
    (φ : R →+* S) {E : Set (PrimeSpectrum R)} (hE : IsConstructible E) :
    IsConstructible (comap φ ⁻¹' E) :=
  (primeSpectrum_comap_isSpectralMap φ).isConstructible_preimage hE

end
