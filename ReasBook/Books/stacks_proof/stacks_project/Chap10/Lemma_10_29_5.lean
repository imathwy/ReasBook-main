import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum Topology

section

variable {R : Type u} [CommRing R]

-- Proof sketch: this is the `bridge/view` localization-away specialization of the owner theorem
-- `PrimeSpectrum.isConstructible_comap_image`. The primitive input is the constructible subset of
-- `Spec(R_f)`; the finite-presentation hypothesis is derived canonically from
-- `IsLocalization.Away.finitePresentation`.
/-- Lemma 10.29.5: for `S = R_f`, the image of a constructible subset of `Spec(S)` in `Spec(R)` is
constructible. -/
@[stacks 00F9]
theorem isConstructible_image_comap_localizationAway (f : R)
    {s : Set (PrimeSpectrum (Localization.Away f))} (hs : IsConstructible s) :
    IsConstructible (comap (algebraMap R (Localization.Away f)) '' s) := by
  simpa using
    PrimeSpectrum.isConstructible_comap_image
      (RingHom.finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation f)) hs

end
