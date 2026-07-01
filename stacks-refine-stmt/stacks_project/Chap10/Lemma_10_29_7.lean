import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial PrimeSpectrum
open TopologicalSpace

universe u

section

variable {R : Type u} [CommRing R]

-- Layering for this item:
-- * source-facing: the textbook compact-open image statement below.
-- * core/canonical owners: `Polynomial.image_comap_C_basicOpen`, `Polynomial.isOpenMap_comap_C`,
--   and `CompactOpens.map`.
-- * bridge/view: `isCompact_isOpen_image_comap_C_basicOpen` unwraps the owner-level compact-open
--   image back to the textbook `IsCompact ∧ IsOpen` formulation.

/-
Lemma 10.29.7: the exact image formula for a standard open under the structure morphism
`Spec(R[X]) → Spec(R)` is the canonical theorem `Polynomial.image_comap_C_basicOpen`.
-/
recall Polynomial.image_comap_C_basicOpen

/-- Lemma 10.29.7: for a polynomial `f : R[X]`, the image of the standard open `D(f)` under the
structure map `Spec(R[X]) → Spec(R)` is a compact open, i.e. a quasi-compact open subset of
`Spec(R)`. -/
theorem isCompact_isOpen_image_comap_C_basicOpen (f : R[X]) :
    IsCompact (comap C '' (basicOpen f : Set (PrimeSpectrum R[X]))) ∧
      IsOpen (comap C '' (basicOpen f : Set (PrimeSpectrum R[X]))) := by
  let U : CompactOpens (PrimeSpectrum R[X]) :=
    ⟨⟨basicOpen f, PrimeSpectrum.isCompact_basicOpen f⟩, (basicOpen f).isOpen⟩
  let V : CompactOpens (PrimeSpectrum R) :=
    U.map (comap C) (continuous_comap C) isOpenMap_comap_C
  refine ⟨?_, ?_⟩
  · simpa [U, V] using V.isCompact
  · simpa [U, V] using V.isOpen

/- The structure morphism `Spec(R[X]) → Spec(R)` is the canonical open-map theorem
`Polynomial.isOpenMap_comap_C` from mathlib. -/
recall Polynomial.isOpenMap_comap_C

end
