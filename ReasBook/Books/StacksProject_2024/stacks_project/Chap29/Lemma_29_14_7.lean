import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Basic

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall:
- this file keeps only the additional fiberwise predicates from `Lemma 29.14.7` that need the
  fiber-ring and Krull-dimension owners;
- the lightweight Chapter 29 owners for the other parts of the lemma live in
  `Lemma_29_14_7_Core.lean`, but are not used here.
-/

universe u

namespace RingHom

variable {R A : Type u} [CommRing R] [CommRing A]

/-- The fiber ring of `φ : R →+* A` over a prime `p` of `R`, written as `κ(p) ⊗[R] A`. -/
abbrev fiberRing (φ : R →+* A) (p : PrimeSpectrum R) : Type _ :=
  let _ : Algebra R A := φ.toAlgebra
  IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal) ⊗[R] A

/-- A ring map has reduced fibers if every fiber ring over a prime of the source is reduced. -/
def hasReducedFibers (φ : R →+* A) : Prop :=
  ∀ p : PrimeSpectrum R, IsReduced (fiberRing φ p)

/-- A ring map has fibers of Krull dimension at most `n` if each fiber ring over a prime of the
source has Krull dimension at most `n`. -/
def fibersKrullDimLE (n : ℕ) (φ : R →+* A) : Prop :=
  ∀ p : PrimeSpectrum R, Ring.KrullDimLE n (fiberRing φ p)

/-- Access a reduced fiber from the reduced-fibers predicate. -/
theorem hasReducedFibers.isReduced (h : hasReducedFibers φ) (p : PrimeSpectrum R) :
    IsReduced (fiberRing φ p) :=
  h p

/-- Access the Krull-dimension bound on the fiber over a chosen prime. -/
theorem fibersKrullDimLE.isKrullDimLE (h : fibersKrullDimLE n φ) (p : PrimeSpectrum R) :
    Ring.KrullDimLE n (fiberRing φ p) :=
  h p

/-- Lemma 29.14.7 (3): the property that all fibers of `R → A` are reduced is local. -/
theorem hasReducedFibers_propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.hasReducedFibers := sorry

/-- Lemma 29.14.7 (4): for a fixed `n`, the property that every fiber of `R → A` has Krull
dimension at most `n` is local. -/
theorem fibersKrullDimLE_propertyIsLocal (n : ℕ) :
    RingHom.PropertyIsLocal (RingHom.fibersKrullDimLE n) := sorry

end RingHom
