import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry PrimeSpectrum IsLocalRing

universe u

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-open owner
-- `AlgebraicGeometry.IsAffineOpen`, the standard affine opens `IsAffineOpen.Spec_basicOpen`,
-- and the local-spectrum closed-point API `IsLocalRing.closedPoint` /
-- `IsLocalRing.isClosed_singleton_closedPoint`. The punctured spectrum is therefore kept as the
-- explicit open complement of the closed point in `PrimeSpectrum A`, rather than as a wrapper.

/-- The punctured spectrum of a local ring `A`, viewed as the open complement of the closed point
in `Spec(A)`. -/
def puncturedSpectrumOpen (A : Type u) [CommRing A] [IsLocalRing A] :
    (Spec (CommRingCat.of A)).Opens :=
  ⟨({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint A).isOpen_compl⟩

/-- Membership in the punctured spectrum means that the prime is not the closed point. -/
theorem mem_puncturedSpectrumOpen_iff_ne_closedPoint (p : PrimeSpectrum A) :
    p ∈ puncturedSpectrumOpen A ↔ p ≠ IsLocalRing.closedPoint A := sorry

/-- Membership in the punctured spectrum means that the corresponding prime ideal is not the
maximal ideal of the local ring. -/
theorem mem_puncturedSpectrumOpen (p : PrimeSpectrum A) :
    p ∈ puncturedSpectrumOpen A ↔ p.asIdeal ≠ maximalIdeal A := sorry

/-- Lemma 31.16.1, owner-level form: for a Noetherian local ring `(A, 𝔪)`, the punctured
spectrum `U = Spec(A) \ {𝔪}` is affine if and only if `A` has Krull dimension at most `1`,
expressed by the canonical owner `Ring.KrullDimLE 1 A`. -/
@[stacks 0BCR]
theorem isAffineOpen_puncturedSpectrum_iff_krullDimLE_one :
    IsAffineOpen (puncturedSpectrumOpen A) ↔ Ring.KrullDimLE 1 A := sorry

/-- Lemma 31.16.1, source-facing companion: the punctured spectrum of a Noetherian local ring is
affine if and only if `dim(A) ≤ 1`. -/
theorem isAffineOpen_puncturedSpectrum_iff_ringKrullDim_le_one :
    IsAffineOpen (puncturedSpectrumOpen A) ↔ ringKrullDim A ≤ 1 := by
  rw [isAffineOpen_puncturedSpectrum_iff_krullDimLE_one]
  simpa using (Ring.krullDimLE_iff (R := A) (n := 1))

end
