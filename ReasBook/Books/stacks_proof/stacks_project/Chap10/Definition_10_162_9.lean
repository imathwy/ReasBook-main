import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The quotient of a local ring by a prime ideal is again a local ring. -/
instance primeSpectrum_quotient_isLocalRing (p : PrimeSpectrum R) : IsLocalRing (R ⧸ p.asIdeal) :=
  by
    -- The quotient map is surjective, so locality descends to the prime quotient.
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Definition 10.162.9: a local ring is analytically unramified when its completion with
respect to the maximal ideal is reduced. -/
@[stacks 032X, mk_iff isAnalyticallyUnramified_iff]
class IsAnalyticallyUnramified : Prop where
  completion_isReduced : IsReduced (AdicCompletion (maximalIdeal R) R)

attribute [instance] IsAnalyticallyUnramified.completion_isReduced

end

section

variable (K : Type u) [Field K]

/-- Helper for Definition 10.162.9: a field is complete for the adic topology defined by the zero
ideal. -/
theorem field_isAdicComplete_bot : IsAdicComplete (⊥ : Ideal K) K := by
  -- The `⊥`-adic topology is discrete, so the standard `bot` instances give completeness.
  infer_instance

/-- Helper for Definition 10.162.9: the completion of a field at its maximal ideal is reduced. -/
theorem field_completion_isReduced : IsReduced (AdicCompletion (maximalIdeal K) K) := by
  let _ : IsAdicComplete (⊥ : Ideal K) K := field_isAdicComplete_bot K
  -- Replace the maximal ideal by `⊥`, then identify the completion with the field itself.
  rw [IsLocalRing.maximalIdeal_eq_bot]
  let e : K ≃ₐ[K] AdicCompletion (⊥ : Ideal K) K := AdicCompletion.ofAlgEquiv (⊥ : Ideal K)
  -- Reducedness descends along the inverse of the completion equivalence.
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Fields are analytically unramified. -/
instance : IsAnalyticallyUnramified K where
  -- The completion at the maximal ideal is identified with the field itself.
  completion_isReduced := field_completion_isReduced K

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace PrimeSpectrum

/-- A prime ideal of a local ring is analytically unramified when the quotient ring by
that prime ideal is analytically unramified. -/
def IsAnalyticallyUnramified (p : PrimeSpectrum R) : Prop :=
  _root_.IsAnalyticallyUnramified (R ⧸ p.asIdeal)

end PrimeSpectrum

end
