import Mathlib.RingTheory.Ideal.GoingDown

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)

open PrimeSpectrum

/- Definition 10.41.1 (1): a ring map `φ : R →+* S` satisfies going up exactly when the induced
map `Spec(S) → Spec(R)` is a specializing map. -/
#check (SpecializingMap (comap φ))

/- Definition 10.41.1 (2): after installing the canonical algebra structure from `φ`, the
going-down property is the owner predicate `Algebra.HasGoingDown R S`. -/
#check
  (let _ : Algebra R S := φ.toAlgebra
   Algebra.HasGoingDown R S)

end
