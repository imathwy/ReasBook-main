import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct

section

variable (R : Type u) (σ : Type v) (S : Type w)
variable [CommRing R] [CommRing S]
variable [Algebra R S] [Algebra (MvPolynomial σ R) S]
variable [IsScalarTower R (MvPolynomial σ R) S]

/- 10.134.0.2: for a polynomial `R`-algebra map `MvPolynomial σ R → S` with kernel `I`, the
first map in the naive cotangent complex is the canonical conormal map. In mathlib this owner is
`KaehlerDifferential.kerCotangentToTensor`, with the canonical tensor order
`S ⊗[MvPolynomial σ R] Ω[MvPolynomial σ R⁄R]`. -/
#check
  ((KaehlerDifferential.kerCotangentToTensor R (MvPolynomial σ R) S) :
    (RingHom.ker (algebraMap (MvPolynomial σ R) S)).Cotangent →ₗ[MvPolynomial σ R]
      S ⊗[MvPolynomial σ R] Ω[MvPolynomial σ R⁄R])

end
