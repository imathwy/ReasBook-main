import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum Algebra.TensorProduct
open scoped TensorProduct

universe u v w

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Lemma 10.41.10: for a field `k` and `k`-algebras `R` and `S`, the canonical map
`Spec(S ⊗[k] R) → Spec(R)` induced by the right-factor inclusion
`TensorProduct.includeRight : R →ₐ[k] S ⊗[k] R` is open. -/
theorem isOpenMap_primeSpectrum_comap_algebraMap_tensorProduct_of_field :
    IsOpenMap (comap ((includeRight : R →ₐ[k] S ⊗[k] R).toRingHom)) := by
  let e : R ⊗[k] S ≃ₐ[k] S ⊗[k] R := Algebra.TensorProduct.comm k R S
  rw [show ((includeRight : R →ₐ[k] S ⊗[k] R).toRingHom) =
      e.toRingHom.comp (algebraMap R (R ⊗[k] S)) by
        ext r
        simp [e],
    comap_comp]
  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field.comp
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective).isOpenMap

end
