import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise TensorProduct

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

local notation "TensorRing" => SeparableClosure k ⊗[k] K
local notation "SpecTensor" => PrimeSpectrum TensorRing

/-- The Galois group acts on `SeparableClosure k ⊗[k] K` through the canonical automorphisms of
the left tensor factor. This ring automorphism is the owner abstraction from which the spectrum
action is derived. -/
private noncomputable def tensorLeftGaloisAut :
    Gal(SeparableClosure k / k) →* TensorRing ≃ₐ[k] TensorRing where
  toFun σ := Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K)
  map_one' := by
    change Algebra.TensorProduct.congr
        (AlgEquiv.refl : SeparableClosure k ≃ₐ[k] SeparableClosure k)
        (AlgEquiv.refl : K ≃ₐ[k] K) = AlgEquiv.refl
    simp
  map_mul' σ τ := by
    change Algebra.TensorProduct.congr
        ((τ : SeparableClosure k ≃ₐ[k] SeparableClosure k).trans σ)
        ((AlgEquiv.refl : K ≃ₐ[k] K).trans (AlgEquiv.refl : K ≃ₐ[k] K)) =
      (Algebra.TensorProduct.congr τ (AlgEquiv.refl : K ≃ₐ[k] K)).trans
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K))
    simpa using
      (Algebra.TensorProduct.congr_trans
        τ σ (AlgEquiv.refl : K ≃ₐ[k] K) (AlgEquiv.refl : K ≃ₐ[k] K))

local notation "tensorAut" =>
  (tensorLeftGaloisAut :
    Gal(SeparableClosure k / k) →*
      (SeparableClosure k ⊗[k] K) ≃ₐ[k] (SeparableClosure k ⊗[k] K))

noncomputable local instance tensorLeftGaloisMulSemiringAction :
    MulSemiringAction (Gal(SeparableClosure k / k)) TensorRing :=
  MulSemiringAction.compHom (SeparableClosure k ⊗[k] K) tensorAut

noncomputable local instance :
    SMul (Gal(SeparableClosure k / k)) SpecTensor where
  smul σ := PrimeSpectrum.comap ((tensorAut σ).symm.toRingHom)

noncomputable local instance :
    MulAction (Gal(SeparableClosure k / k)) SpecTensor where
  one_smul p := by
    change PrimeSpectrum.comap ((tensorAut 1).symm.toRingHom) p = p
    rw [show tensorAut 1 = 1 by exact map_one tensorAut]
    rfl
  mul_smul σ τ p := by
    change PrimeSpectrum.comap ((tensorAut (σ * τ)).symm.toRingHom) p =
      PrimeSpectrum.comap ((tensorAut σ).symm.toRingHom)
        (PrimeSpectrum.comap ((tensorAut τ).symm.toRingHom) p)
    rw [show tensorAut (σ * τ) = tensorAut σ * tensorAut τ by
      exact map_mul tensorAut σ τ]
    rfl

/-- The Galois action on `Spec(SeparableClosure k ⊗[k] K)` is induced by the inverse tensor
automorphism acting on the left tensor factor. -/
theorem galoisTensorPrimeSpectrum_smul_def (σ : Gal(SeparableClosure k / k))
    (p : SpecTensor) :
    σ • p =
      PrimeSpectrum.comap
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : K ≃ₐ[k] K)).symm.toRingHom p :=
  rfl

-- Proof sketch: first replace `K` by the relative separable closure `separableClosure k K` using
-- Lemmas `10.47.13` and `10.47.7`, which identifies the two prime spectra. For the separable
-- extension, primes of `SeparableClosure k ⊗[k] separableClosure k K` correspond to `k`-embeddings
-- `separableClosure k K → SeparableClosure k`, and `Gal(SeparableClosure k / k)` acts transitively
-- on those embeddings by postcomposition.
/-- Lemma 10.47.14: the Galois group of the separable closure acts transitively on the prime
spectrum of `SeparableClosure k ⊗[k] K`. Equivalently, any two primes are conjugate under the
canonical action induced from the left tensor factor. -/
@[instance]
theorem galoisTensorPrimeSpectrum_transitive :
    MulAction.IsPretransitive (Gal(SeparableClosure k / k)) SpecTensor := by
  sorry

/-- Textbook unpacking of Lemma 10.47.14: any two primes are conjugate under the canonical
Galois action. -/
theorem galoisTensorPrimeSpectrum_exists_smul_eq (p q : SpecTensor) :
    ∃ σ : Gal(SeparableClosure k / k), σ • p = q :=
  MulAction.exists_smul_eq (Gal(SeparableClosure k / k)) p q

end
