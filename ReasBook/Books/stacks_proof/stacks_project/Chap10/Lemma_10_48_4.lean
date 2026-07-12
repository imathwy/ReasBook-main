import Mathlib
import StacksProject_2024.Chap10.Definition_10_48_3
import StacksProject_2024.Chap10.Lemma_10_48_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat

namespace Algebra

universe u

section

variable {k R : Type u} [Field k] [IsSepClosed k] [CommRing R] [Algebra k R]

-- Proof sketch: use the remark after Definition 10.48.3 together with
-- Lemma `10.48.2`; over a separably closed field every finite separable extension is already
-- `k`, so every relevant base change is canonically isomorphic to `R`.
/-- Lemma 10.48.4: if `k` is separably algebraically closed, then a `k`-algebra `R` is
geometrically connected over `k` if and only if `Spec R` is connected. -/
@[stacks 037U]
theorem geometricallyConnected_iff_connectedSpace_primeSpectrum_of_isSepClosed :
    geometrically (ConnectedSpace ·) (Spec.map (ofHom (algebraMap k R))) ↔
      ConnectedSpace (PrimeSpectrum R) := by
  rw [Lemma_10_48_2]
  have baseChange_iff (K : Type u) [Field K] [Algebra k K]
      [FiniteDimensional k K] [Algebra.IsSeparable k K] :
      ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) ↔ ConnectedSpace (PrimeSpectrum R) := by
    let eK : K ≃ₐ[k] k :=
      (AlgEquiv.ofBijective (Algebra.ofId k K)
        ⟨(algebraMap k K).injective, IsSepClosed.algebraMap_surjective k K⟩).symm
    let e : R ⊗[k] K ≃ₐ[R] R :=
      (TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eK).trans (TensorProduct.rid k R R)
    let eSpec : PrimeSpectrum (R ⊗[k] K) ≃ₜ PrimeSpectrum R :=
      PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    constructor
    · intro hRK
      letI : ConnectedSpace (PrimeSpectrum (R ⊗[k] K)) := hRK
      have hsurj : Function.Surjective eSpec := eSpec.surjective
      exact hsurj.connectedSpace eSpec.continuous
    · intro hR
      letI : ConnectedSpace (PrimeSpectrum R) := hR
      have hsurj : Function.Surjective eSpec.symm := eSpec.symm.surjective
      exact hsurj.connectedSpace eSpec.symm.continuous
  constructor
  · intro h
    simpa using (baseChange_iff k).1 (h k)
  · intro h K _ _ _ _
    exact (baseChange_iff K).2 h

end

end Algebra
