import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_47_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped TensorProduct
open AlgebraicGeometry CommRingCat

section

variable {k R : Type u} [Field k] [IsSepClosed k] [CommRing R] [Algebra k R]

/-- Lemma 10.47.5 (Tag 037M): over a separably closed field `k`, a `k`-algebra `R` is
geometrically irreducible over `k` if and only if `Spec R` is irreducible. -/
@[stacks 037M]
theorem Lemma_10_47_5
    :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (Spec (of R)) := by
  constructor
  · intro h
    letI : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) := h
    simpa using
      (GeometricallyIrreducible.irreducibleSpace_of_subsingleton
        (Spec.map (ofHom (algebraMap k R))))
  · intro h
    let eK : SeparableClosure k ≃ₐ[k] k := IsSepClosure.equiv k (SeparableClosure k) k
    let e : R ⊗[k] SeparableClosure k ≃ₐ[R] R :=
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) eK).trans
        (Algebra.TensorProduct.rid k R R)
    exact geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_separableClosure.2 <|
      (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).irreducibleSpace_iff.2 <| by
        simpa using h

end
