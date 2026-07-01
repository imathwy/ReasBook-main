import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/- Definition 10.47.4: the canonical scheme-theoretic notion of a geometrically irreducible
`k`-algebra `S` is
`AlgebraicGeometry.GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))`.
-/
#check GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S)))

/-- Prime-spectrum form of the affine base-change criterion for Definition 10.47.4. -/
theorem geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IrreducibleSpace (PrimeSpectrum (S ⊗[k] K)) := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    let e := Scheme.homeoOfIso (pullbackSpecIso k S K).symm
    simpa using e.irreducibleSpace_iff.mpr (h K)
  · intro h K _ _
    let e := Scheme.homeoOfIso (pullbackSpecIso k S K).symm
    simpa using e.irreducibleSpace_iff.mp (h K)

/-- A field is geometrically irreducible over itself. -/
instance : GeometricallyIrreducible (Spec.map (ofHom (algebraMap k k))) := by
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange]
  intro K _ _
  let e : k ⊗[k] K ≃ₐ[k] K := Algebra.TensorProduct.lid k K
  letI : IsDomain (k ⊗[k] K) := MulEquiv.isDomain _ e.toMulEquiv
  infer_instance

end
