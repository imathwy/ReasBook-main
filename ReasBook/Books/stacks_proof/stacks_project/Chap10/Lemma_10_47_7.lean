import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

section

variable {k R S : Type u}
variable [Field k] [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
variable [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k S)))]

instance : GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))) := by
  let e := pullbackSpecIso k R S
  letI : GeometricallyIrreducible (e.inv ≫ pullback.fst _ _) := by
    infer_instance
  simpa [e, pullbackSpecIso_inv_fst'] using
    (inferInstance : GeometricallyIrreducible (e.inv ≫ pullback.fst _ _))

/- Lemma 10.47.7: if `k` is a field, `S` is geometrically irreducible over `k`, and `R` is any
`k`-algebra, then the canonical map `Spec(R ⊗[k] S) → Spec(R)` induces a bijection on irreducible
components.

The owner abstraction is `Scheme.Hom.irreducibleComponentsEquiv`, applied to the tensor-product
projection together with the owner-side base-change instance for
`GeometricallyIrreducible` and the prime-spectrum openness theorem
`PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field`.
-/
#check
  (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))).irreducibleComponentsEquiv
    (by
      simpa using
        (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
          IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)))))

end
