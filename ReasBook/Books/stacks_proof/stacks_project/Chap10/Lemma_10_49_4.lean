import Mathlib
import StacksProject_2024.Chap10.Definition_10_43_1
import StacksProject_2024.Chap10.Lemma_10_43_5
import StacksProject_2024.Chap10.Lemma_10_47_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

universe u

section

variable {k R S : Type u}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

-- Proof sketch: by Lemma `10.43.5`, geometric integrality implies that `R ⊗[k] S` is reduced
-- because `R` is a domain. By Lemma `10.47.7`, geometric integrality also implies geometric
-- irreducibility, so `Spec (R ⊗[k] S)` is irreducible. A commutative ring whose prime spectrum is
-- irreducible and which is reduced is a domain.
/-- Lemma 10.49.4 (Tag 09P9): if `k` is a field, `S` is geometrically integral over `k`, and
`R` is an integral-domain `k`-algebra, then `R ⊗[k] S` is an integral domain. -/
@[stacks 09P9]
theorem Lemma_10_49_4
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap k S)))] [IsDomain R] :
    IsDomain (R ⊗[k] S) := by
  letI : IsGeometricallyReduced k S :=
    geometricallyReduced_iff_isGeometricallyReduced.mp inferInstance
  letI : IsReduced (R ⊗[k] S) := inferInstance
  let f : Spec (of (R ⊗[k] S)) ⟶ Spec (of R) :=
    Spec.map (ofHom (algebraMap R (R ⊗[k] S)))
  letI : GeometricallyIrreducible f := by
    simpa [f] using
      (inferInstance :
        GeometricallyIrreducible (Spec.map (ofHom (algebraMap R (R ⊗[k] S)))))
  haveI : IrreducibleSpace (Spec (of (R ⊗[k] S))) := by
    exact GeometricallyIrreducible.irreducibleSpace f
      (by
        simpa using
          (PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field :
            IsOpenMap (PrimeSpectrum.comap (algebraMap R (R ⊗[k] S)))))
  exact (affine_isIntegral_iff (of (R ⊗[k] S))).mp <|
    isIntegral_of_irreducibleSpace_of_isReduced _

end

end Algebra
