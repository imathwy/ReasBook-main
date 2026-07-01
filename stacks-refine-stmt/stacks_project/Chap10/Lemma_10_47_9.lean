import Mathlib
import stacks_project.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat CategoryTheory

namespace Algebra

universe u

section

variable (k K S : Type u)
variable [Field k] [Field K] [CommRing S]
variable [Algebra k K] [Algebra K S] [Algebra k S] [IsScalarTower k K S]

/-- Lemma 10.47.9: if the field extension `K / k` is geometrically irreducible and the
`K`-algebra `S` is geometrically irreducible over `K`, then `S` is geometrically irreducible over
`k`. -/
-- Proof sketch: apply `AlgebraicGeometry.GeometricallyIrreducible.comp` to the structure maps
-- `Spec S ⟶ Spec K ⟶ Spec k` and identify the composite with `Spec.map (ofHom (algebraMap k S))`.
@[stacks 0G30]
theorem geometrically_irreducible_over_base_of_tower
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K)))]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap K S)))] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k S))) := sorry

end

end Algebra
