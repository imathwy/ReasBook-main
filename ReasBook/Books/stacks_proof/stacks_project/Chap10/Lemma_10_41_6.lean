import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksProject_2024.Chap10.Definition_10_41_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

open AlgebraicGeometry
open PrimeSpectrum

/- Lemma 10.41.6: for the canonical map `Spec(S) → Spec(R)`, the source-facing equivalence is the
affine-spectrum bridge to the canonical owner theorem
`AlgebraicGeometry.isClosedMap_iff_specializingMap`. -/
#check
  (show SpecializingMap (comap (algebraMap R S)) ↔ IsClosedMap (comap (algebraMap R S)) from
    (isClosedMap_iff_specializingMap (Spec.map (CommRingCat.ofHom (algebraMap R S)))).symm)

end
