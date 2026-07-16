import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_153_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The canonical owner for a strict henselization of a local ring. It records that the
structural map is local, the target is strictly henselian, the map is an ind-étale algebra, and
the maximal ideal is the image of the source maximal ideal. -/
class IsStrictHenselizationOf : Prop extends StrictHenselianLocalRing S,
  IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale :
    RingHom.IsFilteredColimitOfEtale (algebraMap R S)
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S

end
