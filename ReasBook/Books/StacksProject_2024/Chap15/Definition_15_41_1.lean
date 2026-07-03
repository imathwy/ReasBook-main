import Mathlib
import StacksProject_2024.Chap10.Definition_10_166_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

/-- Definition 15.41.1: a ring map `R → S` is regular if it is flat and for every prime
`p ⊂ R` the fiber ring `p.asIdeal.Fiber S = S ⊗[R] κ(p)` is geometrically regular over the
residue field `κ(p)`. In this project, `IsGeometricallyRegular` already packages the
Noetherianity required in the textbook definition of the fibers. -/
class IsRegularRingMap (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    Prop extends Module.Flat R S where
  /-- Every fiber ring of a regular ring map is geometrically regular over the corresponding
  residue field. -/
  isGeometricallyRegular_fiber :
    ∀ p : PrimeSpectrum R, IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S)

section

variable (R : Type u) [CommRing R]

-- Proof sketch: the identity map is flat, and for each prime `p` the fiber of `R → R` over `p`
-- identifies with the residue field `κ(p)`, which is geometrically regular over itself by the
-- canonical field instance from `Lemma 10.166.5`.
/-- The identity map of a commutative ring is a regular ring map. -/
instance : IsRegularRingMap R R := sorry

end

end Algebra
