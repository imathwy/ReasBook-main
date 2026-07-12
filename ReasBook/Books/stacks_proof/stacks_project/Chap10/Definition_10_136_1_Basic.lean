import Mathlib
import StacksProject_2024.Chap10.Definition_10_135_1

-- Basic syntomic API split out so later proofs can use the owner predicate without importing
-- field-extension comparison results.

universe u v

section

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

open PrimeSpectrum

/-- Definition for Chap10 Definition 10 136 1: a ring homomorphism has local complete
intersection fibers if every residue-field fiber is a local complete intersection. -/
def HasLocalCompleteIntersectionFibers (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R, IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S)

/-- Definition for Chap10 Definition 10 136 1: a ring homomorphism is syntomic if it is flat, of
finite presentation, and all of its fibers are local complete intersections. -/
@[stacks 00SL]
def Syntomic (f : R →+* S) : Prop :=
  f.Flat ∧ f.FinitePresentation ∧ f.HasLocalCompleteIntersectionFibers

namespace Syntomic

/-- Definition for Chap10 Definition 10 136 1: a syntomic homomorphism is flat. -/
theorem flat {f : R →+* S} (hf : f.Syntomic) : f.Flat :=
  hf.1

/-- Definition for Chap10 Definition 10 136 1: a syntomic homomorphism is finitely presented. -/
theorem finitePresentation {f : R →+* S} (hf : f.Syntomic) : f.FinitePresentation :=
  hf.2.1

/-- Definition for Chap10 Definition 10 136 1: a syntomic homomorphism has local complete
intersection fibers. -/
theorem hasLocalCompleteIntersectionFibers {f : R →+* S} (hf : f.Syntomic) :
    f.HasLocalCompleteIntersectionFibers :=
  hf.2.2

end Syntomic

end RingHom

end
