import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

/-
Definition 10.60.2 is recalled canonically by `ringKrullDim R`: the Krull dimension of a
commutative ring is the Krull dimension of the topological space `Spec(R)`, equivalently the
supremum of the lengths of strict chains of prime ideals of `R`.
-/
recall ringKrullDim

/- Companion recall: the identification of the Krull dimension of `R` with the topological Krull
dimension of `Spec(R)` is the canonical theorem
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`. -/
recall PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim

end
