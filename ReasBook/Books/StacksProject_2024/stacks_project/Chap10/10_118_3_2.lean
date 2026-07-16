import StacksProject_2024.stacks_project.Chap10.«10_118_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/-- 10.118.3.2: the good locus `U(R → S, M)` is the union of the basic opens `D(f)` for which
`S_f` is finitely presented over `R_f`, `M_f` is finitely presented over `S_f`, and both `S_f`
and `M_f` are free as `R_f`-modules. -/
def goodLocus
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] : Set (PrimeSpectrum R) :=
  ⋃ f : { f : R // LocalizationCondition R S M f },
    (basicOpen f.1 : Set (PrimeSpectrum R))

/-- The good locus is the union of the basic opens corresponding to elements satisfying
`(10.118.3.1)`. -/
theorem goodLocus_eq_iUnion :
    goodLocus R S M =
      ⋃ f : { f : R // LocalizationCondition R S M f },
        (basicOpen f.1 : Set (PrimeSpectrum R)) :=
  rfl

end GenericFlatness

end
