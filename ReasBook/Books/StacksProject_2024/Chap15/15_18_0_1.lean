import StacksProject_2024.Chap10.Theorem_10_129_4

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable (I : Ideal R)

namespace Ideal

/-- The closed subset `V(K)` lies in the flat-over-`R` locus of `M` exactly when every prime of
`S` containing `K` lies in that locus. -/
theorem zeroLocus_subset_flatOverBaseLocus_iff (K : Ideal S) :
    zeroLocus (K : Set S) ⊆ Module.flatOverBaseLocus R S M ↔
      ∀ q : PrimeSpectrum S,
        q ∈ zeroLocus (K : Set S) →
          Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := by
  constructor
  · intro h q hq
    exact (Module.mem_flatOverBaseLocus R S M q).1 (h hq)
  · intro h q hq
    exact (Module.mem_flatOverBaseLocus R S M q).2 (h q hq)

end Ideal

/- 15.18.0.1: for every prime `q` of `S` lying in the closed subset `V(IS)`, the localization
`M_q` is flat over the base ring `R`; equivalently, `V(IS)` is contained in the flat-over-`R`
locus of `M`. -/
#check zeroLocus (I.map (algebraMap R S) : Set S) ⊆ Module.flatOverBaseLocus R S M

end
