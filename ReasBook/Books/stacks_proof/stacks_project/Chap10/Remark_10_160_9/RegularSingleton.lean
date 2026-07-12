import Mathlib

open IsLocalRing
open RingTheory.Sequence

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
variable {x : R}

/-- Helper for Remark 10.160.9: a singleton weakly regular sequence in the maximal ideal is
already a regular sequence. -/
theorem regular_singleton_of_mem_maximalIdeal_of_isSMulRegular
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    IsRegular M [x] := by
  -- Upgrade the weakly regular singleton using maximal-ideal membership term-by-term.
  exact
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
      (by
        intro r hr
        simpa [List.mem_singleton.mp hr] using hx)
      ((isWeaklyRegular_singleton_iff M x).2 hreg)

end
