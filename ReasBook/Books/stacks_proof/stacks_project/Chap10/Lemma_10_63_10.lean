import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

/- Domain triage: this item is a source-facing bridge in the owner API `Module.supportDim`. The
primitive owner data is the module `M` and the canonical quotient object `QuotSMulTop f M`; the
two inequalities are derived from owner theorems rather than new primitive structure. -/

-- Proof sketch: the left inequality comes from the quotient map `M →ₗ[R] QuotSMulTop f M` via
-- `Module.supportDim_le_of_surjective`, reflecting `Supp(M / fM) ⊆ Supp(M)`. The right inequality
-- is exactly the canonical theorem `Module.supportDim_le_supportDim_quotSMulTop_succ`.
/-- Lemma 10.63.10: if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`f ∈ maximalIdeal R`, then the support dimension of `M / fM`, written canonically as
`QuotSMulTop f M`, satisfies
`supportDim R (QuotSMulTop f M) ≤ supportDim R M ∧
  supportDim R M ≤ supportDim R (QuotSMulTop f M) + 1`. -/
@[stacks 0B52]
theorem supportDim_quotSMulTop_bounds_of_mem_maximalIdeal (f : R) (hf : f ∈ maximalIdeal R) :
    supportDim R (QuotSMulTop f M) ≤ supportDim R M ∧
      supportDim R M ≤ supportDim R (QuotSMulTop f M) + 1 := by
  constructor
  · simpa using
      supportDim_le_of_surjective (Submodule.mkQ (f • ⊤))
        (Submodule.mkQ_surjective _)
  · simpa using supportDim_le_supportDim_quotSMulTop_succ hf

/- Companion recall: if `f` avoids every minimal prime of `Module.annihilator R M`, then the right
inequality above is an equality. This is the canonical theorem
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal`. -/
recall supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal

/- Companion recall: if `f` is a nonzerodivisor on `M` and lies in the maximal ideal, then the
right inequality above is an equality. This is the canonical theorem
`Module.supportDim_quotSMulTop_succ_eq_supportDim`. -/
recall supportDim_quotSMulTop_succ_eq_supportDim

end Module

end
