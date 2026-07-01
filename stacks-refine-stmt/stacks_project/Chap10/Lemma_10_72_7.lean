import Mathlib
import stacks_project.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Domain-style sampling:
* primary domain: depth and regular sequences for finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular`,
  `exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes`;
* best owner abstraction: the local depth owner is the chapter bridge `moduleDepth R M`, while
  regular sequences are owned by `RingTheory.Sequence.IsRegular`;
* source/core/bridge triage:
  `source-facing`: the one-step depth drop and the extension of a regular sequence to maximal
  length;
  `core/canonical`: `moduleDepth` and `IsRegular`;
  `bridge/view`: the quotient module `QuotSMulTop x M` and the tail list `rs'`.

Primitive data are only the module, the regular sequence owner predicate, and the quotient owner
`QuotSMulTop x M`. A package bundling the appended regularity proof, maximal-ideal membership, and
length equality is derived theorem-shaped API, so it should not be a public class. -/

namespace IsSMulRegular

-- Proof sketch: apply Lemma `10.72.6` to the short exact sequence
-- `0 → M --(x • ·)→ M → QuotSMulTop x M → 0`. The hypothesis `hreg` gives injectivity on the left,
-- `hx` ensures the quotient is still a module over the local ring with respect to the maximal
-- ideal, and comparing with the regular sequence `x` shows the inequalities from Lemma `10.72.6`
-- force the depth to drop by exactly one. Any nontriviality needed in the proof is recovered
-- internally from `hreg`.
/-- Lemma 10.72.7 (1): if `x ∈ 𝔪` is a nonzerodivisor on a finite module `M` over a Noetherian
local ring `R`, then the depth of `M / xM` is the depth of `M` minus `1`. -/
theorem moduleDepth_quotSMulTop_eq_sub_one {x : R}
    (hreg : IsSMulRegular M x) (hx : x ∈ maximalIdeal R) :
    moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 := sorry

end IsSMulRegular

namespace IsRegular

-- Proof sketch: induct on the difference between the current regular sequence length and the
-- depth. If the lengths already agree, take the empty tail. Otherwise, recover internally that
-- the current regular sequence already lies in `maximalIdeal R` using the auxiliary companion
-- `ofList_le_maximalIdeal`, apply part (1) to the quotient by that regular sequence to obtain
-- another nonzerodivisor in the maximal ideal, adjoin it using
-- `isRegular_append_of_isRegular_of_quotient_isRegular`, and continue until the resulting
-- sequence has length equal to the depth.
/-- Lemma 10.72.7 (2): every `M`-regular sequence over a Noetherian local ring extends to an
`M`-regular sequence whose length is the depth of `M`. The maximal-ideal containment of the
extended sequence is recovered from the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. -/
theorem exists_append_eq_moduleDepth {rs : List R} (hreg : IsRegular M rs) :
    ∃ rs' : List R,
      IsRegular M (rs ++ rs') ∧
        moduleDepth R M = (rs ++ rs').length := sorry

-- Proof sketch: if `x ∈ rs` and `x ∉ maximalIdeal R`, then `x` generates the unit ideal, so
-- `Ideal.ofList rs = ⊤`. This contradicts the `top_ne_smul` field of `hreg`. Applying this to
-- every term of `rs` shows `Ideal.ofList rs ≤ maximalIdeal R`.
/-- Auxiliary companion: every `M`-regular sequence over a local ring is contained in
`maximalIdeal R`. -/
theorem ofList_le_maximalIdeal {rs : List R} (hreg : IsRegular M rs) :
    Ideal.ofList rs ≤ maximalIdeal R := sorry

end IsRegular

end
