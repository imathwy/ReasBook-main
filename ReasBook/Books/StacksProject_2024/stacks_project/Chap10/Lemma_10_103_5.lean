import Mathlib
import StacksProject_2024.Chap10.Lemma_10_103_3
import StacksProject_2024.Chap10.Lemma_10_72_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing RingTheory Sequence
open scoped ENat

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

/- Domain-style sampling:
* primary domain: Cohen-Macaulay finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.supportDim_quotSMulTop_succ_eq_supportDim`,
  `IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one`,
  `Module.cohenMacaulay_quotSMulTop_and_depth_eq_sub_one_of_supportDim_quotSMulTop_add_one_eq`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* source/core/bridge triage:
  `source-facing`: the iff statement for passing the Cohen-Macaulay condition across quotient by a
  regular element in the maximal ideal;
  `core/canonical`: `Module.CohenMacaulay`, together with the canonical support-dimension and
  depth-drop theorems for `QuotSMulTop`;
  `bridge/view`: the quotient module `QuotSMulTop x M`.

Primitive data are only `x ∈ maximalIdeal R` and the owner-level regularity hypothesis
`IsSMulRegular M x`. The quotient Cohen-Macaulayness and the reconstruction of
`CohenMacaulay R M` from the quotient are derived API over the existing owner theorems, so this
file should reuse those declarations directly instead of introducing a parallel local bridge API.
-/

-- Proof sketch: the forward implication is exactly Lemma `10.103.3 (2)` after rewriting the
-- support-dimension hypothesis with
-- `Module.supportDim_quotSMulTop_succ_eq_supportDim`. For the reverse implication, the quotient
-- Cohen-Macaulay hypothesis identifies `supportDim R (QuotSMulTop x M)` with the depth of the
-- quotient. The regular element `x` gives a length-one regular sequence in `maximalIdeal R`, so
-- `moduleDepth R M ≥ 1`; together with
-- `IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one`, this rewrites the support-dimension
-- equality back to the defining field of `CohenMacaulay R M`.
/-- Lemma 10.103.5: if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`x ∈ maximalIdeal R` is a nonzerodivisor on `M`, then `M` is Cohen-Macaulay if and only if the
quotient `M / xM`, written canonically as `QuotSMulTop x M`, is Cohen-Macaulay. -/
theorem cohenMacaulay_iff_quotSMulTop_of_mem_maximalIdeal {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    CohenMacaulay R M ↔ CohenMacaulay R (QuotSMulTop x M) := by
  constructor
  · intro hM
    let _ : CohenMacaulay R M := hM
    exact
      (cohenMacaulay_quotSMulTop_and_depth_eq_sub_one_of_supportDim_quotSMulTop_add_one_eq
        (supportDim_quotSMulTop_succ_eq_supportDim hreg hx)).1
  · intro hquot
    have hdepth_pos : (1 : ℕ∞) ≤ moduleDepth R M := by
      by_cases htop : maximalIdeal R • (⊤ : Submodule R M) = ⊤
      · rw [show moduleDepth R M = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M htop]
        simp
      · have hM : Nontrivial M := by
          by_contra hM
          letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
          apply htop
          ext m
          simp [Subsingleton.elim m 0]
        rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M htop]
        refine le_sSup ?_
        refine ⟨[x], ?_, ?_, by simp⟩
        · exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
            (by intro r hr; simpa [List.mem_singleton.mp hr] using hx)
            ((isWeaklyRegular_singleton_iff M x).2 hreg)
        · simpa using hx
    exact ⟨by
      rw [← supportDim_quotSMulTop_succ_eq_supportDim hreg hx,
        hquot.supportDim_eq_moduleDepth,
        IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hreg hx]
      simpa using
        congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) (tsub_add_cancel_of_le hdepth_pos)⟩

end Module

end
