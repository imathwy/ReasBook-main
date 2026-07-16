import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_103_1
import stacks_proof.stacks_project.Chap10.Lemma_10_63_10
import stacks_proof.stacks_project.Chap10.Lemma_10_72_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing RingTheory Sequence
open scoped ENat

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

/- Domain-style sampling:
* primary domain: Cohen-Macaulay finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.supportDim_quotSMulTop_succ_eq_supportDim`,
  `IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* source/core/bridge triage:
  `source-facing`: the iff statement for passing the Cohen-Macaulay condition across quotient by a
  regular element in the maximal ideal;
  `core/canonical`: `Module.CohenMacaulay`, together with the canonical support-dimension and
  depth-drop theorems for `QuotSMulTop`;
  `bridge/view`: the quotient module `QuotSMulTop x M`.

Primitive data are only `x ∈ maximalIdeal R` and the owner-level regularity hypothesis
`IsSMulRegular M x`. The quotient Cohen-Macaulayness and the reconstruction of
`CohenMacaulay R M` from the quotient are derived API over the existing support-dimension and
depth-drop theorems, so this file should reuse those owner-level equalities directly instead of
introducing a parallel local bridge API.
-/

-- Proof sketch: in both directions, the source proof is that quotienting by a regular element in
-- the maximal ideal lowers both support dimension and module depth by exactly one. For the
-- forward implication, combine the two drop formulas with the Cohen-Macaulay equality for `M` and
-- cancel the common `+ 1` after a case split on `supportDim R (QuotSMulTop x M)`. For the
-- reverse implication, the quotient Cohen-Macaulay hypothesis supplies the quotient equality, and
-- the regular element itself provides the positivity needed to cancel the `- 1` terms.
/-- Helper for Lemma 10.103.5: a nonzerodivisor in the maximal ideal gives positive module
depth. -/
lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    (1 : ℕ∞) ≤ moduleDepth R M := by
  by_cases hsmul : maximalIdeal R • (⊤ : Submodule R M) = ⊤
  · -- If `𝔪 M = M`, the local depth is infinite, so positivity is immediate.
    have hdepth_top : moduleDepth R M = ⊤ :=
      Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul
    rw [hdepth_top]
    simp
  · -- Otherwise depth is computed by regular-sequence lengths, and `[x]` is one such sequence.
    have hnontrivial : Nontrivial M := by
      by_contra hsub
      letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hsub
      apply hsmul
      ext m
      simp [Subsingleton.elim m 0]
    letI : Nontrivial M := hnontrivial
    have hsingleton_reg : IsRegular M [x] :=
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
        (by
          intro r hr
          simpa [List.mem_singleton.mp hr] using hx)
        ((isWeaklyRegular_singleton_iff M x).2 hreg)
    have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal R := by
      simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx
    have hdepth_eq :
        moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) :=
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul
    rw [hdepth_eq]
    refine le_sSup ?_
    exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/-- Lemma 10.103.5: if `R` is a Noetherian local ring, `M` is a finite `R`-module, and
`x ∈ maximalIdeal R` is a nonzerodivisor on `M`, then `M` is Cohen-Macaulay if and only if the
quotient `M / xM`, written canonically as `QuotSMulTop x M`, is Cohen-Macaulay. -/
@[stacks 0C6G]
theorem cohenMacaulay_iff_quotSMulTop_of_mem_maximalIdeal {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    CohenMacaulay R M ↔ CohenMacaulay R (QuotSMulTop x M) := by
  constructor
  · intro hM
    have hsupport :
        supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
      supportDim_quotSMulTop_succ_eq_supportDim hreg hx
    have hdepth_quot :
        moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 :=
      IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hreg hx
    refine Module.CohenMacaulay.mk ?_
    -- Rewrite the Cohen-Macaulay equality for `M` through the one-step quotient formulas.
    cases hq : supportDim R (QuotSMulTop x M) with
    | bot =>
        have hM_bot : supportDim R M = ⊥ := by
          simpa [hq] using hsupport.symm
        have : False := by
          simpa [hM_bot] using hM.supportDim_eq_moduleDepth
        exact False.elim this
    | coe n =>
        rw [hdepth_quot]
        have hn_cast :
            (((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = (moduleDepth R M : WithBot ℕ∞) := by
          simpa [hq, hM.supportDim_eq_moduleDepth] using hsupport
        have hn : (n : ℕ∞) + 1 = moduleDepth R M :=
          WithBot.coe_inj.mp hn_cast
        have hn_tsub : (n : ℕ∞) = moduleDepth R M - 1 := by
          rw [← hn]
          simpa using
            (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp)).symm
        simpa [hq] using congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) hn_tsub
  · intro hquot
    -- The regular element in `𝔪` gives the positivity needed to cancel the `- 1` identities.
    have hdepth_pos : (1 : ℕ∞) ≤ moduleDepth R M :=
      one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular (R := R) (M := M) hx hreg
    have hsupport :
        supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
      supportDim_quotSMulTop_succ_eq_supportDim hreg hx
    have hdepth_quot :
        moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 :=
      IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hreg hx
    have hdepth_cancel : moduleDepth R M - 1 + 1 = moduleDepth R M :=
      tsub_add_cancel_of_le hdepth_pos
    have hdepth_cancel_cast :
        ((moduleDepth R M - 1 + 1 : ℕ∞) : WithBot ℕ∞) =
          (moduleDepth R M : WithBot ℕ∞) :=
      congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) hdepth_cancel
    refine Module.CohenMacaulay.mk ?_
    -- Rewriting support dimension and depth through the quotient recovers the defining equality.
    rw [← hsupport, hquot.supportDim_eq_moduleDepth, hdepth_quot]
    simpa using hdepth_cancel_cast

end Module

end
