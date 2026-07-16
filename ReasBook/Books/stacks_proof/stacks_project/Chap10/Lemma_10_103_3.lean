import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_103_1
import stacks_proof.stacks_project.Chap10.Lemma_10_63_2
import stacks_proof.stacks_project.Chap10.Lemma_10_72_7
import stacks_proof.stacks_project.Chap10.Lemma_10_72_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped ENat Pointwise

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/- 
Source/core/bridge triage:
* source-facing: Lemma `10.103.3` extracts the regularity and quotient consequences of the support
  dimension equality for `QuotSMulTop g M`;
* core/canonical: `CohenMacaulay R M`, `IsSMulRegular M g`, and the local-depth bridge
  `moduleDepth R M`;
* bridge/view: the quotient module `QuotSMulTop g M` together with the hypothesis
  `supportDim R (QuotSMulTop g M) + 1 = supportDim R M`.

Primitive data are only the owner assumption `[CohenMacaulay R M]` and the support-dimension
equality. In a local ring, `g ∈ maximalIdeal R` is recovered internally from that equality, since
the Cohen-Macaulay hypothesis gives `supportDim R M ≠ ⊥` while a unit `g` would force
`QuotSMulTop g M = 0` and hence `supportDim R (QuotSMulTop g M) = ⊥`. The quotient
Cohen-Macaulayness and depth drop are derived consequences and should be stated through the owner
APIs rather than by repeating a longer `Ideal.depth (maximalIdeal R)` surface.
-/

/-- Helper for Lemma 10.103.3: the support-dimension drop forces the element to lie in the maximal
ideal of the local ring. -/
private theorem mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    g ∈ maximalIdeal R := by
  -- If `g` were a unit, then `gM = M`, so the quotient would be zero and have support dimension
  -- `⊥`, contradicting the Cohen-Macaulay support-dimension identity for `M`.
  by_contra hg
  have hg_unit : IsUnit g := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hg
    exact not_not.mp hg
  have hsmul_top : g • (⊤ : Submodule R M) = ⊤ := by
    refine top_unique ?_
    intro m hm
    rcases hg_unit with ⟨u, rfl⟩
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨(↑u⁻¹ : R) • m, by simp, ?_⟩
    simp [smul_smul]
  have hquot_subsingleton : Subsingleton (QuotSMulTop g M) := by
    rw [Submodule.Quotient.subsingleton_iff]
    simpa using hsmul_top
  letI : Subsingleton (QuotSMulTop g M) := hquot_subsingleton
  have hquot_bot : supportDim R (QuotSMulTop g M) = ⊥ := by
    simpa using Module.supportDim_eq_bot_of_subsingleton (R := R) (M := QuotSMulTop g M)
  have hM_bot : supportDim R M = ⊥ := by
    simpa [hquot_bot] using hdim.symm
  simpa [hM_bot] using
    (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))

/-- Helper for Lemma 10.103.3: every associated prime of a Cohen-Macaulay module has quotient ring
dimension equal to the support dimension of the module. -/
private theorem ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
    [CohenMacaulay R M] (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ p) = supportDim R M := by
  -- The depth lower bound from the associated-prime theorem matches the ambient support
  -- dimension because `M` is Cohen-Macaulay.
  have hlower :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := M) p hp
  have hlower' : supportDim R M ≤ ringKrullDim (R ⧸ p) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hlower
  have hp_support :
      (⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M :=
    Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using hp)
  have hann_le : Module.annihilator R M ≤ p :=
    Module.annihilator_le_of_mem_support hp_support
  have hup : ringKrullDim (R ⧸ p) ≤ supportDim R M := by
    -- The quotient by `p` is a further quotient of `R / Ann(M)`, so its dimension is no larger.
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := M)]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
      (Ideal.Quotient.factor_surjective hann_le)
  exact le_antisymm hup hlower'

-- Proof sketch: the Cohen-Macaulay hypothesis gives `supportDim R M = .some (moduleDepth R M)`,
-- so `supportDim R M ≠ ⊥`. If `g` were a unit, then `QuotSMulTop g M = 0`, forcing
-- `supportDim R (QuotSMulTop g M) = ⊥`, contradicting `hdim`; hence `g ∈ maximalIdeal R`
-- internally. Choose a maximal `M`-regular sequence in the maximal ideal from the Cohen-Macaulay
-- hypothesis. The support-dimension equality for `QuotSMulTop g M` shows that `g` is good with
-- respect to that sequence, so Lemma `10.103.2 (1)` yields injectivity of multiplication by `g`.
/-- Lemma 10.103.3 (1): if `R` is a Noetherian local ring, `M` is a Cohen-Macaulay `R`-module,
and `g` cuts the support dimension down by one, written as
`supportDim R (QuotSMulTop g M) + 1 = supportDim R M`, then `g` is a nonzerodivisor on `M`. -/
@[stacks 00N5]
theorem isSMulRegular_of_cohenMacaulay_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    IsSMulRegular M g := by
  have hg_mem : g ∈ maximalIdeal R :=
    mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq (R := R) (M := M) hdim
  -- Route correction: rather than rebuilding the source induction locally, exclude `g` from every
  -- associated prime using the dimension contradiction forced by the assumed one-step drop.
  have hg_not_mem_union : g ∉ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    intro hg_union
    rcases Set.mem_iUnion.1 hg_union with ⟨p, hp⟩
    rcases Set.mem_iUnion.1 hp with ⟨hp_assoc, hg_mem_p⟩
    let p' : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime⟩
    have hp_supportM : p' ∈ Module.support R M :=
      Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using hp_assoc)
    have hp_zeroLocus : p' ∈ PrimeSpectrum.zeroLocus ({g} : Set R) := by
      exact (PrimeSpectrum.mem_zeroLocus p' ({g} : Set R)).2
        (Set.singleton_subset_iff.mpr hg_mem_p)
    have hp_supportQuot : p' ∈ Module.support R (QuotSMulTop g M) := by
      simpa [Module.support_quotSMulTop] using And.intro hp_supportM hp_zeroLocus
    have hquot_le : ringKrullDim (R ⧸ p) ≤ supportDim R (QuotSMulTop g M) := by
      -- Membership in the quotient support bounds the dimension of `R / p` by the quotient
      -- support dimension.
      have hann_le : Module.annihilator R (QuotSMulTop g M) ≤ p :=
        Module.annihilator_le_of_mem_support hp_supportQuot
      rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R)
        (M := QuotSMulTop g M)]
      exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
        (Ideal.Quotient.factor_surjective hann_le)
    have hp_dim : ringKrullDim (R ⧸ p) = supportDim R M :=
      ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
        (R := R) (M := M) p hp_assoc
    have hle : supportDim R M ≤ supportDim R (QuotSMulTop g M) := by
      calc
        supportDim R M = ringKrullDim (R ⧸ p) := hp_dim.symm
        _ ≤ supportDim R (QuotSMulTop g M) := hquot_le
    have hnot :
        ¬ supportDim R M ≤ supportDim R (QuotSMulTop g M) := by
      cases hq : supportDim R (QuotSMulTop g M) with
      | bot =>
          have hM_bot : supportDim R M = ⊥ := by
            simpa [hq] using hdim.symm
          have : False := by
            simpa [hM_bot] using
              (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))
          exact False.elim this
      | coe n =>
          letI : Nontrivial (R ⧸ p) :=
            Ideal.Quotient.nontrivial_iff.mpr (AssociatedPrimes.mem_iff.mp hp_assoc).isPrime.ne_top
          have hM_ne_top : supportDim R M ≠ ⊤ := by
            letI : IsLocalRing (R ⧸ p) :=
              IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
            intro htop
            have : ringKrullDim (R ⧸ p) = ⊤ := by
              simpa [hp_dim] using htop
            exact ringKrullDim_ne_top this
          have hn_ne_top : (n : ℕ∞) ≠ ⊤ := by
            intro hn_top
            have hM_top : supportDim R M = ⊤ := by
              calc
                supportDim R M = supportDim R (QuotSMulTop g M) + 1 := hdim.symm
                _ = (((⊤ : ℕ∞) : WithBot ℕ∞) + 1) := by rw [hq, hn_top]
                _ = ⊤ := by rfl
            exact hM_ne_top hM_top
          exact fun hle' ↦
            (lt_irrefl (n : ℕ∞)) <|
              (ENat.add_one_le_iff hn_ne_top).1 <| by
                have hle'' :
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                  calc
                    (((n : ℕ∞) : WithBot ℕ∞) + 1) = supportDim R M := by
                      simpa [hq] using hdim
                    _ ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
                      simpa [hq] using hle'
                exact_mod_cast hle''
    exact hnot hle
  -- Avoiding the union of associated primes is exactly the nonzerodivisor criterion.
  simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hg_not_mem_union

-- Proof sketch: first recover `g ∈ maximalIdeal R` internally from `hdim` as in part (1), and
-- then apply part (1) to obtain that `g` is a nonzerodivisor on `M`. Use the quotient criterion
-- for Cohen-Macaulay modules together with the support-dimension equality to identify the depth of
-- `QuotSMulTop g M` as one less than the depth of `M`.
/-- Lemma 10.103.3 (2): under the same hypotheses, the quotient `M / gM`, written canonically as
`QuotSMulTop g M`, is Cohen-Macaulay, and its depth is one less than the depth of `M`. -/
@[stacks 00N5]
theorem cohenMacaulay_quotSMulTop_and_depth_eq_sub_one_of_supportDim_quotSMulTop_add_one_eq
    [CohenMacaulay R M] {g : R}
    (hdim : supportDim R (QuotSMulTop g M) + 1 = supportDim R M) :
    CohenMacaulay R (QuotSMulTop g M) ∧
      moduleDepth R (QuotSMulTop g M) = moduleDepth R M - 1 := by
  have hg_mem : g ∈ maximalIdeal R :=
    mem_maximalIdeal_of_supportDim_quotSMulTop_add_one_eq (R := R) (M := M) hdim
  have hreg : IsSMulRegular M g :=
    isSMulRegular_of_cohenMacaulay_of_supportDim_quotSMulTop_add_one_eq
      (R := R) (M := M) hdim
  have hdepth :
      moduleDepth R (QuotSMulTop g M) = moduleDepth R M - 1 :=
    IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one hreg hg_mem
  refine ⟨?_, hdepth⟩
  refine Module.CohenMacaulay.mk ?_
  -- The assumed support-dimension drop and the one-step depth drop identify the quotient as
  -- Cohen-Macaulay.
  cases hq : supportDim R (QuotSMulTop g M) with
  | bot =>
      have hM_bot : supportDim R M = ⊥ := by
        simpa [hq] using hdim.symm
      have : False := by
        simpa [hM_bot] using
          (Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M))
      exact False.elim this
  | coe n =>
      rw [hdepth]
      have hn_cast :
          (((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) := by
        simpa [hq, Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hdim
      have hn : (n : ℕ∞) + 1 = moduleDepth R M :=
        WithBot.coe_inj.mp hn_cast
      have hn_tsub : (n : ℕ∞) = moduleDepth R M - 1 := by
        rw [← hn]
        simpa using
          (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp)).symm
      simpa using congrArg (fun d : ℕ∞ ↦ (d : WithBot ℕ∞)) hn_tsub

end Module

end
